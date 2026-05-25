import EvmCompiler.Functions.SourceDirect
import EvmCompiler.Functions.Semantics
import EvmCompiler.Locals.Preservation

namespace EvmCompiler

namespace Locals
namespace Direct

set_option maxHeartbeats 800000 in
mutual
  theorem Block.runOpen_mono (program : Program) :
      ∀ {fuel fuel' : Nat} {ctx : Ctx} {block : Block}
        {state : RunState} {outcome : Outcome} {runCtx : Ctx},
        fuel ≤ fuel' →
        Block.runOpen program ctx fuel block state = .ok (outcome, runCtx) →
        Block.runOpen program ctx fuel' block state = .ok (outcome, runCtx) := by
    intro fuel fuel' ctx block state outcome runCtx hLe hRun
    cases fuel with
    | zero =>
        cases block
        simp [Block.runOpen, invalid, Structured.invalid] at hRun
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
                    simpa [Block.runOpen] using hRun
                | cons stmt rest =>
                    cases hStmt : Stmt.run program ctx fuel stmt state with
                    | error err =>
                        simp [Block.runOpen, hStmt] at hRun
                    | ok stmtResult =>
                        rcases stmtResult with ⟨stmtOutcome, stmtCtx⟩
                        have hStmt' :
                            Stmt.run program ctx fuel' stmt state =
                              .ok (stmtOutcome, stmtCtx) :=
                          Stmt.run_mono program hFuelLe hStmt
                        cases hMode : stmtOutcome.mode with
                        | regular =>
                            simp [Block.runOpen, hStmt, hStmt', hMode] at hRun ⊢
                            exact
                              Block.runOpen_mono program hFuelLe hRun
                        | brk =>
                            simp [Block.runOpen, hStmt, hStmt', hMode] at hRun ⊢
                            exact hRun
                        | cont =>
                            simp [Block.runOpen, hStmt, hStmt', hMode] at hRun ⊢
                            exact hRun
                        | leave =>
                            simp [Block.runOpen, hStmt, hStmt', hMode] at hRun ⊢
                            exact hRun
                        | halt kind =>
                            simp [Block.runOpen, hStmt, hStmt', hMode] at hRun ⊢
                            exact hRun

  theorem Block.runScoped_mono (program : Program) :
      ∀ {fuel fuel' : Nat} {ctx : Ctx} {block : Block}
        {state : RunState} {outcome : Outcome},
        fuel ≤ fuel' →
        Block.runScoped program ctx block fuel state = .ok outcome →
        Block.runScoped program ctx block fuel' state = .ok outcome := by
    intro fuel fuel' ctx block state outcome hLe hRun
    unfold Block.runScoped at hRun ⊢
    cases hOpen : Block.runOpen program ctx fuel block state with
    | error err =>
        simp [hOpen] at hRun
    | ok openResult =>
        rcases openResult with ⟨openOutcome, finalCtx⟩
        have hOpen' :
            Block.runOpen program ctx fuel' block state =
              .ok (openOutcome, finalCtx) :=
          Block.runOpen_mono program hLe hOpen
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

  theorem Stmt.runForLoop_mono (program : Program) :
      ∀ {fuel fuel' : Nat} {loopCtx : Ctx} {cond : Expr 1}
        {postBase : Ctx} {post : Block} {bodyBase : Ctx} {body : Block}
        {state : RunState} {outcome : Outcome},
        fuel ≤ fuel' →
        Stmt.runForLoop program loopCtx cond postBase post bodyBase body fuel
          state = .ok outcome →
        Stmt.runForLoop program loopCtx cond postBase post bodyBase body fuel'
          state = .ok outcome := by
    intro fuel fuel' loopCtx cond postBase post bodyBase body state outcome
      hLe hRun
    cases fuel with
    | zero =>
        simp [Stmt.runForLoop, invalid, Structured.invalid] at hRun
    | succ fuel =>
        cases fuel' with
        | zero =>
            omega
        | succ fuel' =>
            have hFuelLe : fuel ≤ fuel' := Nat.succ_le_succ_iff.mp hLe
            unfold Stmt.runForLoop at hRun ⊢
            cases hCond : Expr.runCondition loopCtx cond state with
            | error err =>
                simp [hCond] at hRun ⊢
            | ok condResult =>
                rcases condResult with ⟨stateAfterCond, condTrue⟩
                cases condTrue with
                | false =>
                    simp [hCond] at hRun ⊢
                    exact hRun
                | true =>
                    simp [hCond] at hRun ⊢
                    cases hBody :
                        Block.runScoped program bodyBase body fuel
                          stateAfterCond with
                    | error err =>
                        simp [hBody] at hRun
                    | ok bodyOutcome =>
                        have hBody' :
                            Block.runScoped program bodyBase body fuel'
                              stateAfterCond = .ok bodyOutcome :=
                          Block.runScoped_mono program hFuelLe hBody
                        cases hBodyMode : bodyOutcome.mode with
                        | brk =>
                            simp [hBody, hBody', hBodyMode] at hRun ⊢
                            exact hRun
                        | regular =>
                            simp [hBody, hBody', hBodyMode] at hRun ⊢
                            cases hPost :
                                Block.runScoped program postBase post fuel
                                  bodyOutcome.state with
                            | error err =>
                                simp [hPost] at hRun
                            | ok postOutcome =>
                                have hPost' :
                                    Block.runScoped program postBase post fuel'
                                      bodyOutcome.state = .ok postOutcome :=
                                  Block.runScoped_mono program hFuelLe hPost
                                cases hPostMode : postOutcome.mode with
                                | regular =>
                                    simp [hPost, hPost', hPostMode] at hRun ⊢
                                    exact
                                      Stmt.runForLoop_mono program hFuelLe hRun
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
                                Block.runScoped program postBase post fuel
                                  bodyOutcome.state with
                            | error err =>
                                simp [hPost] at hRun
                            | ok postOutcome =>
                                have hPost' :
                                    Block.runScoped program postBase post fuel'
                                      bodyOutcome.state = .ok postOutcome :=
                                  Block.runScoped_mono program hFuelLe hPost
                                cases hPostMode : postOutcome.mode with
                                | regular =>
                                    simp [hPost, hPost', hPostMode] at hRun ⊢
                                    exact
                                      Stmt.runForLoop_mono program hFuelLe hRun
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

  theorem Stmt.run_mono (program : Program) :
      ∀ {fuel fuel' : Nat} {ctx : Ctx} {stmt : Stmt}
        {state : RunState} {outcome : Outcome} {runCtx : Ctx},
        fuel ≤ fuel' →
        Stmt.run program ctx fuel stmt state = .ok (outcome, runCtx) →
        Stmt.run program ctx fuel' stmt state = .ok (outcome, runCtx) := by
    intro fuel fuel' ctx stmt state outcome runCtx hLe hRun
    cases stmt with
    | expr expr =>
        simpa [Stmt.run] using hRun
    | exprs exprs =>
        simpa [Stmt.run] using hRun
    | let_ name value =>
        simpa [Stmt.run] using hRun
    | assign name value =>
        simpa [Stmt.run] using hRun
    | assignTop name =>
        simpa [Stmt.run] using hRun
    | assignTopWithOffset offset name =>
        simpa [Stmt.run] using hRun
    | block body =>
        unfold Stmt.run at hRun ⊢
        cases hBody : Block.runScoped program ctx body fuel state with
        | error err =>
            simp [hBody] at hRun
        | ok bodyOutcome =>
            have hBody' :
                Block.runScoped program ctx body fuel' state =
                  .ok bodyOutcome :=
              Block.runScoped_mono program hLe hBody
            simp [hBody, hBody'] at hRun ⊢
            exact hRun
    | if_ cond body =>
        cases fuel with
        | zero =>
            simp [Stmt.run, invalid, Structured.invalid] at hRun
        | succ fuel =>
            cases fuel' with
            | zero =>
                omega
            | succ fuel' =>
                have hFuelLe : fuel ≤ fuel' := Nat.succ_le_succ_iff.mp hLe
                unfold Stmt.run at hRun ⊢
                cases hCond : Expr.runCondition ctx cond state with
                | error err =>
                    simp [hCond] at hRun ⊢
                | ok condResult =>
                    rcases condResult with ⟨stateAfterCond, condTrue⟩
                    cases condTrue with
                    | false =>
                        simp [hCond] at hRun ⊢
                        exact hRun
                    | true =>
                        simp [hCond] at hRun ⊢
                        cases hBody :
                            Block.runScoped program ctx body fuel
                              stateAfterCond with
                        | error err =>
                            simp [hBody] at hRun
                        | ok bodyOutcome =>
                            have hBody' :
                                Block.runScoped program ctx body fuel'
                                  stateAfterCond = .ok bodyOutcome :=
                              Block.runScoped_mono program hFuelLe hBody
                            simp [hBody, hBody'] at hRun ⊢
                            exact hRun
    | switch scrutinee cases defaultBody =>
        cases fuel with
        | zero =>
            simp [Stmt.run, invalid, Structured.invalid] at hRun
        | succ fuel =>
            cases fuel' with
            | zero =>
                omega
            | succ fuel' =>
                have hFuelLe : fuel ≤ fuel' := Nat.succ_le_succ_iff.mp hLe
                unfold Stmt.run at hRun ⊢
                cases hScrutinee : Expr.runState ctx scrutinee state with
                | error err =>
                    simp [hScrutinee] at hRun ⊢
                | ok stateAfterScrutinee =>
                    cases hPop : stateAfterScrutinee.evm.stack.pop with
                    | none =>
                        simp [hScrutinee, hPop, invalid, Structured.invalid] at hRun ⊢
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
                                Block.runScoped program ctx selected fuel
                                  (stateAfterScrutinee.withEVM
                                    { stateAfterScrutinee.evm with stack := stack }) with
                            | error err =>
                                simp [hBody] at hRun
                            | ok bodyOutcome =>
                                have hBody' :
                                    Block.runScoped program ctx selected fuel'
                                      (stateAfterScrutinee.withEVM
                                        { stateAfterScrutinee.evm with stack := stack }) =
                                      .ok bodyOutcome :=
                                  Block.runScoped_mono program hFuelLe hBody
                                simp [hBody, hBody'] at hRun ⊢
                                exact hRun
    | for_ init cond post body =>
        cases fuel with
        | zero =>
            simp [Stmt.run, invalid, Structured.invalid] at hRun
        | succ fuel =>
            cases fuel' with
            | zero =>
                omega
            | succ fuel' =>
                have hFuelLe : fuel ≤ fuel' := Nat.succ_le_succ_iff.mp hLe
                unfold Stmt.run at hRun ⊢
                let initBase := ctx.withoutLoopControl
                cases hInit :
                    Block.runOpen program initBase fuel init state with
                | error err =>
                    simp [initBase, hInit] at hRun
                | ok initResult =>
                    rcases initResult with ⟨initOutcome, initCtx⟩
                    have hInit' :
                        Block.runOpen program initBase fuel' init state =
                          .ok (initOutcome, initCtx) :=
                      Block.runOpen_mono program hFuelLe hInit
                    cases hInitMode : initOutcome.mode with
                    | regular =>
                        simp [initBase, hInit, hInit', hInitMode] at hRun ⊢
                        let postBase := initCtx.withoutLoopControl
                        let bodyBase := initCtx.withLoopControl initCtx.layout.length
                        cases hLoop :
                            Stmt.runForLoop program initCtx cond postBase post
                              bodyBase body fuel initOutcome.state with
                        | error err =>
                            simp [postBase, bodyBase, hLoop] at hRun
                        | ok loopOutcome =>
                            have hLoop' :
                                Stmt.runForLoop program initCtx cond postBase post
                                  bodyBase body fuel' initOutcome.state =
                                  .ok loopOutcome :=
                              Stmt.runForLoop_mono program hFuelLe hLoop
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
        simpa [Stmt.run] using hRun
    | cont =>
        simpa [Stmt.run] using hRun
    | leave =>
        simpa [Stmt.run] using hRun
    | call name =>
        cases fuel with
        | zero =>
            simp [Stmt.run, invalid, Structured.invalid] at hRun
        | succ fuel =>
            cases fuel' with
            | zero =>
                omega
            | succ fuel' =>
                have hFuelLe : fuel ≤ fuel' := Nat.succ_le_succ_iff.mp hLe
                unfold Stmt.run at hRun ⊢
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
                          (state.withEVM { state.evm with stack := args }).pushReturn
                            callerStack proc.retc
                        cases hBody :
                            Block.runOpen program
                              (Ctx.procEntryWithLayoutAndRetc
                                proc.entryLayout proc.retc)
                              fuel proc.body callState with
                        | error err =>
                            simp [hLookup, hSplit, callState, hBody] at hRun
                        | ok bodyResult =>
                            rcases bodyResult with ⟨bodyOutcome, bodyCtx⟩
                            have hBody' :
                                Block.runOpen program
                                  (Ctx.procEntryWithLayoutAndRetc
                                    proc.entryLayout proc.retc)
                                  fuel' proc.body callState =
                                    .ok (bodyOutcome, bodyCtx) :=
                              Block.runOpen_mono program hFuelLe hBody
                            cases hBodyMode : bodyOutcome.mode <;>
                              simp [hLookup, hSplit, callState, hBody,
                                hBody', hBodyMode] at hRun ⊢ <;>
                              exact hRun
    | terminal kind =>
        simpa [Stmt.run] using hRun
    | terminalArgs kind args =>
        simpa [Stmt.run] using hRun
end

namespace Block

theorem runOpen_nil_ok {program : Program} {ctx : Ctx} {fuel : Nat}
    {state : RunState} {outcome : Outcome} {runCtx : Ctx}
    (hRun : Block.runOpen program ctx fuel { stmts := [] } state =
      .ok (outcome, runCtx)) :
    outcome = Structured.Outcome.regular state ∧ runCtx = ctx := by
  cases fuel with
  | zero =>
      simp [Block.runOpen, invalid, Structured.invalid] at hRun
  | succ fuel =>
      have hPair :
          (Structured.Outcome.regular state, ctx) = (outcome, runCtx) := by
        simpa [Block.runOpen] using hRun
      injection hPair with hOutcome hCtx
      exact ⟨hOutcome.symm, hCtx.symm⟩

theorem runOpen_append_regular_exists (program : Program) :
    ∀ (left right : List Stmt) (ctx midCtx : Ctx)
      (state mid : RunState) (outcome : Outcome) (runCtx : Ctx),
      (∃ fuel, Block.runOpen program ctx fuel { stmts := left } state =
        .ok (Structured.Outcome.regular mid, midCtx)) →
      (∃ fuel, Block.runOpen program midCtx fuel { stmts := right } mid =
        .ok (outcome, runCtx)) →
      ∃ fuel, Block.runOpen program ctx fuel { stmts := left ++ right } state =
        .ok (outcome, runCtx) := by
  intro left
  induction left with
  | nil =>
      intro right ctx midCtx state mid outcome runCtx hLeft hRight
      rcases hLeft with ⟨fuelLeft, hLeft⟩
      rcases runOpen_nil_ok hLeft with ⟨hOutcome, hCtx⟩
      cases hOutcome
      cases hCtx
      simpa using hRight
  | cons stmt rest ih =>
      intro right ctx midCtx state mid outcome runCtx hLeft hRight
      rcases hLeft with ⟨fuelLeft, hLeft⟩
      cases fuelLeft with
      | zero =>
          simp [Block.runOpen, invalid, Structured.invalid] at hLeft
      | succ fuelLeft =>
          cases hStmt : Stmt.run program ctx fuelLeft stmt state with
          | error err =>
              simp [Block.runOpen, hStmt] at hLeft
          | ok stmtResult =>
              rcases stmtResult with ⟨stmtOutcome, stmtCtx⟩
              cases hMode : stmtOutcome.mode with
              | regular =>
                  simp [Block.runOpen, hStmt, hMode] at hLeft
                  have hRest :
                      ∃ fuel,
                        Block.runOpen program stmtCtx fuel { stmts := rest }
                          stmtOutcome.state =
                          .ok (Structured.Outcome.regular mid, midCtx) :=
                    ⟨fuelLeft, hLeft⟩
                  rcases ih right stmtCtx midCtx stmtOutcome.state mid outcome
                      runCtx hRest hRight with
                    ⟨fuelRest, hRestAppend⟩
                  let fuel := Nat.max fuelLeft fuelRest + 1
                  refine ⟨fuel, ?_⟩
                  have hStmt' :
                      Stmt.run program ctx (Nat.max fuelLeft fuelRest) stmt state =
                        .ok (stmtOutcome, stmtCtx) :=
                    Stmt.run_mono program (Nat.le_max_left _ _) hStmt
                  have hRestAppend' :
                      Block.runOpen program stmtCtx (Nat.max fuelLeft fuelRest)
                          { stmts := rest ++ right } stmtOutcome.state =
                        .ok (outcome, runCtx) :=
                    Block.runOpen_mono program (Nat.le_max_right _ _)
                      hRestAppend
                  simp [fuel, Block.runOpen, hStmt', hMode, hRestAppend']
              | brk =>
                  have hPair :
                      (stmtOutcome, ctx) =
                        (Structured.Outcome.regular mid, midCtx) := by
                    simpa [Block.runOpen, hStmt, hMode] using hLeft
                  injection hPair with hOutcome _hCtx
                  rw [hOutcome] at hMode
                  simp [Structured.Outcome.regular] at hMode
              | cont =>
                  have hPair :
                      (stmtOutcome, ctx) =
                        (Structured.Outcome.regular mid, midCtx) := by
                    simpa [Block.runOpen, hStmt, hMode] using hLeft
                  injection hPair with hOutcome _hCtx
                  rw [hOutcome] at hMode
                  simp [Structured.Outcome.regular] at hMode
              | leave =>
                  have hPair :
                      (stmtOutcome, ctx) =
                        (Structured.Outcome.regular mid, midCtx) := by
                    simpa [Block.runOpen, hStmt, hMode] using hLeft
                  injection hPair with hOutcome _hCtx
                  rw [hOutcome] at hMode
                  simp [Structured.Outcome.regular] at hMode
              | halt kind =>
                  have hPair :
                      (stmtOutcome, ctx) =
                        (Structured.Outcome.regular mid, midCtx) := by
                    simpa [Block.runOpen, hStmt, hMode] using hLeft
                  injection hPair with hOutcome _hCtx
                  rw [hOutcome] at hMode
                  simp [Structured.Outcome.regular] at hMode

theorem runOpen_append_nonregular_exists (program : Program) :
    ∀ (left right : List Stmt) (ctx : Ctx) (state : RunState)
      (outcome : Outcome) (runCtx : Ctx),
      (∃ fuel, Block.runOpen program ctx fuel { stmts := left } state =
        .ok (outcome, runCtx)) →
      outcome.mode ≠ .regular →
      ∃ fuel, Block.runOpen program ctx fuel { stmts := left ++ right } state =
        .ok (outcome, runCtx) := by
  intro left
  induction left with
  | nil =>
      intro right ctx state outcome runCtx hLeft hMode
      rcases hLeft with ⟨fuelLeft, hLeft⟩
      rcases runOpen_nil_ok hLeft with ⟨hOutcome, _hCtx⟩
      cases hOutcome
      simp at hMode
  | cons stmt rest ih =>
      intro right ctx state outcome runCtx hLeft hMode
      rcases hLeft with ⟨fuelLeft, hLeft⟩
      cases fuelLeft with
      | zero =>
          simp [Block.runOpen, invalid, Structured.invalid] at hLeft
      | succ fuelLeft =>
          cases hStmt : Stmt.run program ctx fuelLeft stmt state with
          | error err =>
              simp [Block.runOpen, hStmt] at hLeft
          | ok stmtResult =>
              rcases stmtResult with ⟨stmtOutcome, stmtCtx⟩
              cases hModeStmt : stmtOutcome.mode with
              | regular =>
                  simp [Block.runOpen, hStmt, hModeStmt] at hLeft
                  rcases ih right stmtCtx stmtOutcome.state outcome runCtx
                      ⟨fuelLeft, hLeft⟩ hMode with
                    ⟨fuelRest, hRestAppend⟩
                  let fuel := Nat.max fuelLeft fuelRest + 1
                  refine ⟨fuel, ?_⟩
                  have hStmt' :
                      Stmt.run program ctx (Nat.max fuelLeft fuelRest) stmt state =
                        .ok (stmtOutcome, stmtCtx) :=
                    Stmt.run_mono program (Nat.le_max_left _ _) hStmt
                  have hRestAppend' :
                      Block.runOpen program stmtCtx (Nat.max fuelLeft fuelRest)
                          { stmts := rest ++ right } stmtOutcome.state =
                        .ok (outcome, runCtx) :=
                    Block.runOpen_mono program (Nat.le_max_right _ _)
                      hRestAppend
                  simp [fuel, Block.runOpen, hStmt', hModeStmt, hRestAppend']
              | brk =>
                  have hPair :
                      (stmtOutcome, ctx) = (outcome, runCtx) := by
                    simpa [Block.runOpen, hStmt, hModeStmt] using hLeft
                  injection hPair with hOutcome hCtx
                  exact ⟨fuelLeft + 1,
                    by
                      rw [← hOutcome, ← hCtx]
                      simp [Block.runOpen, hStmt, hModeStmt]⟩
              | cont =>
                  have hPair :
                      (stmtOutcome, ctx) = (outcome, runCtx) := by
                    simpa [Block.runOpen, hStmt, hModeStmt] using hLeft
                  injection hPair with hOutcome hCtx
                  exact ⟨fuelLeft + 1,
                    by
                      rw [← hOutcome, ← hCtx]
                      simp [Block.runOpen, hStmt, hModeStmt]⟩
              | leave =>
                  have hPair :
                      (stmtOutcome, ctx) = (outcome, runCtx) := by
                    simpa [Block.runOpen, hStmt, hModeStmt] using hLeft
                  injection hPair with hOutcome hCtx
                  exact ⟨fuelLeft + 1,
                    by
                      rw [← hOutcome, ← hCtx]
                      simp [Block.runOpen, hStmt, hModeStmt]⟩
              | halt kind =>
                  have hPair :
                      (stmtOutcome, ctx) = (outcome, runCtx) := by
                    simpa [Block.runOpen, hStmt, hModeStmt] using hLeft
                  injection hPair with hOutcome hCtx
                  exact ⟨fuelLeft + 1,
                    by
                      rw [← hOutcome, ← hCtx]
                      simp [Block.runOpen, hStmt, hModeStmt]⟩

end Block

end Direct
end Locals

namespace Functions

namespace Outcome

theorem eq_regular_of_mode {outcome : Outcome}
    (hMode : outcome.mode = .regular) :
    outcome = Structured.Outcome.regular outcome.state := by
  cases outcome
  cases hMode
  rfl

end Outcome

namespace Switch

theorem select_toLocals (returns : List Name) (scrutinee : Word)
    (cases : List (Word × Block)) (defaultBody : Option Block) :
    Locals.Direct.Switch.select scrutinee (CaseList.toLocals returns cases)
        (Default.toLocals returns defaultBody) =
      Option.map (Block.toLocals returns)
        (Switch.select scrutinee cases defaultBody) := by
  induction cases with
  | nil =>
      cases defaultBody <;> rfl
  | cons head rest ih =>
      rcases head with ⟨value, body⟩
      by_cases hEq : value = scrutinee
      · simp [Switch.select, Locals.Direct.Switch.select,
          CaseList.toLocals, hEq]
      · simp [Switch.select, Locals.Direct.Switch.select,
          CaseList.toLocals, hEq, ih]

end Switch

namespace FunList

theorem lookup_toLocals {name : Name} {functions : List FunDef} {fn : FunDef}
    (hLookup : find? name functions = some fn) :
    Locals.Direct.ProcList.lookup? name (toLocalsProcs functions) =
      some fn.toLocalsProc := by
  induction functions with
  | nil =>
      simp [find?] at hLookup
  | cons head rest ih =>
      by_cases hEq : head.name = name
      · simp [find?, hEq] at hLookup
        cases hLookup
        cases hEq
        simp [toLocalsProcs, Locals.Direct.ProcList.lookup?,
          FunDef.toLocalsProc]
      · simp [find?, hEq] at hLookup
        simp [toLocalsProcs, Locals.Direct.ProcList.lookup?,
          FunDef.toLocalsProc, hEq]
        simpa [FunDef.toLocalsProc] using ih hLookup

end FunList

namespace Lower

theorem evalArgs_runOpen_exists (program : Program) (ctx : Ctx) :
    ∀ {args : List (Expr 1)} {state state' : RunState},
      Direct.evalArgs ctx args state = .ok state' →
      ∃ fuel,
        Locals.Direct.Block.runOpen program.toLocals ctx fuel
          { stmts := evalArgs args } state =
          .ok (Structured.Outcome.regular state', ctx) := by
  intro args
  induction args with
  | nil =>
      intro state state' hRun
      simp [Direct.evalArgs] at hRun
      cases hRun
      exact ⟨1, by simp [evalArgs, Locals.Direct.Block.runOpen,
        Structured.Outcome.regular]⟩
  | cons arg rest ih =>
      intro state state' hRun
      unfold Direct.evalArgs at hRun
      cases hArgs :
          Locals.Direct.Expr.ExprSeq.runCode ctx 0
            (Lower.argExprs (arg :: rest)) state.evm with
      | error err =>
          simp [hArgs] at hRun
      | ok evmAfterArgs =>
          simp [hArgs] at hRun
          cases hRun
          refine ⟨2, ?_⟩
          simp [evalArgs, Locals.Direct.Block.runOpen,
            Locals.Direct.Stmt.run, hArgs, Structured.Outcome.regular]

theorem pushReturns_runOpen_exists (program : Program) (ctx : Ctx) :
    ∀ {returns : List Name} {state state' : RunState},
      Direct.pushReturns ctx returns state = .ok state' →
      ∃ fuel,
        Locals.Direct.Block.runOpen program.toLocals ctx fuel
          { stmts := pushReturns returns } state =
          .ok (Structured.Outcome.regular state', ctx) := by
  intro returns
  cases returns with
  | nil =>
      intro state state' hRun
      simp [Direct.pushReturns] at hRun
      cases hRun
      exact ⟨1, by simp [pushReturns, Locals.Direct.Block.runOpen,
        Structured.Outcome.regular]⟩
  | cons name rest =>
      intro state state' hRun
      unfold Direct.pushReturns at hRun
      cases hExprs :
          Locals.Direct.Expr.ExprSeq.runCode ctx 0
            (returnExprs (name :: rest)) state.evm with
      | error err =>
          simp [hExprs] at hRun
      | ok evmAfterReturns =>
          simp [hExprs] at hRun
          cases hRun
          refine ⟨2, ?_⟩
          simp [pushReturns, Locals.Direct.Block.runOpen,
            Locals.Direct.Stmt.run, hExprs, Structured.Outcome.regular]

theorem initReturns_runOpen_exists (program : Program) :
    ∀ {returns : List Name} {ctx ctx' : Ctx} {state state' : RunState},
      Direct.initReturns returns ctx state = .ok (state', ctx') →
      ∃ fuel,
        Locals.Direct.Block.runOpen program.toLocals ctx fuel
          { stmts := initReturns returns } state =
          .ok (Structured.Outcome.regular state', ctx') := by
  intro returns
  induction returns with
  | nil =>
      intro ctx ctx' state state' hRun
      simp [Direct.initReturns] at hRun
      rcases hRun with ⟨hState, hCtx⟩
      cases hState
      cases hCtx
      exact ⟨1, by simp [initReturns, Locals.Direct.Block.runOpen,
        Structured.Outcome.regular]⟩
  | cons name rest ih =>
      intro ctx ctx' state state' hRun
      unfold Direct.initReturns at hRun
      cases hHead :
          Locals.Direct.Expr.runState ctx (.lit Direct.zero) state with
      | error err =>
          simp [hHead] at hRun
      | ok stateAfterHead =>
          simp [hHead] at hRun
          rcases ih hRun with ⟨fuelRest, hRest⟩
          refine ⟨fuelRest + 1, ?_⟩
          have hHead' :
              Locals.Direct.Expr.runState ctx (.lit zero) state =
                .ok stateAfterHead := by
            simpa [Direct.zero, zero] using hHead
          simp [initReturns, Locals.Direct.Block.runOpen,
            Locals.Direct.Stmt.run]
          rw [hHead']
          exact hRest

theorem assignReturnedTops_runOpen_exists (program : Program) (ctx : Ctx) :
    ∀ {targets : List Name} {state state' : RunState},
      Direct.assignReturnedTops ctx targets state = .ok state' →
      ∃ fuel,
        Locals.Direct.Block.runOpen program.toLocals ctx fuel
          { stmts := assignReturnedTopsRev targets } state =
          .ok (Structured.Outcome.regular state', ctx) := by
  intro targets
  induction targets with
  | nil =>
      intro state state' hRun
      simp [Direct.assignReturnedTops] at hRun
      cases hRun
      exact ⟨1, by simp [assignReturnedTopsRev, Locals.Direct.Block.runOpen,
        Structured.Outcome.regular]⟩
  | cons name rest ih =>
      intro state state' hRun
      unfold Direct.assignReturnedTops at hRun
      cases hHead : Direct.assignTopWithOffset ctx rest.length name state with
      | error err =>
          simp [hHead] at hRun
      | ok stateAfterHead =>
          simp [hHead] at hRun
          rcases ih hRun with ⟨fuelRest, hRest⟩
          refine ⟨fuelRest + 1, ?_⟩
          unfold Direct.assignTopWithOffset at hHead
          have hHead' :
              (do
                let depth ←
                  (Locals.Layout.lookupDepth? name ctx.layout).elim
                    Locals.invalid pure
                let swapOp ←
                  (Locals.StackOp.swap? (rest.length + depth)).elim
                  Locals.invalid pure
                let evmAfterSwap ← swapOp.step state.evm
                let evmAfterPop ← Structured.BasicOp.pop.step evmAfterSwap
                .ok (state.withEVM evmAfterPop)) = .ok stateAfterHead := by
            simpa [Locals.invalid] using hHead
          simp [assignReturnedTopsRev, Locals.Direct.Block.runOpen,
            Locals.Direct.Stmt.run, Structured.Outcome.regular]
          cases hDepth : Locals.Layout.lookupDepth? name ctx.layout with
          | none =>
              simp [hDepth, Locals.invalid, Structured.invalid] at hHead
          | some depth =>
              cases hSwap : Locals.StackOp.swap? (rest.length + depth) with
              | none =>
                  simp [hDepth, hSwap, Locals.invalid, Structured.invalid] at hHead
              | some swapOp =>
                  cases hSwapStep : swapOp.step state.evm with
                  | error err =>
                      simp [hDepth, hSwap, hSwapStep] at hHead
                  | ok evmAfterSwap =>
                      cases hPop :
                          Structured.BasicOp.pop.step evmAfterSwap with
                      | error err =>
                          simp [hDepth, hSwap, hSwapStep, hPop] at hHead
                      | ok evmAfterPop =>
                          simp [hDepth, hSwap, hSwapStep, hPop] at hHead
                          cases hHead
                          simp [hDepth, hSwap, hSwapStep, hPop, hRest,
                            Structured.Outcome.regular]

end Lower

theorem Block.toLocals_eq_stmts (returns : List Name) (block : Block) :
    Block.toLocals returns block =
      { stmts := StmtList.toLocals returns block.stmts } := by
  cases block
  rfl

namespace FunDef

def lowerBodyResult (retc : Nat) (bodyCtx : Locals.Ctx)
    (bodyOutcome : Outcome) :
    Except EVMException Outcome :=
  match bodyOutcome.mode with
  | .regular => do
      let stateAfterCleanup ←
        Locals.Direct.Ctx.runCleanupToPreserving bodyCtx retc 0
          bodyOutcome.state
      .ok (Structured.Outcome.regular stateAfterCleanup)
  | .brk | .cont =>
      Structured.invalid
  | .leave | .halt _ =>
      .ok bodyOutcome

end FunDef

namespace Direct

set_option maxHeartbeats 1000000 in
mutual
  theorem Block.runOpen_mono (program : Program) :
      ∀ {returns : List Name} {fuel fuel' : Nat} {ctx : Ctx}
        {block : Block} {state : RunState} {outcome : Outcome}
        {runCtx : Ctx},
        fuel ≤ fuel' →
        Block.runOpen program returns ctx fuel block state =
          .ok (outcome, runCtx) →
        Block.runOpen program returns ctx fuel' block state =
          .ok (outcome, runCtx) := by
    intro returns fuel fuel' ctx block state outcome runCtx hLe hRun
    cases fuel with
    | zero =>
        cases block
        simp [Block.runOpen, Structured.invalid] at hRun
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
                    simpa [Block.runOpen] using hRun
                | cons stmt rest =>
                    cases hStmt :
                        Stmt.run program returns ctx fuel stmt state with
                    | error err =>
                        simp [Block.runOpen, hStmt] at hRun
                    | ok stmtResult =>
                        rcases stmtResult with ⟨stmtOutcome, stmtCtx⟩
                        have hStmt' :
                            Stmt.run program returns ctx fuel' stmt state =
                              .ok (stmtOutcome, stmtCtx) :=
                          Stmt.run_mono program hFuelLe hStmt
                        cases hMode : stmtOutcome.mode with
                        | regular =>
                            simp [Block.runOpen, hStmt, hStmt', hMode]
                              at hRun ⊢
                            exact
                              Block.runOpen_mono program hFuelLe hRun
                        | brk =>
                            simp [Block.runOpen, hStmt, hStmt', hMode]
                              at hRun ⊢
                            exact hRun
                        | cont =>
                            simp [Block.runOpen, hStmt, hStmt', hMode]
                              at hRun ⊢
                            exact hRun
                        | leave =>
                            simp [Block.runOpen, hStmt, hStmt', hMode]
                              at hRun ⊢
                            exact hRun
                        | halt kind =>
                            simp [Block.runOpen, hStmt, hStmt', hMode]
                              at hRun ⊢
                            exact hRun
  termination_by
    returns fuel _fuel' _ctx block _state _outcome _runCtx _hLe _hRun =>
      (fuel, 0, sizeOf block)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  theorem Block.runScoped_mono (program : Program) :
      ∀ {returns : List Name} {fuel fuel' : Nat} {ctx : Ctx}
        {block : Block} {state : RunState} {outcome : Outcome},
        fuel ≤ fuel' →
        Block.runScoped program returns ctx block fuel state = .ok outcome →
        Block.runScoped program returns ctx block fuel' state = .ok outcome := by
    intro returns fuel fuel' ctx block state outcome hLe hRun
    unfold Block.runScoped at hRun ⊢
    cases hOpen : Block.runOpen program returns ctx fuel block state with
    | error err =>
        simp [hOpen] at hRun
    | ok openResult =>
        rcases openResult with ⟨openOutcome, finalCtx⟩
        have hOpen' :
            Block.runOpen program returns ctx fuel' block state =
              .ok (openOutcome, finalCtx) :=
          Block.runOpen_mono program hLe hOpen
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
    returns fuel _fuel' _ctx block _state _outcome _hLe _hRun =>
      (fuel, 1, sizeOf block)
  decreasing_by
    all_goals simp_wf
    all_goals
      first
      | omega
      | exact Prod.Lex.right _
          (Prod.Lex.left _ _ (by omega))

  theorem FunDef.runBody_mono (program : Program) :
      ∀ {fuel fuel' : Nat} {fn : FunDef} {state : RunState}
        {outcome : Outcome},
        fuel ≤ fuel' →
        FunDef.runBody program fn fuel state = .ok outcome →
        FunDef.runBody program fn fuel' state = .ok outcome := by
    intro fuel fuel' fn state outcome hLe hRun
    cases fuel with
    | zero =>
        simp [FunDef.runBody, Structured.invalid] at hRun
    | succ fuel =>
        cases fuel' with
        | zero =>
            omega
        | succ fuel' =>
            have hFuelLe : fuel ≤ fuel' := Nat.succ_le_succ_iff.mp hLe
            unfold FunDef.runBody at hRun ⊢
            let entryCtx :=
              Locals.Ctx.procEntryWithLayoutAndRetc
                fn.params.reverse fn.returns.length
            cases hInit : initReturns fn.returns entryCtx state with
            | error err =>
                simp [entryCtx, hInit] at hRun
            | ok initResult =>
                rcases initResult with ⟨stateAfterInit, initCtx⟩
                cases hBody :
                    Block.runOpen program fn.returns initCtx fuel fn.body
                      stateAfterInit with
                | error err =>
                    simp [entryCtx, hInit, hBody] at hRun
                | ok bodyResult =>
                    rcases bodyResult with ⟨bodyOutcome, bodyCtx⟩
                    have hBody' :
                        Block.runOpen program fn.returns initCtx fuel'
                            fn.body stateAfterInit =
                          .ok (bodyOutcome, bodyCtx) :=
                      Block.runOpen_mono program hFuelLe hBody
                    cases hMode : bodyOutcome.mode <;>
                      simp [entryCtx, hInit, hBody, hBody', hMode]
                        at hRun ⊢ <;>
                      exact hRun
  termination_by
    fuel _fuel' fn _state _outcome _hLe _hRun =>
      (fuel, 2, sizeOf fn.body)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  theorem Stmt.runForLoop_mono (program : Program) :
      ∀ {returns : List Name} {fuel fuel' : Nat} {loopCtx : Ctx}
        {cond : Expr 1} {postBase : Ctx} {post : Block}
        {bodyBase : Ctx} {body : Block} {state : RunState}
        {outcome : Outcome},
        fuel ≤ fuel' →
        Stmt.runForLoop program returns loopCtx cond postBase post bodyBase body
          fuel state = .ok outcome →
        Stmt.runForLoop program returns loopCtx cond postBase post bodyBase body
          fuel' state = .ok outcome := by
    intro returns fuel fuel' loopCtx cond postBase post bodyBase body state
      outcome hLe hRun
    cases fuel with
    | zero =>
        simp [Stmt.runForLoop, Structured.invalid] at hRun
    | succ fuel =>
        cases fuel' with
        | zero =>
            omega
        | succ fuel' =>
            have hFuelLe : fuel ≤ fuel' := Nat.succ_le_succ_iff.mp hLe
            unfold Stmt.runForLoop at hRun ⊢
            cases hCond : Locals.Direct.Expr.runCondition loopCtx cond state with
            | error err =>
                simp [hCond] at hRun ⊢
            | ok condResult =>
                rcases condResult with ⟨stateAfterCond, condTrue⟩
                cases condTrue with
                | false =>
                    simp [hCond] at hRun ⊢
                    exact hRun
                | true =>
                    simp [hCond] at hRun ⊢
                    cases hBody :
                        Block.runScoped program returns bodyBase body fuel
                          stateAfterCond with
                    | error err =>
                        simp [hBody] at hRun
                    | ok bodyOutcome =>
                        have hBody' :
                            Block.runScoped program returns bodyBase body fuel'
                              stateAfterCond = .ok bodyOutcome :=
                          Block.runScoped_mono program hFuelLe hBody
                        cases hBodyMode : bodyOutcome.mode with
                        | brk =>
                            simp [hBody, hBody', hBodyMode] at hRun ⊢
                            exact hRun
                        | regular =>
                            simp [hBody, hBody', hBodyMode] at hRun ⊢
                            cases hPost :
                                Block.runScoped program returns postBase post fuel
                                  bodyOutcome.state with
                            | error err =>
                                simp [hPost] at hRun
                            | ok postOutcome =>
                                have hPost' :
                                    Block.runScoped program returns postBase post
                                      fuel' bodyOutcome.state =
                                      .ok postOutcome :=
                                  Block.runScoped_mono program hFuelLe hPost
                                cases hPostMode : postOutcome.mode with
                                | regular =>
                                    simp [hPost, hPost', hPostMode] at hRun ⊢
                                    exact
                                      Stmt.runForLoop_mono program hFuelLe hRun
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
                                Block.runScoped program returns postBase post fuel
                                  bodyOutcome.state with
                            | error err =>
                                simp [hPost] at hRun
                            | ok postOutcome =>
                                have hPost' :
                                    Block.runScoped program returns postBase post
                                      fuel' bodyOutcome.state =
                                      .ok postOutcome :=
                                  Block.runScoped_mono program hFuelLe hPost
                                cases hPostMode : postOutcome.mode with
                                | regular =>
                                    simp [hPost, hPost', hPostMode] at hRun ⊢
                                    exact
                                      Stmt.runForLoop_mono program hFuelLe hRun
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
    returns fuel _fuel' _loopCtx _cond _postBase _post _bodyBase _body
      _state _outcome _hLe _hRun => (fuel, 3, 0)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  theorem Stmt.run_mono (program : Program) :
      ∀ {returns : List Name} {fuel fuel' : Nat} {ctx : Ctx}
        {stmt : Stmt} {state : RunState} {outcome : Outcome}
        {runCtx : Ctx},
        fuel ≤ fuel' →
        Stmt.run program returns ctx fuel stmt state =
          .ok (outcome, runCtx) →
        Stmt.run program returns ctx fuel' stmt state =
          .ok (outcome, runCtx) := by
    intro returns fuel fuel' ctx stmt state outcome runCtx hLe hRun
    cases stmt with
    | expr expr =>
        simpa [Stmt.run] using hRun
    | let_ name value =>
        simpa [Stmt.run] using hRun
    | assign name value =>
        simpa [Stmt.run] using hRun
    | block body =>
        unfold Stmt.run at hRun ⊢
        cases hBody : Block.runScoped program returns ctx body fuel state with
        | error err =>
            simp [hBody] at hRun
        | ok bodyOutcome =>
            have hBody' :
                Block.runScoped program returns ctx body fuel' state =
                  .ok bodyOutcome :=
              Block.runScoped_mono program hLe hBody
            simp [hBody, hBody'] at hRun ⊢
            exact hRun
    | if_ cond body =>
        cases fuel with
        | zero =>
            simp [Stmt.run, Structured.invalid] at hRun
        | succ fuel =>
            cases fuel' with
            | zero =>
                omega
            | succ fuel' =>
                have hFuelLe : fuel ≤ fuel' := Nat.succ_le_succ_iff.mp hLe
                unfold Stmt.run at hRun ⊢
                cases hCond :
                    Locals.Direct.Expr.runCondition ctx cond state with
                | error err =>
                    simp [hCond] at hRun ⊢
                | ok condResult =>
                    rcases condResult with ⟨stateAfterCond, condTrue⟩
                    cases condTrue with
                    | false =>
                        simp [hCond] at hRun ⊢
                        exact hRun
                    | true =>
                        simp [hCond] at hRun ⊢
                        cases hBody :
                            Block.runScoped program returns ctx body fuel
                              stateAfterCond with
                        | error err =>
                            simp [hBody] at hRun
                        | ok bodyOutcome =>
                            have hBody' :
                                Block.runScoped program returns ctx body fuel'
                                  stateAfterCond = .ok bodyOutcome :=
                              Block.runScoped_mono program hFuelLe hBody
                            simp [hBody, hBody'] at hRun ⊢
                            exact hRun
    | switch scrutinee cases defaultBody =>
        cases fuel with
        | zero =>
            simp [Stmt.run, Structured.invalid] at hRun
        | succ fuel =>
            cases fuel' with
            | zero =>
                omega
            | succ fuel' =>
                have hFuelLe : fuel ≤ fuel' := Nat.succ_le_succ_iff.mp hLe
                unfold Stmt.run at hRun ⊢
                cases hScrutinee :
                    Locals.Direct.Expr.runState ctx scrutinee state with
                | error err =>
                    simp [hScrutinee] at hRun ⊢
                | ok stateAfterScrutinee =>
                    cases hPop : stateAfterScrutinee.evm.stack.pop with
                    | none =>
                        simp [hScrutinee, hPop, Structured.invalid]
                          at hRun ⊢
                    | some pair =>
                        rcases pair with ⟨stack, value⟩
                        let stateAfterPop :=
                          stateAfterScrutinee.withEVM
                            { stateAfterScrutinee.evm with stack := stack }
                        cases hSelected :
                            Switch.select value cases defaultBody with
                        | none =>
                            simp [hScrutinee, hPop, hSelected] at hRun ⊢
                            exact hRun
                        | some selected =>
                            simp [hScrutinee, hPop, hSelected] at hRun ⊢
                            cases hBody :
                                Block.runScoped program returns ctx selected fuel
                                  (stateAfterScrutinee.withEVM
                                    { stateAfterScrutinee.evm with
                                      stack := stack }) with
                            | error err =>
                                simpa [hBody] using hRun
                            | ok bodyOutcome =>
                                have hBody' :
                                    Block.runScoped program returns ctx selected
                                      fuel'
                                      (stateAfterScrutinee.withEVM
                                        { stateAfterScrutinee.evm with
                                          stack := stack }) =
                                      .ok bodyOutcome :=
                                  Block.runScoped_mono program hFuelLe hBody
                                simpa [hBody, hBody'] using hRun
    | for_ init cond post body =>
        cases fuel with
        | zero =>
            simp [Stmt.run, Structured.invalid] at hRun
        | succ fuel =>
            cases fuel' with
            | zero =>
                omega
            | succ fuel' =>
                have hFuelLe : fuel ≤ fuel' := Nat.succ_le_succ_iff.mp hLe
                unfold Stmt.run at hRun ⊢
                let initBase := ctx.withoutLoopControl
                cases hInit :
                    Block.runOpen program returns initBase fuel init state with
                | error err =>
                    simp [initBase, hInit] at hRun
                | ok initResult =>
                    rcases initResult with ⟨initOutcome, initCtx⟩
                    have hInit' :
                        Block.runOpen program returns initBase fuel' init state =
                          .ok (initOutcome, initCtx) :=
                      Block.runOpen_mono program hFuelLe hInit
                    cases hInitMode : initOutcome.mode with
                    | regular =>
                        simp [initBase, hInit, hInit', hInitMode] at hRun ⊢
                        let postBase := initCtx.withoutLoopControl
                        let bodyBase :=
                          initCtx.withLoopControl initCtx.layout.length
                        cases hLoop :
                            Stmt.runForLoop program returns initCtx cond
                              postBase post bodyBase body fuel
                              initOutcome.state with
                        | error err =>
                            simp [postBase, bodyBase, hLoop] at hRun
                        | ok loopOutcome =>
                            have hLoop' :
                                Stmt.runForLoop program returns initCtx cond
                                  postBase post bodyBase body fuel'
                                  initOutcome.state =
                                  .ok loopOutcome :=
                              Stmt.runForLoop_mono program hFuelLe hLoop
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
        simpa [Stmt.run] using hRun
    | cont =>
        simpa [Stmt.run] using hRun
    | leave =>
        simpa [Stmt.run] using hRun
    | call targets functionName args =>
        cases fuel with
        | zero =>
            simp [Stmt.run, Structured.invalid] at hRun
        | succ fuel =>
            cases fuel' with
            | zero =>
                omega
            | succ fuel' =>
                have hFuelLe : fuel ≤ fuel' := Nat.succ_le_succ_iff.mp hLe
                unfold Stmt.run at hRun ⊢
                cases hArgs : evalArgs ctx args state with
                | error err =>
                    simp [hArgs] at hRun ⊢
                | ok stateAfterArgs =>
                    cases hLookup :
                        FunList.find? functionName program.functions with
                    | none =>
                        simp [hArgs, hLookup, Structured.invalid] at hRun
                    | some fn =>
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
                                FunDef.runBody program fn fuel callState with
                            | error err =>
                                simp [hArgs, hLookup, hSplit, callState, hBody]
                                  at hRun
                            | ok bodyOutcome =>
                                have hBody' :
                                    FunDef.runBody program fn fuel'
                                        callState =
                                      .ok bodyOutcome :=
                                  FunDef.runBody_mono program hFuelLe hBody
                                cases hBodyMode : bodyOutcome.mode <;>
                                  simp [hArgs, hLookup, hSplit, callState,
                                    hBody, hBody', hBodyMode] at hRun ⊢ <;>
                                  exact hRun
    | terminal kind =>
        simpa [Stmt.run] using hRun
    | terminalArgs kind args =>
        simpa [Stmt.run] using hRun
  termination_by
    returns fuel _fuel' _ctx stmt _state _outcome _runCtx _hLe _hRun =>
      (fuel, 4, sizeOf stmt)
  decreasing_by
    all_goals simp_wf
    all_goals
      first
      | omega
      | exact Prod.Lex.right _
          (Prod.Lex.left _ _ (by omega))
end

namespace Block

theorem runOpen_nil_ok {program : Program} {returns : List Name}
    {ctx : Ctx} {fuel : Nat} {state : RunState} {outcome : Outcome}
    {runCtx : Ctx}
    (hRun : Block.runOpen program returns ctx fuel { stmts := [] } state =
      .ok (outcome, runCtx)) :
    outcome = Structured.Outcome.regular state ∧ runCtx = ctx := by
  cases fuel with
  | zero =>
      simp [Block.runOpen, Structured.invalid] at hRun
  | succ fuel =>
      have hPair :
          (Structured.Outcome.regular state, ctx) = (outcome, runCtx) := by
        simpa [Block.runOpen] using hRun
      injection hPair with hOutcome hCtx
      exact ⟨hOutcome.symm, hCtx.symm⟩

theorem runOpen_append_regular_exists (program : Program) :
    ∀ {returns : List Name} (left right : List Stmt) (ctx midCtx : Ctx)
      (state mid : RunState) (outcome : Outcome) (runCtx : Ctx),
      (∃ fuel, Block.runOpen program returns ctx fuel { stmts := left } state =
        .ok (Structured.Outcome.regular mid, midCtx)) →
      (∃ fuel, Block.runOpen program returns midCtx fuel { stmts := right } mid =
        .ok (outcome, runCtx)) →
      ∃ fuel, Block.runOpen program returns ctx fuel
        { stmts := left ++ right } state = .ok (outcome, runCtx) := by
  intro returns left
  induction left with
  | nil =>
      intro right ctx midCtx state mid outcome runCtx hLeft hRight
      rcases hLeft with ⟨fuelLeft, hLeft⟩
      rcases runOpen_nil_ok hLeft with ⟨hOutcome, hCtx⟩
      cases hOutcome
      cases hCtx
      simpa using hRight
  | cons stmt rest ih =>
      intro right ctx midCtx state mid outcome runCtx hLeft hRight
      rcases hLeft with ⟨fuelLeft, hLeft⟩
      cases fuelLeft with
      | zero =>
          simp [Block.runOpen, Structured.invalid] at hLeft
      | succ fuelLeft =>
          cases hStmt :
              Stmt.run program returns ctx fuelLeft stmt state with
          | error err =>
              simp [Block.runOpen, hStmt] at hLeft
          | ok stmtResult =>
              rcases stmtResult with ⟨stmtOutcome, stmtCtx⟩
              cases hMode : stmtOutcome.mode with
              | regular =>
                  simp [Block.runOpen, hStmt, hMode] at hLeft
                  have hRest :
                      ∃ fuel,
                        Block.runOpen program returns stmtCtx fuel
                          { stmts := rest } stmtOutcome.state =
                          .ok (Structured.Outcome.regular mid, midCtx) :=
                    ⟨fuelLeft, hLeft⟩
                  rcases ih right stmtCtx midCtx stmtOutcome.state mid outcome
                      runCtx hRest hRight with
                    ⟨fuelRest, hRestAppend⟩
                  let fuel := Nat.max fuelLeft fuelRest + 1
                  refine ⟨fuel, ?_⟩
                  have hStmt' :
                      Stmt.run program returns ctx
                          (Nat.max fuelLeft fuelRest) stmt state =
                        .ok (stmtOutcome, stmtCtx) :=
                    Stmt.run_mono program (Nat.le_max_left _ _) hStmt
                  have hRestAppend' :
                      Block.runOpen program returns stmtCtx
                          (Nat.max fuelLeft fuelRest)
                          { stmts := rest ++ right } stmtOutcome.state =
                        .ok (outcome, runCtx) :=
                    Block.runOpen_mono program (Nat.le_max_right _ _)
                      hRestAppend
                  simp [fuel, Block.runOpen, hStmt', hMode, hRestAppend']
              | brk =>
                  have hPair :
                      (stmtOutcome, ctx) =
                        (Structured.Outcome.regular mid, midCtx) := by
                    simpa [Block.runOpen, hStmt, hMode] using hLeft
                  injection hPair with hOutcome _hCtx
                  rw [hOutcome] at hMode
                  simp [Structured.Outcome.regular] at hMode
              | cont =>
                  have hPair :
                      (stmtOutcome, ctx) =
                        (Structured.Outcome.regular mid, midCtx) := by
                    simpa [Block.runOpen, hStmt, hMode] using hLeft
                  injection hPair with hOutcome _hCtx
                  rw [hOutcome] at hMode
                  simp [Structured.Outcome.regular] at hMode
              | leave =>
                  have hPair :
                      (stmtOutcome, ctx) =
                        (Structured.Outcome.regular mid, midCtx) := by
                    simpa [Block.runOpen, hStmt, hMode] using hLeft
                  injection hPair with hOutcome _hCtx
                  rw [hOutcome] at hMode
                  simp [Structured.Outcome.regular] at hMode
              | halt kind =>
                  have hPair :
                      (stmtOutcome, ctx) =
                        (Structured.Outcome.regular mid, midCtx) := by
                    simpa [Block.runOpen, hStmt, hMode] using hLeft
                  injection hPair with hOutcome _hCtx
                  rw [hOutcome] at hMode
                  simp [Structured.Outcome.regular] at hMode

end Block

theorem Stmt.run_nonregular_ctx (program : Program)
    {returns : List Name} {ctx : Ctx} {fuel : Nat} {stmt : Stmt}
    {state : RunState} {outcome : Outcome} {runCtx : Ctx}
    (hRun : Stmt.run program returns ctx fuel stmt state =
      .ok (outcome, runCtx))
    (hNonregular : outcome.mode ≠ .regular) :
    runCtx = ctx := by
  -- The statement interpreter always restores the incoming context before
  -- reporting an early control effect.  Regular statements are the only ones
  -- allowed to extend the layout.
  cases stmt with
  | expr expr =>
      unfold Stmt.run at hRun
      cases hExpr : Locals.Direct.Expr.runState ctx expr state with
      | error err => simp [hExpr] at hRun
      | ok state' =>
          have hPair :
              (Structured.Outcome.regular state', ctx) = (outcome, runCtx) := by
            simpa [hExpr] using hRun
          injection hPair with _hOutcome hCtx
          exact hCtx.symm
  | let_ name value =>
      unfold Stmt.run at hRun
      cases hExpr : Locals.Direct.Expr.runState ctx value state with
      | error err => simp [hExpr] at hRun
      | ok state' =>
          have hPair :
              (Structured.Outcome.regular state',
                  ctx.withLayout (name :: ctx.layout)) = (outcome, runCtx) := by
            simpa [hExpr] using hRun
          injection hPair with hOutcome _hCtx
          have hRegular : outcome.mode = .regular := by
            rw [← hOutcome]
            rfl
          exact (hNonregular hRegular).elim
  | assign name value =>
      unfold Stmt.run at hRun
      cases hValue : Locals.Direct.Expr.runState ctx value state with
      | error err => simp [hValue] at hRun
      | ok stateAfterValue =>
          simp [hValue, Direct.assignTop] at hRun
          cases hDepth : Locals.Layout.lookupDepth? name ctx.layout with
          | none =>
              simp [hDepth, Structured.invalid] at hRun
          | some depth =>
              cases hSwapOp : Locals.StackOp.swap? depth with
              | none =>
                  simp [hDepth, hSwapOp, Structured.invalid] at hRun
              | some swapOp =>
                  cases hSwap : swapOp.step stateAfterValue.evm with
                  | error err =>
                      simp [hDepth, hSwapOp, hSwap] at hRun
                  | ok evmAfterSwap =>
                      cases hPop : Structured.BasicOp.pop.step evmAfterSwap with
                      | error err =>
                          simp [hDepth, hSwapOp, hSwap, hPop] at hRun
                      | ok evmAfterPop =>
                          have hPair :
                              (Structured.Outcome.regular
                                  (stateAfterValue.withEVM evmAfterPop), ctx) =
                                (outcome, runCtx) := by
                            simpa [hDepth, hSwapOp, hSwap, hPop] using hRun
                          injection hPair with _hOutcome hCtx
                          exact hCtx.symm
  | block body =>
      unfold Stmt.run at hRun
      cases hBody : Block.runScoped program returns ctx body fuel state with
      | error err => simp [hBody] at hRun
      | ok bodyOutcome =>
          simp [hBody] at hRun
          rcases hRun with ⟨_, hCtx⟩
          exact hCtx.symm
  | if_ cond body =>
      cases fuel with
      | zero => simp [Stmt.run, Structured.invalid] at hRun
      | succ fuel =>
          unfold Stmt.run at hRun
          cases hCond : Locals.Direct.Expr.runCondition ctx cond state with
          | error err => simp [hCond] at hRun
          | ok condResult =>
              rcases condResult with ⟨stateAfterCond, condTrue⟩
              cases condTrue with
              | false =>
                  have hPair :
                      (Structured.Outcome.regular stateAfterCond, ctx) =
                        (outcome, runCtx) := by
                    simpa [hCond] using hRun
                  injection hPair with _hOutcome hCtx
                  exact hCtx.symm
              | true =>
                  simp [hCond] at hRun
                  cases hBody :
                      Block.runScoped program returns ctx body fuel
                        stateAfterCond with
                  | error err => simp [hBody] at hRun
                  | ok bodyOutcome =>
                      simp [hBody] at hRun
                      rcases hRun with ⟨_, hCtx⟩
                      exact hCtx.symm
  | switch scrutinee cases defaultBody =>
      cases fuel with
      | zero => simp [Stmt.run, Structured.invalid] at hRun
      | succ fuel =>
          unfold Stmt.run at hRun
          cases hScrutinee :
              Locals.Direct.Expr.runState ctx scrutinee state with
          | error err => simp [hScrutinee] at hRun
          | ok stateAfterScrutinee =>
              cases hPop : stateAfterScrutinee.evm.stack.pop with
              | none => simp [hScrutinee, hPop, Structured.invalid] at hRun
              | some pair =>
                  rcases pair with ⟨stack, value⟩
                  cases hSelected :
                      Switch.select value cases defaultBody with
                  | none =>
                      let stateAfterPop :=
                        stateAfterScrutinee.withEVM
                          { stateAfterScrutinee.evm with stack := stack }
                      simp [hScrutinee, hPop, hSelected, stateAfterPop] at hRun
                      exact hRun.2.symm
                  | some body =>
                      simp [hScrutinee, hPop, hSelected] at hRun
                      cases hBody :
                          Block.runScoped program returns ctx body fuel
                            (stateAfterScrutinee.withEVM
                              { stateAfterScrutinee.evm with stack := stack }) with
                      | error err => simp [hBody] at hRun
                      | ok bodyOutcome =>
                          simp [hBody] at hRun
                          rcases hRun with ⟨_, hCtx⟩
                          exact hCtx.symm
  | for_ init cond post body =>
      cases fuel with
      | zero => simp [Stmt.run, Structured.invalid] at hRun
      | succ fuel =>
          unfold Stmt.run at hRun
          let initBase := ctx.withoutLoopControl
          cases hInit :
              Block.runOpen program returns initBase fuel init state with
          | error err => simp [initBase, hInit] at hRun
          | ok initResult =>
              rcases initResult with ⟨initOutcome, initCtx⟩
              cases hInitMode : initOutcome.mode with
              | regular =>
                  simp [initBase, hInit, hInitMode] at hRun
                  let postBase := initCtx.withoutLoopControl
                  let bodyBase := initCtx.withLoopControl initCtx.layout.length
                  cases hLoop :
                      Stmt.runForLoop program returns initCtx cond postBase post
                        bodyBase body fuel initOutcome.state with
                  | error err =>
                      simp [postBase, bodyBase, hLoop] at hRun
                  | ok loopOutcome =>
                      cases hLoopMode : loopOutcome.mode with
                      | regular =>
                          simp [postBase, bodyBase, hLoop, hLoopMode] at hRun
                          cases hCleanup :
                              Locals.Direct.Ctx.runCleanupTo initCtx
                                ctx.layout.length loopOutcome.state with
                          | error err =>
                              simp [hCleanup] at hRun
                          | ok state' =>
                              have hPair :
                                  (Structured.Outcome.regular state', ctx) =
                                    (outcome, runCtx) := by
                                simpa [hCleanup] using hRun
                              injection hPair with _hOutcome hCtx
                              exact hCtx.symm
                      | brk =>
                          simp [postBase, bodyBase, hLoop, hLoopMode,
                            Structured.invalid] at hRun
                      | cont =>
                          simp [postBase, bodyBase, hLoop, hLoopMode,
                            Structured.invalid] at hRun
                      | leave =>
                          simp [postBase, bodyBase, hLoop, hLoopMode] at hRun
                          rcases hRun with ⟨_, hCtx⟩
                          exact hCtx.symm
                      | halt kind =>
                          simp [postBase, bodyBase, hLoop, hLoopMode] at hRun
                          rcases hRun with ⟨_, hCtx⟩
                          exact hCtx.symm
              | brk =>
                  simp [initBase, hInit, hInitMode, Structured.invalid] at hRun
              | cont =>
                  simp [initBase, hInit, hInitMode, Structured.invalid] at hRun
              | leave =>
                  simp [initBase, hInit, hInitMode] at hRun
                  rcases hRun with ⟨_, hCtx⟩
                  exact hCtx.symm
              | halt kind =>
                  simp [initBase, hInit, hInitMode] at hRun
                  rcases hRun with ⟨_, hCtx⟩
                  exact hCtx.symm
  | brk =>
      unfold Stmt.run at hRun
      cases hTarget : ctx.breakDepth? with
      | none =>
          simp [hTarget, Structured.invalid] at hRun
      | some target =>
          cases hCleanup : Locals.Direct.Ctx.runCleanupTo ctx target state with
          | error err =>
              simp [hTarget, hCleanup] at hRun
          | ok state' =>
              have hPair :
                  (Structured.Outcome.brk state', ctx) = (outcome, runCtx) := by
                simpa [hTarget, hCleanup] using hRun
              injection hPair with _hOutcome hCtx
              exact hCtx.symm
  | cont =>
      unfold Stmt.run at hRun
      cases hTarget : ctx.continueDepth? with
      | none =>
          simp [hTarget, Structured.invalid] at hRun
      | some target =>
          cases hCleanup : Locals.Direct.Ctx.runCleanupTo ctx target state with
          | error err =>
              simp [hTarget, hCleanup] at hRun
          | ok state' =>
              have hPair :
                  (Structured.Outcome.cont state', ctx) = (outcome, runCtx) := by
                simpa [hTarget, hCleanup] using hRun
              injection hPair with _hOutcome hCtx
              exact hCtx.symm
  | leave =>
      unfold Stmt.run at hRun
      cases hPush : pushReturns ctx returns state with
      | error err =>
          simp [hPush] at hRun
      | ok stateAfterReturns =>
          cases hTarget : ctx.leaveDepth? with
          | none =>
              simp [hPush, hTarget, Structured.invalid] at hRun
          | some target =>
              cases hCleanup :
                  Locals.Direct.Ctx.runCleanupToPreserving ctx ctx.leaveRetc
                    target stateAfterReturns with
              | error err =>
                  simp [hPush, hTarget, hCleanup] at hRun
              | ok state' =>
                  cases hReturns : state'.returns with
                  | nil =>
                      simp [hPush, hTarget, hCleanup, hReturns,
                        Structured.invalid] at hRun
                  | cons ret rest =>
                      simp [hPush, hTarget, hCleanup, hReturns] at hRun
                      exact hRun.2.symm
  | call targets functionName args =>
      cases fuel with
      | zero => simp [Stmt.run, Structured.invalid] at hRun
      | succ fuel =>
          unfold Stmt.run at hRun
          cases hArgs : evalArgs ctx args state with
          | error err => simp [hArgs] at hRun
          | ok stateAfterArgs =>
              cases hLookup :
                  FunList.find? functionName program.functions with
              | none => simp [hArgs, hLookup, Structured.invalid] at hRun
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
                          FunDef.runBody program fn fuel callState with
                      | error err =>
                          simp [hArgs, hLookup, hSplit, callState, hBody] at hRun
                      | ok callOutcome =>
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
                                      simp [hPopRet, hAttach, Structured.invalid] at hRun
                                  | some stack =>
                                      let stateWithReturns :=
                                        returned.withEVM
                                          { callOutcome.state.evm with stack := stack }
                                      cases hAssign :
                                          assignReturnedTops ctx targets.reverse
                                            stateWithReturns with
                                      | error err =>
                                          simp [hPopRet, hAttach, stateWithReturns,
                                            hAssign] at hRun
                                      | ok stateAfterAssign =>
                                          have hPair :
                                              (Structured.Outcome.regular
                                                  stateAfterAssign, ctx) =
                                                (outcome, runCtx) := by
                                            simpa [hPopRet, hAttach, stateWithReturns,
                                              hAssign] using hRun
                                          injection hPair with _hOutcome hCtx
                                          exact hCtx.symm
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
                                      simp [hPopRet, hAttach, Structured.invalid] at hRun
                                  | some stack =>
                                      let stateWithReturns :=
                                        returned.withEVM
                                          { callOutcome.state.evm with stack := stack }
                                      cases hAssign :
                                          assignReturnedTops ctx targets.reverse
                                            stateWithReturns with
                                      | error err =>
                                          simp [hPopRet, hAttach, stateWithReturns,
                                            hAssign] at hRun
                                      | ok stateAfterAssign =>
                                          have hPair :
                                              (Structured.Outcome.regular
                                                  stateAfterAssign, ctx) =
                                                (outcome, runCtx) := by
                                            simpa [hPopRet, hAttach, stateWithReturns,
                                              hAssign] using hRun
                                          injection hPair with _hOutcome hCtx
                                          exact hCtx.symm
                          | brk =>
                              simp [hArgs, hLookup, hSplit, callState, hBody,
                                hMode, Structured.invalid] at hRun
                          | cont =>
                              simp [hArgs, hLookup, hSplit, callState, hBody,
                                hMode, Structured.invalid] at hRun
                          | halt kind =>
                              simp [hArgs, hLookup, hSplit, callState, hBody,
                                hMode] at hRun
                              rcases hRun with ⟨_, hCtx⟩
                              exact hCtx.symm
  | terminal kind =>
      unfold Stmt.run at hRun
      cases hCleanup : Locals.Direct.Ctx.runCleanupAll ctx state with
      | error err =>
          simp [hCleanup] at hRun
      | ok stateAfterCleanup =>
          cases hTerminal : Structured.Terminal.step kind stateAfterCleanup.evm with
          | error err =>
              simp [hCleanup, hTerminal] at hRun
          | ok evm =>
              have hPair :
                  (Structured.Outcome.halt kind (stateAfterCleanup.withEVM evm),
                      ctx) = (outcome, runCtx) := by
                simpa [hCleanup, hTerminal] using hRun
              injection hPair with _hOutcome hCtx
              exact hCtx.symm
  | terminalArgs kind args =>
      unfold Stmt.run at hRun
      cases hArgs :
          Locals.Direct.Expr.ExprSeq.runCode ctx 0 args state.evm with
      | error err =>
          simp [hArgs] at hRun
      | ok evmAfterArgs =>
          cases hTerminal : Structured.Terminal.step kind evmAfterArgs with
          | error err =>
              simp [hArgs, hTerminal] at hRun
          | ok evm =>
              have hPair :
                  (Structured.Outcome.halt kind (state.withEVM evm), ctx) =
                    (outcome, runCtx) := by
                simpa [hArgs, hTerminal] using hRun
              injection hPair with _hOutcome hCtx
              exact hCtx.symm

set_option maxHeartbeats 1200000 in
mutual
  theorem Block.runOpen_toLocals_exists (program : Program) :
      ∀ {returns : List Name} {ctx : Ctx} {fuel : Nat}
        {block : Block} {state : RunState} {outcome : Outcome}
        {runCtx : Ctx},
        Block.runOpen program returns ctx fuel block state =
          .ok (outcome, runCtx) →
        ∃ lowerFuel,
          Locals.Direct.Block.runOpen program.toLocals ctx lowerFuel
            (Block.toLocals returns block) state =
            .ok (outcome, runCtx) := by
    intro returns ctx fuel block state outcome runCtx hRun
    cases fuel with
    | zero =>
        cases block
        simp [Block.runOpen, Structured.invalid] at hRun
    | succ fuel =>
        cases block with
        | mk stmts =>
            cases stmts with
            | nil =>
                have hPair :
                    (Structured.Outcome.regular state, ctx) =
                      (outcome, runCtx) := by
                  simpa [Block.runOpen] using hRun
                injection hPair with hOutcome hCtx
                cases hOutcome
                cases hCtx
                exact ⟨1, by simp [Block.toLocals, StmtList.toLocals,
                  Locals.Direct.Block.runOpen,
                  Structured.Outcome.regular]⟩
            | cons stmt rest =>
                cases hStmt : Stmt.run program returns ctx fuel stmt state with
                | error err =>
                    simp [Block.runOpen, hStmt] at hRun
                | ok stmtResult =>
                    rcases stmtResult with ⟨stmtOutcome, stmtCtx⟩
                    rcases Stmt.run_toLocals_exists program hStmt with
                      ⟨stmtFuel, hStmtLower⟩
                    cases hMode : stmtOutcome.mode with
                      | regular =>
                          simp [Block.runOpen, hStmt, hMode] at hRun
                          rcases Block.runOpen_toLocals_exists program hRun with
                            ⟨restFuel, hRestLower⟩
                          have hStmtLowerRegular :
                              Locals.Direct.Block.runOpen program.toLocals ctx
                                stmtFuel { stmts := Stmt.toLocals returns stmt }
                                state =
                                .ok (Structured.Outcome.regular
                                  stmtOutcome.state, stmtCtx) := by
                            have hEq :
                                stmtOutcome =
                                  Structured.Outcome.regular stmtOutcome.state :=
                              Outcome.eq_regular_of_mode hMode
                            rw [hEq] at hStmtLower
                            exact hStmtLower
                          simpa [Block.toLocals, StmtList.toLocals] using
                            Locals.Direct.Block.runOpen_append_regular_exists
                              program.toLocals
                              (Stmt.toLocals returns stmt)
                              (StmtList.toLocals returns rest)
                              ctx stmtCtx state stmtOutcome.state outcome runCtx
                              ⟨stmtFuel, hStmtLowerRegular⟩
                              ⟨restFuel, hRestLower⟩
                      | brk =>
                          have hPair :
                              (stmtOutcome, ctx) = (outcome, runCtx) := by
                            simpa [Block.runOpen, hStmt, hMode] using hRun
                          injection hPair with hOutcome hCtx
                          rw [← hOutcome, ← hCtx]
                          have hNonregular : stmtOutcome.mode ≠ .regular := by
                            simp [hMode]
                          have hStmtCtx : stmtCtx = ctx :=
                            Stmt.run_nonregular_ctx program hStmt hNonregular
                          simpa [Block.toLocals, StmtList.toLocals] using
                            Locals.Direct.Block.runOpen_append_nonregular_exists
                              program.toLocals
                              (Stmt.toLocals returns stmt)
                              (StmtList.toLocals returns rest)
                              ctx state stmtOutcome ctx
                              ⟨stmtFuel, by simpa [hStmtCtx] using hStmtLower⟩
                              hNonregular
                      | cont =>
                          have hPair :
                              (stmtOutcome, ctx) = (outcome, runCtx) := by
                            simpa [Block.runOpen, hStmt, hMode] using hRun
                          injection hPair with hOutcome hCtx
                          rw [← hOutcome, ← hCtx]
                          have hNonregular : stmtOutcome.mode ≠ .regular := by
                            simp [hMode]
                          have hStmtCtx : stmtCtx = ctx :=
                            Stmt.run_nonregular_ctx program hStmt hNonregular
                          simpa [Block.toLocals, StmtList.toLocals] using
                            Locals.Direct.Block.runOpen_append_nonregular_exists
                              program.toLocals
                              (Stmt.toLocals returns stmt)
                              (StmtList.toLocals returns rest)
                              ctx state stmtOutcome ctx
                              ⟨stmtFuel, by simpa [hStmtCtx] using hStmtLower⟩
                              hNonregular
                      | leave =>
                          have hPair :
                              (stmtOutcome, ctx) = (outcome, runCtx) := by
                            simpa [Block.runOpen, hStmt, hMode] using hRun
                          injection hPair with hOutcome hCtx
                          rw [← hOutcome, ← hCtx]
                          have hNonregular : stmtOutcome.mode ≠ .regular := by
                            simp [hMode]
                          have hStmtCtx : stmtCtx = ctx :=
                            Stmt.run_nonregular_ctx program hStmt hNonregular
                          simpa [Block.toLocals, StmtList.toLocals] using
                            Locals.Direct.Block.runOpen_append_nonregular_exists
                              program.toLocals
                              (Stmt.toLocals returns stmt)
                              (StmtList.toLocals returns rest)
                              ctx state stmtOutcome ctx
                              ⟨stmtFuel, by simpa [hStmtCtx] using hStmtLower⟩
                              hNonregular
                      | halt kind =>
                          have hPair :
                              (stmtOutcome, ctx) = (outcome, runCtx) := by
                            simpa [Block.runOpen, hStmt, hMode] using hRun
                          injection hPair with hOutcome hCtx
                          rw [← hOutcome, ← hCtx]
                          have hNonregular : stmtOutcome.mode ≠ .regular := by
                            simp [hMode]
                          have hStmtCtx : stmtCtx = ctx :=
                            Stmt.run_nonregular_ctx program hStmt hNonregular
                          simpa [Block.toLocals, StmtList.toLocals] using
                            Locals.Direct.Block.runOpen_append_nonregular_exists
                              program.toLocals
                              (Stmt.toLocals returns stmt)
                              (StmtList.toLocals returns rest)
                              ctx state stmtOutcome ctx
                              ⟨stmtFuel, by simpa [hStmtCtx] using hStmtLower⟩
                              hNonregular
  termination_by
    returns _ctx fuel block _state _outcome _runCtx _hRun =>
      (fuel, 0, sizeOf block)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  theorem Block.runScoped_toLocals_exists (program : Program) :
      ∀ {returns : List Name} {ctx : Ctx} {fuel : Nat}
        {block : Block} {state : RunState} {outcome : Outcome},
        Block.runScoped program returns ctx block fuel state = .ok outcome →
        ∃ lowerFuel,
          Locals.Direct.Block.runScoped program.toLocals ctx
            (Block.toLocals returns block) lowerFuel state = .ok outcome := by
    intro returns ctx fuel block state outcome hRun
    unfold Block.runScoped at hRun
    unfold Locals.Direct.Block.runScoped
    cases hOpen : Block.runOpen program returns ctx fuel block state with
    | error err =>
        simp [hOpen] at hRun
    | ok openResult =>
        rcases openResult with ⟨openOutcome, finalCtx⟩
        rcases Block.runOpen_toLocals_exists program hOpen with
          ⟨lowerFuel, hOpenLower⟩
        refine ⟨lowerFuel, ?_⟩
        cases hMode : openOutcome.mode with
        | regular =>
            simp [hOpen, hOpenLower, hMode] at hRun ⊢
            exact hRun
        | brk =>
            simp [hOpen, hOpenLower, hMode] at hRun ⊢
            exact hRun
        | cont =>
            simp [hOpen, hOpenLower, hMode] at hRun ⊢
            exact hRun
        | leave =>
            simp [hOpen, hOpenLower, hMode] at hRun ⊢
            exact hRun
        | halt kind =>
            simp [hOpen, hOpenLower, hMode] at hRun ⊢
            exact hRun
  termination_by
    returns _ctx fuel block _state _outcome _hRun =>
      (fuel, 1, sizeOf block)
  decreasing_by
    all_goals simp_wf
    all_goals
      first
      | omega
      | exact Prod.Lex.right _
          (Prod.Lex.left _ _ (by omega))

  theorem FunDef.runBody_toLocals_open_exists (program : Program) :
      ∀ {fn : FunDef} {fuel : Nat} {state : RunState} {outcome : Outcome},
        FunDef.runBody program fn fuel state = .ok outcome →
        ∃ lowerFuel lowerOutcome lowerCtx,
          Locals.Direct.Block.runOpen program.toLocals
            (Locals.Ctx.procEntryWithLayoutAndRetc
              fn.params.reverse fn.returns.length)
            lowerFuel fn.toLocalsProc.body state =
              .ok (lowerOutcome, lowerCtx) ∧
          FunDef.lowerBodyResult fn.returns.length lowerCtx lowerOutcome =
            .ok outcome := by
    intro fn fuel state outcome hRun
    cases fuel with
    | zero =>
        simp [FunDef.runBody, Structured.invalid] at hRun
    | succ fuel =>
        unfold FunDef.runBody at hRun
        let entryCtx :=
          Locals.Ctx.procEntryWithLayoutAndRetc
            fn.params.reverse fn.returns.length
        cases hInit : initReturns fn.returns entryCtx state with
        | error err =>
            simp [entryCtx, hInit] at hRun
        | ok initResult =>
            rcases initResult with ⟨stateAfterInit, initCtx⟩
            rcases Lower.initReturns_runOpen_exists program hInit with
              ⟨initFuel, hInitLower⟩
            cases hBody :
                Block.runOpen program fn.returns initCtx fuel fn.body
                  stateAfterInit with
            | error err =>
                simp [entryCtx, hInit, hBody] at hRun
            | ok bodyResult =>
                rcases bodyResult with ⟨bodyOutcome, bodyCtx⟩
                rcases Block.runOpen_toLocals_exists program hBody with
                  ⟨bodyFuel, hBodyLower⟩
                cases hMode : bodyOutcome.mode with
                | regular =>
                    simp [entryCtx, hInit, hBody, hMode] at hRun
                    have hBodyLowerRegular :
                        Locals.Direct.Block.runOpen program.toLocals initCtx
                          bodyFuel
                          { stmts :=
                              StmtList.toLocals fn.returns fn.body.stmts }
                          stateAfterInit =
                          .ok (Structured.Outcome.regular bodyOutcome.state,
                            bodyCtx) := by
                      have hEq :
                          bodyOutcome =
                            Structured.Outcome.regular bodyOutcome.state :=
                        Outcome.eq_regular_of_mode hMode
                      rw [hEq] at hBodyLower
                      simpa [Block.toLocals_eq_stmts] using hBodyLower
                    cases hPush :
                        pushReturns bodyCtx fn.returns bodyOutcome.state with
                    | error err =>
                        simp [hPush] at hRun
                    | ok stateAfterReturns =>
                        rcases Lower.pushReturns_runOpen_exists program
                            bodyCtx hPush with
                          ⟨pushFuel, hPushLower⟩
                        cases hCleanup :
                            Locals.Direct.Ctx.runCleanupToPreserving bodyCtx
                              fn.returns.length 0 stateAfterReturns with
                        | error err =>
                            simp [entryCtx, hPush, hCleanup] at hRun
                        | ok stateAfterCleanup =>
                            simp [entryCtx, hPush, hCleanup] at hRun
                            cases hRun
                            rcases
                              Locals.Direct.Block.runOpen_append_regular_exists
                                program.toLocals
                                (Lower.initReturns fn.returns)
                                (StmtList.toLocals fn.returns fn.body.stmts)
                                entryCtx initCtx state stateAfterInit
                                (Structured.Outcome.regular bodyOutcome.state)
                                bodyCtx
                                ⟨initFuel, by
                                  simpa [entryCtx] using hInitLower⟩
                                ⟨bodyFuel, hBodyLowerRegular⟩ with
                              ⟨initBodyFuel, hInitBodyLower⟩
                            rcases
                              Locals.Direct.Block.runOpen_append_regular_exists
                                program.toLocals
                                (Lower.initReturns fn.returns ++
                                  StmtList.toLocals fn.returns fn.body.stmts)
                                (Lower.pushReturns fn.returns)
                                entryCtx bodyCtx state bodyOutcome.state
                                (Structured.Outcome.regular stateAfterReturns)
                                bodyCtx
                                ⟨initBodyFuel, by
                                  simpa [List.append_assoc] using
                                    hInitBodyLower⟩
                                ⟨pushFuel, hPushLower⟩ with
                              ⟨openFuel, hOpenLower⟩
                            refine ⟨openFuel, Structured.Outcome.regular
                              stateAfterReturns, bodyCtx, ?_, ?_⟩
                            have hOpenLower' :
                                Locals.Direct.Block.runOpen program.toLocals
                                  entryCtx openFuel
                                  {
                                    stmts :=
                                      Lower.initReturns fn.returns ++
                                        (StmtList.toLocals fn.returns
                                          fn.body.stmts ++
                                          Lower.pushReturns fn.returns) }
                                  state =
                                  .ok (Structured.Outcome.regular
                                    stateAfterReturns, bodyCtx) := by
                              simpa [List.append_assoc] using hOpenLower
                            · simpa [FunDef.toLocalsProc, entryCtx,
                                List.append_assoc] using hOpenLower'
                            · simpa [FunDef.lowerBodyResult, hCleanup,
                                Structured.Outcome.regular] using hRun
                | brk =>
                    simp [entryCtx, hInit, hBody, hMode,
                      Structured.invalid] at hRun
                | cont =>
                    simp [entryCtx, hInit, hBody, hMode,
                      Structured.invalid] at hRun
                | leave =>
                    have hBodyMode : bodyOutcome.mode ≠ .regular := by
                      simp [hMode]
                    have hDirect : bodyOutcome = outcome := by
                      simpa [entryCtx, hInit, hBody, hMode] using hRun
                    have hOutcomeMode : outcome.mode = .leave := by
                      rw [← hDirect]
                      exact hMode
                    rcases
                      Locals.Direct.Block.runOpen_append_nonregular_exists
                        program.toLocals
                        (StmtList.toLocals fn.returns fn.body.stmts)
                        (Lower.pushReturns fn.returns)
                        initCtx stateAfterInit bodyOutcome bodyCtx
                        ⟨bodyFuel, by
                          simpa [Block.toLocals_eq_stmts] using hBodyLower⟩
                        hBodyMode with
                    ⟨bodyPushFuel, hBodyPushLower⟩
                    rcases
                      Locals.Direct.Block.runOpen_append_regular_exists
                        program.toLocals
                        (Lower.initReturns fn.returns)
                        (StmtList.toLocals fn.returns fn.body.stmts ++
                          Lower.pushReturns fn.returns)
                        entryCtx initCtx state stateAfterInit bodyOutcome
                        bodyCtx
                        ⟨initFuel, by
                          simpa [entryCtx] using hInitLower⟩
                        ⟨bodyPushFuel, hBodyPushLower⟩ with
                    ⟨openFuel, hOpenLower⟩
                    refine ⟨openFuel, bodyOutcome, bodyCtx, ?_, ?_⟩
                    · simpa [FunDef.toLocalsProc, entryCtx,
                        List.append_assoc] using hOpenLower
                    · simp [FunDef.lowerBodyResult, hOutcomeMode, hDirect]
                | halt kind =>
                    have hBodyMode : bodyOutcome.mode ≠ .regular := by
                      simp [hMode]
                    have hDirect : bodyOutcome = outcome := by
                      simpa [entryCtx, hInit, hBody, hMode] using hRun
                    have hOutcomeMode : outcome.mode = .halt kind := by
                      rw [← hDirect]
                      exact hMode
                    rcases
                      Locals.Direct.Block.runOpen_append_nonregular_exists
                        program.toLocals
                        (StmtList.toLocals fn.returns fn.body.stmts)
                        (Lower.pushReturns fn.returns)
                        initCtx stateAfterInit bodyOutcome bodyCtx
                        ⟨bodyFuel, by
                          simpa [Block.toLocals_eq_stmts] using hBodyLower⟩
                        hBodyMode with
                    ⟨bodyPushFuel, hBodyPushLower⟩
                    rcases
                      Locals.Direct.Block.runOpen_append_regular_exists
                        program.toLocals
                        (Lower.initReturns fn.returns)
                        (StmtList.toLocals fn.returns fn.body.stmts ++
                          Lower.pushReturns fn.returns)
                        entryCtx initCtx state stateAfterInit bodyOutcome
                        bodyCtx
                        ⟨initFuel, by
                          simpa [entryCtx] using hInitLower⟩
                        ⟨bodyPushFuel, hBodyPushLower⟩ with
                    ⟨openFuel, hOpenLower⟩
                    refine ⟨openFuel, bodyOutcome, bodyCtx, ?_, ?_⟩
                    · simpa [FunDef.toLocalsProc, entryCtx,
                        List.append_assoc] using hOpenLower
                    · simp [FunDef.lowerBodyResult, hOutcomeMode, hDirect]
  termination_by
    fn fuel _state _outcome _hRun => (fuel, 2, sizeOf fn.body)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  theorem Stmt.runForLoop_toLocals_exists (program : Program) :
      ∀ {returns : List Name} {loopCtx : Ctx} {cond : Expr 1}
        {postBase : Ctx} {post : Block} {bodyBase : Ctx} {body : Block}
        {fuel : Nat} {state : RunState} {outcome : Outcome},
        Stmt.runForLoop program returns loopCtx cond postBase post bodyBase body
          fuel state = .ok outcome →
        ∃ lowerFuel,
          Locals.Direct.Stmt.runForLoop program.toLocals loopCtx cond
            postBase (Block.toLocals returns post)
            bodyBase (Block.toLocals returns body) lowerFuel state =
            .ok outcome := by
    intro returns loopCtx cond postBase post bodyBase body fuel state outcome
      hRun
    cases fuel with
    | zero =>
        simp [Stmt.runForLoop, Structured.invalid] at hRun
    | succ fuel =>
        unfold Stmt.runForLoop at hRun
        unfold Locals.Direct.Stmt.runForLoop
        cases hCond : Locals.Direct.Expr.runCondition loopCtx cond state with
        | error err =>
            simp [hCond] at hRun
        | ok condResult =>
            rcases condResult with ⟨stateAfterCond, condTrue⟩
            cases condTrue with
            | false =>
                simp [hCond] at hRun
                cases hRun
                exact ⟨1, by simp [hCond, Structured.Outcome.regular]⟩
            | true =>
                simp [hCond] at hRun
                cases hBody :
                    Block.runScoped program returns bodyBase body fuel
                      stateAfterCond with
                | error err =>
                    simp [hBody] at hRun
                | ok bodyOutcome =>
                    rcases Block.runScoped_toLocals_exists program hBody with
                      ⟨bodyFuel, hBodyLower⟩
                    cases hBodyMode : bodyOutcome.mode with
                    | brk =>
                        simp [hBody, hBodyMode] at hRun
                        cases hRun
                        refine ⟨bodyFuel + 1, ?_⟩
                        simp [hCond, hBodyLower, hBodyMode,
                          Structured.Outcome.regular]
                    | regular =>
                        simp [hBody, hBodyMode] at hRun
                        cases hPost :
                            Block.runScoped program returns postBase post fuel
                              bodyOutcome.state with
                        | error err =>
                            simp [hPost] at hRun
                        | ok postOutcome =>
                            rcases Block.runScoped_toLocals_exists program
                              hPost with ⟨postFuel, hPostLower⟩
                            cases hPostMode : postOutcome.mode with
                            | regular =>
                                simp [hPost, hPostMode] at hRun
                                rcases Stmt.runForLoop_toLocals_exists program
                                  hRun with ⟨loopFuel, hLoopLower⟩
                                let innerFuel := Nat.max bodyFuel
                                  (Nat.max postFuel loopFuel)
                                refine ⟨innerFuel + 1, ?_⟩
                                simp [hCond]
                                have hBodyLower' :
                                    Locals.Direct.Block.runScoped
                                      program.toLocals bodyBase
                                      (Block.toLocals returns body)
                                      innerFuel stateAfterCond =
                                      .ok bodyOutcome :=
                                  Locals.Direct.Block.runScoped_mono
                                    program.toLocals (by
                                      dsimp [innerFuel]
                                      exact Nat.le_max_left _ _) hBodyLower
                                have hPostLower' :
                                    Locals.Direct.Block.runScoped
                                      program.toLocals postBase
                                      (Block.toLocals returns post)
                                      innerFuel bodyOutcome.state =
                                      .ok postOutcome :=
                                  Locals.Direct.Block.runScoped_mono
                                    program.toLocals (by
                                      dsimp [innerFuel]
                                      exact Nat.le_trans
                                        (Nat.le_max_left _ _)
                                        (Nat.le_max_right _ _)) hPostLower
                                have hLoopLower' :
                                    Locals.Direct.Stmt.runForLoop
                                      program.toLocals loopCtx cond postBase
                                      (Block.toLocals returns post) bodyBase
                                      (Block.toLocals returns body) innerFuel
                                      postOutcome.state = .ok outcome :=
                                  Locals.Direct.Stmt.runForLoop_mono
                                    program.toLocals (by
                                      dsimp [innerFuel]
                                      exact Nat.le_trans
                                        (Nat.le_max_right _ _)
                                        (Nat.le_max_right _ _)) hLoopLower
                                simp [hBodyLower', hBodyMode, hPostLower',
                                  hPostMode, hLoopLower']
                            | brk =>
                                simp [hPost, hPostMode, Structured.invalid] at hRun
                            | cont =>
                                simp [hPost, hPostMode, Structured.invalid] at hRun
                            | leave =>
                                simp [hPost, hPostMode] at hRun
                                let innerFuel := Nat.max bodyFuel postFuel
                                have hBodyLower' :
                                    Locals.Direct.Block.runScoped
                                      program.toLocals bodyBase
                                      (Block.toLocals returns body)
                                      innerFuel stateAfterCond =
                                      .ok bodyOutcome :=
                                  Locals.Direct.Block.runScoped_mono
                                    program.toLocals (by
                                      dsimp [innerFuel]
                                      exact Nat.le_max_left _ _) hBodyLower
                                have hPostLower' :
                                    Locals.Direct.Block.runScoped
                                      program.toLocals postBase
                                      (Block.toLocals returns post)
                                      innerFuel bodyOutcome.state =
                                      .ok postOutcome :=
                                  Locals.Direct.Block.runScoped_mono
                                    program.toLocals (by
                                      dsimp [innerFuel]
                                      exact Nat.le_max_right _ _) hPostLower
                                refine ⟨innerFuel + 1, ?_⟩
                                simpa [hCond, hBodyLower', hBodyMode,
                                  hPostLower', hPostMode] using hRun
                            | halt kind =>
                                simp [hPost, hPostMode] at hRun
                                let innerFuel := Nat.max bodyFuel postFuel
                                have hBodyLower' :
                                    Locals.Direct.Block.runScoped
                                      program.toLocals bodyBase
                                      (Block.toLocals returns body)
                                      innerFuel stateAfterCond =
                                      .ok bodyOutcome :=
                                  Locals.Direct.Block.runScoped_mono
                                    program.toLocals (by
                                      dsimp [innerFuel]
                                      exact Nat.le_max_left _ _) hBodyLower
                                have hPostLower' :
                                    Locals.Direct.Block.runScoped
                                      program.toLocals postBase
                                      (Block.toLocals returns post)
                                      innerFuel bodyOutcome.state =
                                      .ok postOutcome :=
                                  Locals.Direct.Block.runScoped_mono
                                    program.toLocals (by
                                      dsimp [innerFuel]
                                      exact Nat.le_max_right _ _) hPostLower
                                refine ⟨innerFuel + 1, ?_⟩
                                simpa [hCond, hBodyLower', hBodyMode,
                                  hPostLower', hPostMode] using hRun
                    | cont =>
                        simp [hBody, hBodyMode] at hRun
                        cases hPost :
                            Block.runScoped program returns postBase post fuel
                              bodyOutcome.state with
                        | error err =>
                            simp [hPost] at hRun
                        | ok postOutcome =>
                            rcases Block.runScoped_toLocals_exists program
                              hPost with ⟨postFuel, hPostLower⟩
                            cases hPostMode : postOutcome.mode with
                            | regular =>
                                simp [hPost, hPostMode] at hRun
                                rcases Stmt.runForLoop_toLocals_exists program
                                  hRun with ⟨loopFuel, hLoopLower⟩
                                let innerFuel := Nat.max bodyFuel
                                  (Nat.max postFuel loopFuel)
                                refine ⟨innerFuel + 1, ?_⟩
                                simp [hCond]
                                have hBodyLower' :
                                    Locals.Direct.Block.runScoped
                                      program.toLocals bodyBase
                                      (Block.toLocals returns body)
                                      innerFuel stateAfterCond =
                                      .ok bodyOutcome :=
                                  Locals.Direct.Block.runScoped_mono
                                    program.toLocals (by
                                      dsimp [innerFuel]
                                      exact Nat.le_max_left _ _) hBodyLower
                                have hPostLower' :
                                    Locals.Direct.Block.runScoped
                                      program.toLocals postBase
                                      (Block.toLocals returns post)
                                      innerFuel bodyOutcome.state =
                                      .ok postOutcome :=
                                  Locals.Direct.Block.runScoped_mono
                                    program.toLocals (by
                                      dsimp [innerFuel]
                                      exact Nat.le_trans
                                        (Nat.le_max_left _ _)
                                        (Nat.le_max_right _ _)) hPostLower
                                have hLoopLower' :
                                    Locals.Direct.Stmt.runForLoop
                                      program.toLocals loopCtx cond postBase
                                      (Block.toLocals returns post) bodyBase
                                      (Block.toLocals returns body) innerFuel
                                      postOutcome.state = .ok outcome :=
                                  Locals.Direct.Stmt.runForLoop_mono
                                    program.toLocals (by
                                      dsimp [innerFuel]
                                      exact Nat.le_trans
                                        (Nat.le_max_right _ _)
                                        (Nat.le_max_right _ _)) hLoopLower
                                simp [hBodyLower', hBodyMode, hPostLower',
                                  hPostMode, hLoopLower']
                            | brk =>
                                simp [hPost, hPostMode, Structured.invalid] at hRun
                            | cont =>
                                simp [hPost, hPostMode, Structured.invalid] at hRun
                            | leave =>
                                simp [hPost, hPostMode] at hRun
                                let innerFuel := Nat.max bodyFuel postFuel
                                have hBodyLower' :
                                    Locals.Direct.Block.runScoped
                                      program.toLocals bodyBase
                                      (Block.toLocals returns body)
                                      innerFuel stateAfterCond =
                                      .ok bodyOutcome :=
                                  Locals.Direct.Block.runScoped_mono
                                    program.toLocals (by
                                      dsimp [innerFuel]
                                      exact Nat.le_max_left _ _) hBodyLower
                                have hPostLower' :
                                    Locals.Direct.Block.runScoped
                                      program.toLocals postBase
                                      (Block.toLocals returns post)
                                      innerFuel bodyOutcome.state =
                                      .ok postOutcome :=
                                  Locals.Direct.Block.runScoped_mono
                                    program.toLocals (by
                                      dsimp [innerFuel]
                                      exact Nat.le_max_right _ _) hPostLower
                                refine ⟨innerFuel + 1, ?_⟩
                                simpa [hCond, hBodyLower', hBodyMode,
                                  hPostLower', hPostMode] using hRun
                            | halt kind =>
                                simp [hPost, hPostMode] at hRun
                                let innerFuel := Nat.max bodyFuel postFuel
                                have hBodyLower' :
                                    Locals.Direct.Block.runScoped
                                      program.toLocals bodyBase
                                      (Block.toLocals returns body)
                                      innerFuel stateAfterCond =
                                      .ok bodyOutcome :=
                                  Locals.Direct.Block.runScoped_mono
                                    program.toLocals (by
                                      dsimp [innerFuel]
                                      exact Nat.le_max_left _ _) hBodyLower
                                have hPostLower' :
                                    Locals.Direct.Block.runScoped
                                      program.toLocals postBase
                                      (Block.toLocals returns post)
                                      innerFuel bodyOutcome.state =
                                      .ok postOutcome :=
                                  Locals.Direct.Block.runScoped_mono
                                    program.toLocals (by
                                      dsimp [innerFuel]
                                      exact Nat.le_max_right _ _) hPostLower
                                refine ⟨innerFuel + 1, ?_⟩
                                simpa [hCond, hBodyLower', hBodyMode,
                                  hPostLower', hPostMode] using hRun
                    | leave =>
                        simp [hBody, hBodyMode] at hRun
                        refine ⟨bodyFuel + 1, ?_⟩
                        simpa [hCond, hBodyLower, hBodyMode] using hRun
                    | halt kind =>
                        simp [hBody, hBodyMode] at hRun
                        refine ⟨bodyFuel + 1, ?_⟩
                        simpa [hCond, hBodyLower, hBodyMode] using hRun
  termination_by
    returns _loopCtx _cond _postBase _post _bodyBase _body fuel _state
        _outcome _hRun =>
      (fuel, 3, 0)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  theorem Stmt.run_toLocals_exists (program : Program) :
      ∀ {returns : List Name} {ctx : Ctx} {fuel : Nat} {stmt : Stmt}
        {state : RunState} {outcome : Outcome} {runCtx : Ctx},
        Stmt.run program returns ctx fuel stmt state = .ok (outcome, runCtx) →
        ∃ lowerFuel,
          Locals.Direct.Block.runOpen program.toLocals ctx lowerFuel
            { stmts := Stmt.toLocals returns stmt } state =
            .ok (outcome, runCtx) := by
    intro returns ctx fuel stmt state outcome runCtx hRun
    cases stmt with
    | expr expr =>
        exact ⟨2, by
          simpa [Stmt.run, Stmt.toLocals, Locals.Direct.Block.runOpen,
            Locals.Direct.Stmt.run, Structured.Outcome.regular] using hRun⟩
    | let_ name value =>
        exact ⟨2, by
          simpa [Stmt.run, Stmt.toLocals, Locals.Direct.Block.runOpen,
            Locals.Direct.Stmt.run, Structured.Outcome.regular] using hRun⟩
    | assign name value =>
        unfold Stmt.run at hRun
        unfold Locals.Direct.Expr.runState at hRun
        cases hCode : Locals.Direct.Expr.runCode ctx 0 value state.evm with
        | error err =>
            simp [hCode] at hRun
        | ok evmAfterValue =>
            simp [hCode, Direct.assignTop] at hRun
            cases hDepth : Locals.Layout.lookupDepth? name ctx.layout with
            | none =>
                simp [hDepth, Structured.invalid] at hRun
            | some depth =>
                cases hSwapOp : Locals.StackOp.swap? depth with
                | none =>
                    simp [hDepth, hSwapOp, Structured.invalid] at hRun
                | some swapOp =>
                    cases hSwap : swapOp.step evmAfterValue with
                    | error err =>
                        simp [hDepth, hSwapOp, hSwap] at hRun
                    | ok evmAfterSwap =>
                        cases hPop :
                            Structured.BasicOp.pop.step evmAfterSwap with
                        | error err =>
                            simp [hDepth, hSwapOp, hSwap, hPop] at hRun
                        | ok evmAfterPop =>
                            have hPair :
                                (Structured.Outcome.regular
                                    (state.withEVM evmAfterPop), ctx) =
                                  (outcome, runCtx) := by
                              simpa [hDepth, hSwapOp, hSwap, hPop] using hRun
                            injection hPair with hOutcome hCtx
                            rw [← hOutcome, ← hCtx]
                            exact ⟨2, by
                              simp [Stmt.toLocals, Locals.Direct.Block.runOpen,
                                Locals.Direct.Stmt.run, hCode, hDepth,
                                hSwapOp, hSwap, hPop,
                                Structured.Outcome.regular]⟩
    | block body =>
        unfold Stmt.run at hRun
        cases hBody : Block.runScoped program returns ctx body fuel state with
        | error err =>
            simp [hBody] at hRun
        | ok bodyOutcome =>
            rcases Block.runScoped_toLocals_exists program hBody with
              ⟨bodyFuel, hBodyLower⟩
            have hPair : (bodyOutcome, ctx) = (outcome, runCtx) := by
              simpa [hBody] using hRun
            injection hPair with hOutcome hCtx
            rw [← hOutcome, ← hCtx]
            exact ⟨bodyFuel + 2, by
              simp [Stmt.toLocals, Locals.Direct.Block.runOpen,
                Locals.Direct.Stmt.run]
              have hBodyLower' :
                  Locals.Direct.Block.runScoped program.toLocals ctx
                    (Block.toLocals returns body) (bodyFuel + 1) state =
                    .ok bodyOutcome :=
                Locals.Direct.Block.runScoped_mono program.toLocals
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
            simp [Stmt.run, Structured.invalid] at hRun
        | succ fuel =>
            unfold Stmt.run at hRun
            cases hCond : Locals.Direct.Expr.runCondition ctx cond state with
            | error err =>
                simp [hCond] at hRun
            | ok condResult =>
                rcases condResult with ⟨stateAfterCond, condTrue⟩
                cases condTrue with
                | false =>
                    have hPair :
                        (Structured.Outcome.regular stateAfterCond, ctx) =
                          (outcome, runCtx) := by
                      simpa [hCond] using hRun
                    injection hPair with hOutcome hCtx
                    rw [← hOutcome, ← hCtx]
                    exact ⟨2, by
                      simp [Stmt.toLocals, Locals.Direct.Block.runOpen,
                        Locals.Direct.Stmt.run, hCond,
                        Structured.Outcome.regular]⟩
                | true =>
                    simp [hCond] at hRun
                    cases hBody :
                        Block.runScoped program returns ctx body fuel
                          stateAfterCond with
                    | error err =>
                        simp [hBody] at hRun
                    | ok bodyOutcome =>
                        rcases Block.runScoped_toLocals_exists program
                          hBody with ⟨bodyFuel, hBodyLower⟩
                        have hPair :
                            (bodyOutcome, ctx) = (outcome, runCtx) := by
                          simpa [hCond, hBody] using hRun
                        injection hPair with hOutcome hCtx
                        rw [← hOutcome, ← hCtx]
                        refine ⟨bodyFuel + 2, ?_⟩
                        simp [Stmt.toLocals, Locals.Direct.Block.runOpen,
                          Locals.Direct.Stmt.run, hCond]
                        have hBodyLower' :
                            Locals.Direct.Block.runScoped program.toLocals ctx
                              (Block.toLocals returns body) bodyFuel
                              stateAfterCond = .ok bodyOutcome := hBodyLower
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
            simp [Stmt.run, Structured.invalid] at hRun
        | succ fuel =>
            unfold Stmt.run at hRun
            cases hScrutinee :
                Locals.Direct.Expr.runState ctx scrutinee state with
            | error err =>
                simp [hScrutinee] at hRun
            | ok stateAfterScrutinee =>
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
                        have hPair :
                            (Structured.Outcome.regular stateAfterPop, ctx) =
                              (outcome, runCtx) := by
                          simpa [hScrutinee, hPop, hSelected, stateAfterPop]
                            using hRun
                        injection hPair with hOutcome hCtx
                        rw [← hOutcome, ← hCtx]
                        exact ⟨2, by
                          simp [Stmt.toLocals, Locals.Direct.Block.runOpen,
                            Locals.Direct.Stmt.run, hScrutinee, hPop,
                            Switch.select_toLocals, hSelected, stateAfterPop,
                            Structured.Outcome.regular]⟩
                    | some selected =>
                        simp [hScrutinee, hPop, hSelected, stateAfterPop] at hRun
                        cases hBody :
                            Block.runScoped program returns ctx selected fuel
                              stateAfterPop with
                        | error err =>
                            have hBody' :
                                Block.runScoped program returns ctx selected fuel
                                  (stateAfterScrutinee.withEVM
                                    { stateAfterScrutinee.evm with
                                      stack := stack }) = .error err := by
                              simpa [stateAfterPop] using hBody
                            simp [hBody'] at hRun
                        | ok bodyOutcome =>
                            have hBody' :
                                Block.runScoped program returns ctx selected fuel
                                  (stateAfterScrutinee.withEVM
                                    { stateAfterScrutinee.evm with
                                      stack := stack }) = .ok bodyOutcome := by
                              simpa [stateAfterPop] using hBody
                            rcases Block.runScoped_toLocals_exists program
                              hBody with ⟨bodyFuel, hBodyLower⟩
                            have hPair :
                                (bodyOutcome, ctx) = (outcome, runCtx) := by
                              simpa [hBody'] using hRun
                            injection hPair with hOutcome hCtx
                            rw [← hOutcome, ← hCtx]
                            refine ⟨bodyFuel + 2, ?_⟩
                            simp [Stmt.toLocals, Locals.Direct.Block.runOpen,
                              Locals.Direct.Stmt.run, hScrutinee, hPop,
                              Switch.select_toLocals, hSelected]
                            have hBodyLower' :
                                Locals.Direct.Block.runScoped program.toLocals
                                  ctx (Block.toLocals returns selected)
                                  bodyFuel stateAfterPop = .ok bodyOutcome :=
                              hBodyLower
                            have hBodyLowerExplicit :
                                Locals.Direct.Block.runScoped program.toLocals
                                  ctx (Block.toLocals returns selected)
                                  bodyFuel
                                  (stateAfterScrutinee.withEVM
                                    { stateAfterScrutinee.evm with
                                      stack := stack }) = .ok bodyOutcome := by
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
            simp [Stmt.run, Structured.invalid] at hRun
        | succ fuel =>
            unfold Stmt.run at hRun
            let initBase := ctx.withoutLoopControl
            cases hInit :
                Block.runOpen program returns initBase fuel init state with
            | error err =>
                simp [initBase, hInit] at hRun
            | ok initResult =>
                rcases initResult with ⟨initOutcome, initCtx⟩
                rcases Block.runOpen_toLocals_exists program hInit with
                  ⟨initFuel, hInitLower⟩
                cases hInitMode : initOutcome.mode with
                | regular =>
                    simp [initBase, hInit, hInitMode] at hRun
                    have hInitLowerRegular :
                        Locals.Direct.Block.runOpen program.toLocals initBase
                          initFuel (Block.toLocals returns init) state =
                          .ok (Structured.Outcome.regular initOutcome.state,
                            initCtx) := by
                      have hEq :
                          initOutcome =
                            Structured.Outcome.regular initOutcome.state :=
                        Outcome.eq_regular_of_mode hInitMode
                      rw [hEq] at hInitLower
                      exact hInitLower
                    let postBase := initCtx.withoutLoopControl
                    let bodyBase := initCtx.withLoopControl initCtx.layout.length
                    cases hLoop :
                        Stmt.runForLoop program returns initCtx cond postBase post
                          bodyBase body fuel initOutcome.state with
                    | error err =>
                        simp [postBase, bodyBase, hLoop] at hRun
                    | ok loopOutcome =>
                        rcases Stmt.runForLoop_toLocals_exists program
                          hLoop with ⟨loopFuel, hLoopLower⟩
                        cases hLoopMode : loopOutcome.mode with
                        | regular =>
                            simp [postBase, bodyBase, hLoop, hLoopMode] at hRun
                            cases hCleanup :
                                Locals.Direct.Ctx.runCleanupTo initCtx
                                  ctx.layout.length loopOutcome.state with
                            | error err =>
                                simp [hCleanup] at hRun
                            | ok stateAfterCleanup =>
                                have hPair :
                                    (Structured.Outcome.regular
                                      stateAfterCleanup, ctx) =
                                      (outcome, runCtx) := by
                                  simpa [hCleanup] using hRun
                                let innerFuel := Nat.max initFuel loopFuel
                                refine ⟨innerFuel + 2, ?_⟩
                                simp [Stmt.toLocals, Locals.Direct.Block.runOpen,
                                  Locals.Direct.Stmt.run, initBase]
                                have hInitLower' :
                                    Locals.Direct.Block.runOpen
                                      program.toLocals initBase innerFuel
                                      (Block.toLocals returns init) state =
                                      .ok (Structured.Outcome.regular
                                        initOutcome.state, initCtx) :=
                                  Locals.Direct.Block.runOpen_mono
                                    program.toLocals (by
                                      dsimp [innerFuel]
                                      exact Nat.le_max_left _ _) hInitLowerRegular
                                have hLoopLower' :
                                    Locals.Direct.Stmt.runForLoop
                                      program.toLocals initCtx cond postBase
                                      (Block.toLocals returns post) bodyBase
                                      (Block.toLocals returns body) innerFuel
                                      initOutcome.state = .ok loopOutcome :=
                                  Locals.Direct.Stmt.runForLoop_mono
                                    program.toLocals (by
                                      dsimp [innerFuel]
                                      exact Nat.le_max_right _ _) hLoopLower
                                simpa [hInitLower', hInitMode, initBase, postBase,
                                  bodyBase, hLoopLower', hLoopMode, hCleanup,
                                  Structured.Outcome.regular] using hPair
                        | brk =>
                            simp [postBase, bodyBase, hLoop, hLoopMode,
                              Structured.invalid] at hRun
                        | cont =>
                            simp [postBase, bodyBase, hLoop, hLoopMode,
                              Structured.invalid] at hRun
                        | leave =>
                            simp [postBase, bodyBase, hLoop, hLoopMode] at hRun
                            have hPair :
                                (loopOutcome, ctx) = (outcome, runCtx) := by
                              simpa using hRun
                            let innerFuel := Nat.max initFuel loopFuel
                            refine ⟨innerFuel + 2, ?_⟩
                            simp [Stmt.toLocals, Locals.Direct.Block.runOpen,
                              Locals.Direct.Stmt.run, initBase]
                            have hInitLower' :
                                Locals.Direct.Block.runOpen program.toLocals
                                  initBase innerFuel
                                  (Block.toLocals returns init) state =
                                  .ok (Structured.Outcome.regular
                                    initOutcome.state, initCtx) :=
                              Locals.Direct.Block.runOpen_mono program.toLocals
                                (by
                                  dsimp [innerFuel]
                                  exact Nat.le_max_left _ _) hInitLowerRegular
                            have hLoopLower' :
                                Locals.Direct.Stmt.runForLoop program.toLocals
                                  initCtx cond postBase
                                  (Block.toLocals returns post) bodyBase
                                  (Block.toLocals returns body) innerFuel
                                  initOutcome.state = .ok loopOutcome :=
                              Locals.Direct.Stmt.runForLoop_mono
                                program.toLocals (by
                                  dsimp [innerFuel]
                                  exact Nat.le_max_right _ _) hLoopLower
                            simpa [hInitLower', hInitMode, initBase, postBase,
                              bodyBase, hLoopLower', hLoopMode] using hPair
                        | halt kind =>
                            simp [postBase, bodyBase, hLoop, hLoopMode] at hRun
                            have hPair :
                                (loopOutcome, ctx) = (outcome, runCtx) := by
                              simpa using hRun
                            let innerFuel := Nat.max initFuel loopFuel
                            refine ⟨innerFuel + 2, ?_⟩
                            simp [Stmt.toLocals, Locals.Direct.Block.runOpen,
                              Locals.Direct.Stmt.run, initBase]
                            have hInitLower' :
                                Locals.Direct.Block.runOpen program.toLocals
                                  initBase innerFuel
                                  (Block.toLocals returns init) state =
                                  .ok (Structured.Outcome.regular
                                    initOutcome.state, initCtx) :=
                              Locals.Direct.Block.runOpen_mono program.toLocals
                                (by
                                  dsimp [innerFuel]
                                  exact Nat.le_max_left _ _) hInitLowerRegular
                            have hLoopLower' :
                                Locals.Direct.Stmt.runForLoop program.toLocals
                                  initCtx cond postBase
                                  (Block.toLocals returns post) bodyBase
                                  (Block.toLocals returns body) innerFuel
                                  initOutcome.state = .ok loopOutcome :=
                              Locals.Direct.Stmt.runForLoop_mono
                                program.toLocals (by
                                  dsimp [innerFuel]
                                  exact Nat.le_max_right _ _) hLoopLower
                            simpa [hInitLower', hInitMode, initBase, postBase,
                              bodyBase, hLoopLower', hLoopMode] using hPair
                | brk =>
                    simp [initBase, hInit, hInitMode, Structured.invalid] at hRun
                | cont =>
                    simp [initBase, hInit, hInitMode, Structured.invalid] at hRun
                | leave =>
                    simp [initBase, hInit, hInitMode] at hRun
                    have hPair : (initOutcome, ctx) = (outcome, runCtx) := by
                      simpa using hRun
                    injection hPair with hOutcome hCtx
                    rw [← hOutcome, ← hCtx]
                    have hNonregular : initOutcome.mode ≠ .regular := by
                      simp [hInitMode]
                    simpa [Stmt.toLocals] using
                      Locals.Direct.Block.runOpen_append_nonregular_exists
                        program.toLocals [Locals.Stmt.for_
                          (Block.toLocals returns init) cond
                          (Block.toLocals returns post)
                          (Block.toLocals returns body)] [] ctx state
                        initOutcome ctx
                        (by
                          refine ⟨initFuel + 2, ?_⟩
                          simp [Locals.Direct.Block.runOpen,
                            Locals.Direct.Stmt.run, initBase]
                          have hInitLower' :
                              Locals.Direct.Block.runOpen program.toLocals
                                initBase initFuel
                                (Block.toLocals returns init) state =
                                .ok (initOutcome, initCtx) :=
                            hInitLower
                          have hInitLower'' :
                              Locals.Direct.Block.runOpen program.toLocals
                                initBase (initFuel + 1)
                                (Block.toLocals returns init) state =
                                .ok (initOutcome, initCtx) :=
                            Locals.Direct.Block.runOpen_mono program.toLocals
                              (Nat.le_succ initFuel) hInitLower'
                          simp [hInitLower', hInitLower'', hInitMode, initBase])
                        hNonregular
                | halt kind =>
                    simp [initBase, hInit, hInitMode] at hRun
                    have hPair : (initOutcome, ctx) = (outcome, runCtx) := by
                      simpa using hRun
                    injection hPair with hOutcome hCtx
                    rw [← hOutcome, ← hCtx]
                    have hNonregular : initOutcome.mode ≠ .regular := by
                      simp [hInitMode]
                    simpa [Stmt.toLocals] using
                      Locals.Direct.Block.runOpen_append_nonregular_exists
                        program.toLocals [Locals.Stmt.for_
                          (Block.toLocals returns init) cond
                          (Block.toLocals returns post)
                          (Block.toLocals returns body)] [] ctx state
                        initOutcome ctx
                        (by
                          refine ⟨initFuel + 2, ?_⟩
                          simp [Locals.Direct.Block.runOpen,
                            Locals.Direct.Stmt.run, initBase]
                          have hInitLower' :
                              Locals.Direct.Block.runOpen program.toLocals
                                initBase initFuel
                                (Block.toLocals returns init) state =
                                .ok (initOutcome, initCtx) :=
                            hInitLower
                          have hInitLower'' :
                              Locals.Direct.Block.runOpen program.toLocals
                                initBase (initFuel + 1)
                                (Block.toLocals returns init) state =
                                .ok (initOutcome, initCtx) :=
                            Locals.Direct.Block.runOpen_mono program.toLocals
                              (Nat.le_succ initFuel) hInitLower'
                          simp [hInitLower', hInitLower'', hInitMode, initBase])
                        hNonregular
    | brk =>
        exact ⟨1, by
          simpa [Stmt.run, Stmt.toLocals, Locals.Direct.Block.runOpen,
            Locals.Direct.Stmt.run] using hRun⟩
    | cont =>
        exact ⟨1, by
          simpa [Stmt.run, Stmt.toLocals, Locals.Direct.Block.runOpen,
            Locals.Direct.Stmt.run] using hRun⟩
    | leave =>
        unfold Stmt.run at hRun
        cases hPush : pushReturns ctx returns state with
        | error err =>
            simp [hPush] at hRun
        | ok stateAfterReturns =>
            rcases Lower.pushReturns_runOpen_exists program ctx hPush with
              ⟨pushFuel, hPushLower⟩
            cases hTarget : ctx.leaveDepth? with
            | none =>
                simp [hPush, hTarget, Structured.invalid] at hRun
            | some target =>
                cases hCleanup :
                    Locals.Direct.Ctx.runCleanupToPreserving ctx
                      ctx.leaveRetc target stateAfterReturns with
                | error err =>
                    simp [hPush, hTarget, hCleanup] at hRun
                | ok stateAfterCleanup =>
                    cases hReturns : stateAfterCleanup.returns with
                    | nil =>
                        simp [hPush, hTarget, hCleanup, hReturns,
                          Structured.invalid] at hRun
                    | cons ret rest =>
                        have hPair :
                            (Structured.Outcome.leave stateAfterCleanup, ctx) =
                              (outcome, runCtx) := by
                          simpa [hPush, hTarget, hCleanup, hReturns] using hRun
                        injection hPair with hOutcome hCtx
                        rw [← hOutcome, ← hCtx]
                        rcases
                          Locals.Direct.Block.runOpen_append_regular_exists
                            program.toLocals
                            (Lower.pushReturns returns)
                            [Locals.Stmt.leave]
                            ctx ctx state stateAfterReturns
                            (Structured.Outcome.leave stateAfterCleanup) ctx
                            ⟨pushFuel, hPushLower⟩
                            ⟨1, by
                              simp [Locals.Direct.Block.runOpen,
                                Locals.Direct.Stmt.run, hTarget, hCleanup,
                                hReturns, Structured.Outcome.leave]⟩ with
                          ⟨lowerFuel, hLower⟩
                        exact ⟨lowerFuel, by
                          simpa [Stmt.toLocals, List.append_assoc] using
                            hLower⟩
    | call targets functionName args =>
        cases fuel with
        | zero =>
            simp [Stmt.run, Structured.invalid] at hRun
        | succ fuel =>
            unfold Stmt.run at hRun
            cases hArgs : evalArgs ctx args state with
            | error err =>
                simp [hArgs] at hRun
            | ok stateAfterArgs =>
                rcases Lower.evalArgs_runOpen_exists program ctx hArgs with
                  ⟨argsFuel, hArgsLower⟩
                cases hLookup : FunList.find? functionName program.functions with
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
                        simp [hArgs, hLookup, hSplit, Structured.invalid] at hRun
                    | some split =>
                        rcases split with ⟨argStack, callerStack⟩
                        let callState :=
                          (stateAfterArgs.withEVM
                            { stateAfterArgs.evm with stack := argStack })
                            |>.pushReturn callerStack fn.returns.length
                        cases hBody : FunDef.runBody program fn fuel callState with
                        | error err =>
                            simp [hArgs, hLookup, hSplit, callState, hBody] at hRun
                        | ok callOutcome =>
                            rcases FunDef.runBody_toLocals_open_exists program
                              hBody with
                              ⟨bodyFuel, lowerBodyOutcome, lowerBodyCtx,
                                hBodyLowerOpen, hBodyRel⟩
                            have hBodyLowerOpen' :
                                Locals.Direct.Block.runOpen program.toLocals
                                  (Locals.Ctx.procEntryWithLayoutAndRetc
                                    fn.params.reverse fn.returns.length)
                                  bodyFuel
                                  {
                                    stmts :=
                                      Lower.initReturns fn.returns ++
                                        (StmtList.toLocals fn.returns
                                          fn.body.stmts ++
                                          Lower.pushReturns fn.returns) }
                                  ((stateAfterArgs.withEVM
                                    { stateAfterArgs.evm with
                                      stack := argStack })
                                    |>.pushReturn callerStack
                                      fn.returns.length) =
                                  .ok (lowerBodyOutcome, lowerBodyCtx) := by
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
                                            assignReturnedTops ctx targets.reverse
                                              stateWithReturns with
                                        | error err =>
                                            simp [hPopRet, hAttach,
                                              stateWithReturns, hAssign] at hRun
                                        | ok stateAfterAssign =>
                                            have hPair :
                                                (Structured.Outcome.regular
                                                    stateAfterAssign, ctx) =
                                                  (outcome, runCtx) := by
                                              simpa [hPopRet, hAttach,
                                                stateWithReturns, hAssign]
                                                using hRun
                                            injection hPair with hOutcome hCtx
                                            rw [← hOutcome, ← hCtx]
                                            rcases Lower.assignReturnedTops_runOpen_exists
                                                program ctx hAssign with
                                              ⟨assignFuel, hAssignLower⟩
                                            let callFuel := bodyFuel + 2
                                            have hCallLower :
                                                Locals.Direct.Block.runOpen
                                                  program.toLocals ctx callFuel
                                                  { stmts := [Locals.Stmt.call
                                                    functionName] } stateAfterArgs =
                                                  .ok (Structured.Outcome.regular
                                                    stateWithReturns, ctx) := by
                                                unfold callFuel
                                                simp [Locals.Direct.Block.runOpen,
                                                  Locals.Direct.Stmt.run,
                                                  hLowerLookup', FunDef.toLocalsProc,
                                                  hSplit, callState]
                                                rw [hBodyLowerOpen']
                                                cases hLowerMode :
                                                    lowerBodyOutcome.mode with
                                                | regular =>
                                                    simp [FunDef.lowerBodyResult,
                                                      hLowerMode] at hBodyRel
                                                    cases hCleanup :
                                                        Locals.Direct.Ctx.runCleanupToPreserving
                                                          lowerBodyCtx
                                                            fn.returns.length 0
                                                          lowerBodyOutcome.state with
                                                    | error err =>
                                                        simp [hCleanup] at hBodyRel
                                                    | ok cleaned =>
                                                        have hEq :
                                                            Structured.Outcome.regular
                                                              cleaned =
                                                              callOutcome := by
                                                          simpa [hCleanup,
                                                            Structured.Outcome.regular]
                                                            using hBodyRel
                                                        cases hEq
                                                        have hPopRetClean :
                                                            cleaned.popReturn? =
                                                              some (frame,
                                                                returned) := by
                                                          simpa
                                                            [Structured.Outcome.regular]
                                                            using hPopRet
                                                        have hAttachClean :
                                                            Structured.StackFrame.attachReturns?
                                                              frame
                                                              cleaned.evm.stack =
                                                                some stack := by
                                                          simpa
                                                            [Structured.Outcome.regular]
                                                            using hAttach
                                                        simp [hLowerMode, hCleanup,
                                                          hPopRetClean,
                                                          hAttachClean,
                                                          stateWithReturns,
                                                          Structured.Outcome.regular]
                                                | brk =>
                                                    simp [FunDef.lowerBodyResult,
                                                      hLowerMode,
                                                      Structured.invalid] at hBodyRel
                                                | cont =>
                                                    simp [FunDef.lowerBodyResult,
                                                      hLowerMode,
                                                      Structured.invalid] at hBodyRel
                                                | leave =>
                                                    simp [FunDef.lowerBodyResult,
                                                      hLowerMode] at hBodyRel
                                                    have hEq :
                                                        lowerBodyOutcome =
                                                          callOutcome := by
                                                      simpa using hBodyRel
                                                    cases hEq
                                                    simp [hLowerMode] at hBodyMode
                                                | halt lowerKind =>
                                                    simp [FunDef.lowerBodyResult,
                                                      hLowerMode] at hBodyRel
                                                    have hEq :
                                                        lowerBodyOutcome =
                                                          callOutcome := by
                                                      simpa using hBodyRel
                                                    cases hEq
                                                    simp [hLowerMode] at hBodyMode
                                            rcases
                                              Locals.Direct.Block.runOpen_append_regular_exists
                                                program.toLocals
                                                (Lower.evalArgs args)
                                                [Locals.Stmt.call functionName]
                                                ctx ctx state stateAfterArgs
                                                (Structured.Outcome.regular
                                                  stateWithReturns) ctx
                                                ⟨argsFuel, hArgsLower⟩
                                                ⟨callFuel, hCallLower⟩ with
                                              ⟨argsCallFuel, hArgsCallLower⟩
                                            rcases
                                              Locals.Direct.Block.runOpen_append_regular_exists
                                                program.toLocals
                                                (Lower.evalArgs args ++
                                                  [Locals.Stmt.call functionName])
                                                (Lower.assignReturnedTops targets)
                                                ctx ctx state stateWithReturns
                                                (Structured.Outcome.regular
                                                  stateAfterAssign) ctx
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
                                            assignReturnedTops ctx targets.reverse
                                              stateWithReturns with
                                        | error err =>
                                            simp [hPopRet, hAttach,
                                              stateWithReturns, hAssign] at hRun
                                        | ok stateAfterAssign =>
                                            have hPair :
                                                (Structured.Outcome.regular
                                                    stateAfterAssign, ctx) =
                                                  (outcome, runCtx) := by
                                              simpa [hPopRet, hAttach,
                                                stateWithReturns, hAssign]
                                                using hRun
                                            injection hPair with hOutcome hCtx
                                            rw [← hOutcome, ← hCtx]
                                            rcases Lower.assignReturnedTops_runOpen_exists
                                                program ctx hAssign with
                                              ⟨assignFuel, hAssignLower⟩
                                            let callFuel := bodyFuel + 2
                                            have hCallLower :
                                                Locals.Direct.Block.runOpen
                                                  program.toLocals ctx callFuel
                                                  { stmts := [Locals.Stmt.call
                                                    functionName] } stateAfterArgs =
                                                  .ok (Structured.Outcome.regular
                                                    stateWithReturns, ctx) := by
                                                unfold callFuel
                                                simp [Locals.Direct.Block.runOpen,
                                                  Locals.Direct.Stmt.run,
                                                  hLowerLookup', FunDef.toLocalsProc,
                                                  hSplit, callState]
                                                rw [hBodyLowerOpen']
                                                cases hLowerMode :
                                                    lowerBodyOutcome.mode with
                                                | regular =>
                                                    simp [FunDef.lowerBodyResult,
                                                      hLowerMode] at hBodyRel
                                                    cases hCleanup :
                                                        Locals.Direct.Ctx.runCleanupToPreserving
                                                          lowerBodyCtx
                                                            fn.returns.length 0
                                                          lowerBodyOutcome.state with
                                                    | error err =>
                                                        simp [hCleanup] at hBodyRel
                                                    | ok cleaned =>
                                                        have hEq :
                                                            Structured.Outcome.regular
                                                              cleaned =
                                                              callOutcome := by
                                                          simpa [hCleanup,
                                                            Structured.Outcome.regular]
                                                            using hBodyRel
                                                        cases hEq
                                                        simp at hBodyMode
                                                | brk =>
                                                    simp [FunDef.lowerBodyResult,
                                                      hLowerMode,
                                                      Structured.invalid] at hBodyRel
                                                | cont =>
                                                    simp [FunDef.lowerBodyResult,
                                                      hLowerMode,
                                                      Structured.invalid] at hBodyRel
                                                | leave =>
                                                    simp [FunDef.lowerBodyResult,
                                                      hLowerMode] at hBodyRel
                                                    have hEq :
                                                        lowerBodyOutcome =
                                                          callOutcome := by
                                                      simpa using hBodyRel
                                                    cases hEq
                                                    simp [hLowerMode, hPopRet,
                                                      hAttach, stateWithReturns,
                                                      Structured.Outcome.regular]
                                                | halt lowerKind =>
                                                    simp [FunDef.lowerBodyResult,
                                                      hLowerMode] at hBodyRel
                                                    have hEq :
                                                        lowerBodyOutcome =
                                                          callOutcome := by
                                                      simpa using hBodyRel
                                                    cases hEq
                                                    simp [hLowerMode] at hBodyMode
                                            rcases
                                              Locals.Direct.Block.runOpen_append_regular_exists
                                                program.toLocals
                                                (Lower.evalArgs args)
                                                [Locals.Stmt.call functionName]
                                                ctx ctx state stateAfterArgs
                                                (Structured.Outcome.regular
                                                  stateWithReturns) ctx
                                                ⟨argsFuel, hArgsLower⟩
                                                ⟨callFuel, hCallLower⟩ with
                                              ⟨argsCallFuel, hArgsCallLower⟩
                                            rcases
                                              Locals.Direct.Block.runOpen_append_regular_exists
                                                program.toLocals
                                                (Lower.evalArgs args ++
                                                  [Locals.Stmt.call functionName])
                                                (Lower.assignReturnedTops targets)
                                                ctx ctx state stateWithReturns
                                                (Structured.Outcome.regular
                                                  stateAfterAssign) ctx
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
                                have hPair :
                                    (Structured.Outcome.halt kind
                                      callOutcome.state, ctx) =
                                      (outcome, runCtx) := by
                                  simpa using hRun
                                injection hPair with hOutcome hCtx
                                rw [← hOutcome, ← hCtx]
                                let callFuel := bodyFuel + 2
                                have hCallLower :
                                    Locals.Direct.Block.runOpen program.toLocals
                                      ctx callFuel { stmts := [Locals.Stmt.call
                                        functionName] } stateAfterArgs =
                                      .ok (Structured.Outcome.halt kind
                                        callOutcome.state, ctx) := by
                                    unfold callFuel
                                    simp [Locals.Direct.Block.runOpen,
                                      Locals.Direct.Stmt.run, hLowerLookup',
                                      FunDef.toLocalsProc, hSplit, callState]
                                    rw [hBodyLowerOpen']
                                    cases hLowerMode : lowerBodyOutcome.mode with
                                    | regular =>
                                        simp [FunDef.lowerBodyResult,
                                          hLowerMode] at hBodyRel
                                        cases hCleanup :
                                            Locals.Direct.Ctx.runCleanupToPreserving
                                              lowerBodyCtx fn.returns.length 0
                                              lowerBodyOutcome.state with
                                        | error err =>
                                            simp [hCleanup] at hBodyRel
                                        | ok cleaned =>
                                            have hEq :
                                                Structured.Outcome.regular
                                                  cleaned = callOutcome := by
                                              simpa [hCleanup,
                                                Structured.Outcome.regular]
                                                using hBodyRel
                                            cases hEq
                                            simp at hBodyMode
                                    | brk =>
                                        simp [FunDef.lowerBodyResult,
                                          hLowerMode, Structured.invalid]
                                          at hBodyRel
                                    | cont =>
                                        simp [FunDef.lowerBodyResult,
                                          hLowerMode, Structured.invalid]
                                          at hBodyRel
                                    | leave =>
                                        simp [FunDef.lowerBodyResult,
                                          hLowerMode] at hBodyRel
                                        have hEq :
                                            lowerBodyOutcome = callOutcome := by
                                          simpa using hBodyRel
                                        cases hEq
                                        simp [hLowerMode] at hBodyMode
                                    | halt lowerKind =>
                                        simp [FunDef.lowerBodyResult,
                                          hLowerMode] at hBodyRel
                                        have hEq :
                                            lowerBodyOutcome = callOutcome := by
                                          simpa using hBodyRel
                                        cases hEq
                                        have hKindEq : lowerKind = kind := by
                                          rw [hBodyMode] at hLowerMode
                                          cases hLowerMode
                                          rfl
                                        subst lowerKind
                                        simp [hLowerMode,
                                          Structured.Outcome.halt]
                                rcases
                                  Locals.Direct.Block.runOpen_append_regular_exists
                                    program.toLocals
                                    (Lower.evalArgs args)
                                    [Locals.Stmt.call functionName]
                                    ctx ctx state stateAfterArgs
                                    (Structured.Outcome.halt kind
                                      callOutcome.state) ctx
                                    ⟨argsFuel, hArgsLower⟩
                                    ⟨callFuel, hCallLower⟩ with
                                  ⟨argsCallFuel, hArgsCallLower⟩
                                have hNonregular :
                                    (Structured.Outcome.halt kind
                                      callOutcome.state).mode ≠ .regular := by
                                  simp [Structured.Outcome.halt]
                                rcases
                                  Locals.Direct.Block.runOpen_append_nonregular_exists
                                    program.toLocals
                                    (Lower.evalArgs args ++
                                      [Locals.Stmt.call functionName])
                                    (Lower.assignReturnedTops targets)
                                    ctx state
                                    (Structured.Outcome.halt kind
                                      callOutcome.state) ctx
                                    ⟨argsCallFuel, by
                                      simpa [List.append_assoc] using
                                        hArgsCallLower⟩
                                    hNonregular with
                                  ⟨lowerFuel, hLower⟩
                                exact ⟨lowerFuel, by
                                  simpa [Stmt.toLocals, List.append_assoc,
                                    Lower.assignReturnedTops] using hLower⟩
    | terminal kind =>
        exact ⟨1, by
          simpa [Stmt.run, Stmt.toLocals, Locals.Direct.Block.runOpen,
            Locals.Direct.Stmt.run, Structured.Outcome.halt] using hRun⟩
    | terminalArgs kind args =>
        exact ⟨1, by
          simpa [Stmt.run, Stmt.toLocals, Locals.Direct.Block.runOpen,
            Locals.Direct.Stmt.run, Structured.Outcome.halt] using hRun⟩
  termination_by
    returns _ctx fuel stmt _state _outcome _runCtx _hRun =>
      (fuel, 4, sizeOf stmt)
  decreasing_by
    all_goals simp_wf
    all_goals
      first
      | omega
      | exact Prod.Lex.right _
          (Prod.Lex.left _ _ (by omega))
end

namespace Program

theorem runState_toLocals_exists {program : Program} {fuel : Nat}
    {state : RunState} {outcome : Outcome}
    (hRun : Direct.Program.runState fuel program state = .ok outcome) :
    ∃ lowerFuel,
      Locals.Direct.Program.runState lowerFuel program.toLocals state =
        .ok outcome := by
  exact Block.runScoped_toLocals_exists program hRun

theorem run_toLocals_exists {program : Program} {fuel : Nat}
    {initial : EVMState} {outcome : Outcome}
    (hRun : Direct.Program.run fuel program initial = .ok outcome) :
    ∃ lowerFuel,
      Locals.Program.run lowerFuel program.toLocals initial = .ok outcome := by
  exact runState_toLocals_exists hRun

end Program

end Direct

namespace Program

noncomputable def compileChecked? (program : Program) :
    Option Assembly.Program := do
  let lower ← program.toExpressions?
  Expressions.Program.compileChecked? lower

theorem compileChecked?_eq_some {program : Program}
    {asm : Assembly.Program}
    (hCompile : compileChecked? program = some asm) :
    ∃ lower : Expressions.Program,
      program.toExpressions? = some lower ∧
        Expressions.Program.compileChecked? lower = some asm := by
  unfold compileChecked? at hCompile
  cases hLower : program.toExpressions? with
  | none =>
      simp [hLower] at hCompile
  | some lower =>
      simp [hLower] at hCompile
      exact ⟨lower, rfl, hCompile⟩

theorem compileChecked?_noCallCreate {program : Program}
    {asm : Assembly.Program}
    (hProgram : program.usesCallCreate = false)
    (hCompile : compileChecked? program = some asm) :
    Assembly.Program.usesCallCreate asm = false := by
  rcases compileChecked?_eq_some hCompile with
    ⟨lower, hLower, hLowerCompile⟩
  have hLocalsNoCall :
      program.toLocals.usesCallCreate = false :=
    CompilerFacts.Program.toLocals_noCallCreate program hProgram
  have hLowerNo :
      lower.usesCallCreate = false :=
    Locals.CompilerFacts.Program.toExpressions?_noCallCreate
      program.toLocals hLocalsNoCall
      (by simpa [Program.toExpressions?] using hLower)
  exact
    Expressions.Program.compileChecked?_noCallCreate hLowerNo hLowerCompile

theorem compile_preserves {program : Program} {lower : Expressions.Program}
    {asm : Assembly.Program} {fuel : Nat} {initial : EVMState}
    {outcome : Outcome}
    (hLower : program.toExpressions? = some lower)
    (hCompile :
      Structured.Preservation.ProcedurePreservation.compileChecked?
        lower.toStructured = some asm)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hRun : program.run fuel initial = .ok outcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      Structured.Preservation.WholeProgramOutcomeRel outcome targetOutcome := by
  rcases Direct.Program.run_toLocals_exists
      (by simpa [Program.run] using hRun) with
    ⟨lowerFuel, hLowerRun⟩
  exact
    Locals.Program.compile_preserves hLower hCompile hInitialPc hLowerRun

theorem compile_preserves_checked {program : Program} {asm : Assembly.Program}
    {fuel : Nat} {initial : EVMState} {outcome : Outcome}
    (hCompile : compileChecked? program = some asm)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hRun : program.run fuel initial = .ok outcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      Structured.Preservation.WholeProgramOutcomeRel outcome targetOutcome := by
  rcases compileChecked?_eq_some hCompile with
    ⟨lower, hLower, hLowerCompile⟩
  rcases Direct.Program.run_toLocals_exists
      (by simpa [Program.run] using hRun) with
    ⟨lowerFuel, hLowerRun⟩
  have hLocalsCompile :
      Locals.Program.compileChecked? program.toLocals = some asm := by
    have hLowerLocals : program.toLocals.toExpressions? = some lower := by
      simpa [Program.toExpressions?] using hLower
    unfold Locals.Program.compileChecked?
    simp [hLowerLocals, hLowerCompile]
  exact
    Locals.Program.compile_preserves_checked
      hLocalsCompile hInitialPc hLowerRun

end Program

namespace Source

/--
Whole-program observation relation for the stack-free function source
interpreter. The direct procedure outcome is existentially hidden here: callers
above the function layer should rely on named-source outcomes, not on operand
stack frames, return tokens, cleanup depths, or direct procedure layouts.
-/
def WholeProgramOutcomeRel (source : Outcome)
    (target : Assembly.StepResult) : Prop :=
  ∃ direct,
    SourceDirect.BlockScopedOutcomeRel [] [] [] source direct ∧
      Structured.Preservation.WholeProgramOutcomeRel direct target

namespace Program

/--
Source-facing compiler acceptance for the function layer.

`source` is the actual source-language wellformedness/scoping condition.
`frameBound` is a compiler resource bound for the lowering into the direct
procedure backend; it is intentionally bundled here so higher layers do not
traffic directly in return-token/frame-layout proof objects.
-/
structure CompileAccepted (program : Functions.Program) : Prop where
  source : program.SourceAccepted
  frameBound : SourceDirect.FrameBound.Program program

noncomputable def compileChecked? (program : Functions.Program) :
    Option Assembly.Program := do
  let lower ← program.toExpressions?
  Structured.Preservation.ProcedurePreservation.compileChecked?
    lower.toStructured

theorem compileChecked?_eq_some {program : Functions.Program}
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

theorem compileChecked?_noCallCreate {program : Functions.Program}
    {asm : Assembly.Program}
    (hProgram : program.usesCallCreate = false)
    (hCompile : compileChecked? program = some asm) :
    Assembly.Program.usesCallCreate asm = false := by
  rcases compileChecked?_eq_some hCompile with
    ⟨lower, hLower, hLowerCompile⟩
  have hLocalsNoCall :
      program.toLocals.usesCallCreate = false :=
    CompilerFacts.Program.toLocals_noCallCreate program hProgram
  have hLowerNo :
      lower.usesCallCreate = false :=
    Locals.CompilerFacts.Program.toExpressions?_noCallCreate
      program.toLocals hLocalsNoCall
      (by simpa [Functions.Program.toExpressions?] using hLower)
  exact
    Structured.Preservation.ProcedurePreservation.compileChecked?_noCallCreate
      (program := lower.toStructured) (asm := asm)
      (by
        simpa [Expressions.CompilerFacts.Program.toStructured_usesCallCreate]
          using hLowerNo)
      hLowerCompile

theorem runState_toDirect_exists_of_compileAccepted
    {prim : PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {program : Functions.Program} {fuel : Nat}
    {source : Source.State} {target : Locals.RunState}
    {sourceOutcome : Source.Outcome}
    (hAccepted : CompileAccepted program)
    (hSourceRun :
      Source.Program.runState prim fuel program source = .ok sourceOutcome)
    (hRel : SourceDirect.StateRel [] [] source target) :
    ∃ targetOutcome,
      Direct.Program.runState fuel program target = .ok targetOutcome ∧
      SourceDirect.BlockScopedOutcomeRel [] [] [] sourceOutcome
        targetOutcome := by
  exact
    SourceDirect.Program.runState_toDirect_exists
      (prim := prim) hPrim (program := program) (fuel := fuel)
      (source := source) (target := target)
      (sourceOutcome := sourceOutcome)
      hAccepted.source.2 hAccepted.frameBound hSourceRun hRel

theorem run_toDirect_exists_of_compileAccepted
    {prim : PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {program : Functions.Program} {fuel : Nat}
    {initial : EVMState} {sourceOutcome : Source.Outcome}
    (hAccepted : CompileAccepted program)
    (hInitialStack : initial.stack = [])
    (hSourceRun :
      Source.Program.run prim fuel program initial = .ok sourceOutcome) :
    ∃ targetOutcome,
      Direct.Program.run fuel program initial = .ok targetOutcome ∧
      SourceDirect.BlockScopedOutcomeRel [] [] [] sourceOutcome
        targetOutcome := by
  exact
    SourceDirect.Program.run_toDirect_exists
      (prim := prim) hPrim (program := program) (fuel := fuel)
      (initial := initial) (sourceOutcome := sourceOutcome)
      hAccepted.source.2 hAccepted.frameBound hInitialStack hSourceRun

theorem compile_preserves {prim : PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {program : Functions.Program} {lower : Expressions.Program}
    {asm : Assembly.Program} {fuel : Nat} {initial : EVMState}
    {sourceOutcome : Source.Outcome}
    (hScoped : program.Scoped)
    (hFrameBound : SourceDirect.FrameBound.Program program)
    (hLower : program.toExpressions? = some lower)
    (hCompile :
      Structured.Preservation.ProcedurePreservation.compileChecked?
        lower.toStructured = some asm)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = [])
    (hRun : Source.Program.run prim fuel program initial = .ok sourceOutcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      WholeProgramOutcomeRel sourceOutcome targetOutcome := by
  rcases
      SourceDirect.Program.run_toDirect_exists
        (prim := prim) hPrim (program := program) (fuel := fuel)
        (initial := initial) (sourceOutcome := sourceOutcome)
        hScoped hFrameBound hInitialStack hRun with
    ⟨directOutcome, hDirectRun, hSourceRel⟩
  rcases
      Functions.Program.compile_preserves
        (program := program) (lower := lower) (asm := asm)
        (fuel := fuel) (initial := initial) (outcome := directOutcome)
        hLower hCompile hInitialPc
        (by simpa [Functions.Program.run] using hDirectRun) with
    ⟨targetFuel, targetOutcome, hTargetRun, hWholeRel⟩
  exact
    ⟨targetFuel, targetOutcome, hTargetRun, directOutcome, hSourceRel,
      hWholeRel⟩

theorem compile_preserves_of_compileAccepted
    {prim : PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {program : Functions.Program} {lower : Expressions.Program}
    {asm : Assembly.Program} {fuel : Nat} {initial : EVMState}
    {sourceOutcome : Source.Outcome}
    (hAccepted : CompileAccepted program)
    (hLower : program.toExpressions? = some lower)
    (hCompile :
      Structured.Preservation.ProcedurePreservation.compileChecked?
        lower.toStructured = some asm)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = [])
    (hRun : Source.Program.run prim fuel program initial = .ok sourceOutcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      WholeProgramOutcomeRel sourceOutcome targetOutcome := by
  exact
    compile_preserves (prim := prim) hPrim (program := program)
      (lower := lower) (asm := asm) (fuel := fuel) (initial := initial)
      (sourceOutcome := sourceOutcome) hAccepted.source.2
      hAccepted.frameBound hLower hCompile hInitialPc hInitialStack hRun

theorem compile_preserves_checked_of_compileAccepted
    {prim : PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {program : Functions.Program} {asm : Assembly.Program} {fuel : Nat}
    {initial : EVMState} {sourceOutcome : Source.Outcome}
    (hCompile : compileChecked? program = some asm)
    (hAccepted : CompileAccepted program)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = [])
    (hRun : Source.Program.run prim fuel program initial = .ok sourceOutcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      WholeProgramOutcomeRel sourceOutcome targetOutcome := by
  rcases compileChecked?_eq_some hCompile with
    ⟨lower, hLower, hStructuredCompile⟩
  exact
    compile_preserves_of_compileAccepted hPrim hAccepted hLower
      hStructuredCompile hInitialPc hInitialStack hRun

end Program
end Source

namespace Inline
namespace Program

theorem compile_preserves {program : Functions.Program}
    {lower : Expressions.Program} {asm : Assembly.Program}
    {fuel : Nat} {initial : EVMState} {outcome : Outcome}
    (hLower : Functions.Program.toExpressions? program = some lower)
    (hCompile :
      Structured.Preservation.ProcedurePreservation.compileChecked?
        lower.toStructured = some asm)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hRun : Functions.Program.run fuel program initial = .ok outcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      Structured.Preservation.WholeProgramOutcomeRel outcome targetOutcome :=
  Functions.Program.compile_preserves hLower hCompile hInitialPc hRun

end Program
end Inline

end Functions
end EvmCompiler
