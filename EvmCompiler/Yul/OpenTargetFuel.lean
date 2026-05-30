import EvmCompiler.Yul.CompilerOpen

/-!
Successful-path fuel extension for open compiler-source execution.

`CompilerOpen` fuel is an executable cutoff.  Increasing it does not preserve
the entire open interaction tree: an under-fueled sibling path may stop before
a later external call that a larger cutoff exposes.  The useful compositional
fact is narrower and true.  Once one concrete finite response path already
resolves successfully, any larger cutoff follows that same path to the same
successful result.
-/

namespace EvmCompiler
namespace Yul
namespace Reference
namespace SourceBridgeFacts
namespace CompilerOpen
namespace FunctionsOpen

private theorem invalid_not_resolves_ok
    {α : Type} {trace : OpenExternal.OpenTrace} {result : α}
    (h :
      OpenExternal.OpenResultResolves
        (CompilerOpen.invalid : CompilerOpen.Result α) trace (.ok result)) :
    False := by
  cases h

set_option maxHeartbeats 1000000 in
mutual
  theorem Block.runOpen_resolves_mono
      (prim : Objects.Source.PrimitiveSemantics)
      (program : Functions.Program) :
      ∀ {fuel fuel' : Nat} {ctx : Ctx} {block : Functions.Block}
        {state : State} {trace : OpenExternal.OpenTrace}
        {result : Outcome × Ctx},
        fuel ≤ fuel' →
        OpenExternal.OpenResultResolves
          (Block.runOpen prim program ctx fuel block state) trace (.ok result) →
        OpenExternal.OpenResultResolves
          (Block.runOpen prim program ctx fuel' block state) trace
          (.ok result) := by
    intro fuel fuel' ctx block state trace result hLe hRun
    cases fuel with
    | zero =>
        exact
          (invalid_not_resolves_ok
            (by simpa only [Block.runOpen] using hRun)).elim
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
                    simp only [Block.runOpen] at hRun ⊢
                    exact
                      OpenExternal.OpenResultResolves.bind_ok_mono hRun
                        (fun hStmt =>
                          Stmt.run_resolves_mono prim program hFuelLe hStmt)
                        (by
                          intro stmtResult trace result hRest
                          cases hMode : stmtResult.1.mode with
                          | regular =>
                              simp only [hMode] at hRest ⊢
                              exact
                                Block.runOpen_resolves_mono prim program
                                  hFuelLe hRest
                          | brk =>
                              simpa only [hMode] using hRest
                          | cont =>
                              simpa only [hMode] using hRest
                          | leave =>
                              simpa only [hMode] using hRest
                          | halt kind =>
                              simpa only [hMode] using hRest)
  termination_by
    fuel _fuel' _ctx block _state _trace _result _hLe _hRun =>
      (fuel, 0, sizeOf block)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  theorem Block.runScoped_resolves_mono
      (prim : Objects.Source.PrimitiveSemantics)
      (program : Functions.Program) :
      ∀ {fuel fuel' : Nat} {ctx : Ctx} {block : Functions.Block}
        {state : State} {trace : OpenExternal.OpenTrace}
        {result : Outcome},
        fuel ≤ fuel' →
        OpenExternal.OpenResultResolves
          (Block.runScoped prim program ctx block fuel state) trace (.ok result) →
        OpenExternal.OpenResultResolves
          (Block.runScoped prim program ctx block fuel' state) trace
          (.ok result) := by
    intro fuel fuel' ctx block state trace result hLe hRun
    unfold Block.runScoped at hRun ⊢
    exact
      OpenExternal.OpenResultResolves.bind_ok_mono hRun
        (fun hOpen =>
          Block.runOpen_resolves_mono prim program hLe hOpen)
        (fun hNext => hNext)
  termination_by
    fuel _fuel' _ctx block _state _trace _result _hLe _hRun =>
      (fuel, 1, sizeOf block)
  decreasing_by
    all_goals simp_wf
    all_goals
      first
      | omega
      | exact Prod.Lex.right _
          (Prod.Lex.left _ _ (by omega))

  theorem FunDef.runBody_resolves_mono
      (prim : Objects.Source.PrimitiveSemantics)
      (program : Functions.Program) :
      ∀ {fuel fuel' : Nat} {fn : Functions.FunDef} {args : List Word}
        {shared : EvmYul.SharedState .EVM}
        {trace : OpenExternal.OpenTrace} {result : CallResult},
        fuel ≤ fuel' →
        OpenExternal.OpenResultResolves
          (FunDef.runBody prim program fn args fuel shared) trace (.ok result) →
        OpenExternal.OpenResultResolves
          (FunDef.runBody prim program fn args fuel' shared) trace
          (.ok result) := by
    intro fuel fuel' fn args shared trace result hLe hRun
    cases fuel with
    | zero =>
        exact
          (invalid_not_resolves_ok
            (by simpa only [FunDef.runBody] using hRun)).elim
    | succ fuel =>
        cases fuel' with
        | zero =>
            omega
        | succ fuel' =>
            have hFuelLe : fuel ≤ fuel' := Nat.succ_le_succ_iff.mp hLe
            unfold FunDef.runBody at hRun ⊢
            cases hParams :
                Functions.Source.Store.insertMany fn.params args
                  Locals.Source.Store.empty with
            | none =>
                exact
                  (invalid_not_resolves_ok
                    (by simpa only [hParams] using hRun)).elim
            | some paramStore =>
                simp only [hParams] at hRun ⊢
                exact
                  OpenExternal.OpenResultResolves.bind_ok_mono hRun
                    (fun hBody =>
                      Block.runOpen_resolves_mono prim program hFuelLe hBody)
                    (fun hNext => hNext)
  termination_by
    fuel _fuel' fn _args _shared _trace _result _hLe _hRun =>
      (fuel, 2, sizeOf fn.body)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  theorem Stmt.runForLoop_resolves_mono
      (prim : Objects.Source.PrimitiveSemantics)
      (program : Functions.Program) :
      ∀ {fuel fuel' : Nat} {loopCtx : Ctx}
        {cond : Functions.Expr 1} {postBase : Ctx}
        {post : Functions.Block} {bodyBase : Ctx}
        {body : Functions.Block} {state : State}
        {trace : OpenExternal.OpenTrace} {result : Outcome},
        fuel ≤ fuel' →
        OpenExternal.OpenResultResolves
          (Stmt.runForLoop prim program loopCtx cond postBase post bodyBase body
            fuel state) trace (.ok result) →
        OpenExternal.OpenResultResolves
          (Stmt.runForLoop prim program loopCtx cond postBase post bodyBase body
            fuel' state) trace (.ok result) := by
    intro fuel fuel' loopCtx cond postBase post bodyBase body state trace result
      hLe hRun
    cases fuel with
    | zero =>
        exact
          (invalid_not_resolves_ok
            (by simpa only [Stmt.runForLoop] using hRun)).elim
    | succ fuel =>
        cases fuel' with
        | zero =>
            omega
        | succ fuel' =>
            have hFuelLe : fuel ≤ fuel' := Nat.succ_le_succ_iff.mp hLe
            simp only [Stmt.runForLoop] at hRun ⊢
            exact
              OpenExternal.OpenResultResolves.bind_ok_mono hRun
                (fun hCond => hCond)
                (by
                  intro condResult trace result hCondTail
                  cases hCond : condResult.2 with
                  | true =>
                    simp only [hCond] at hCondTail ⊢
                    exact
                      OpenExternal.OpenResultResolves.bind_ok_mono hCondTail
                        (fun hBody =>
                          Block.runScoped_resolves_mono prim program hFuelLe
                            hBody)
                        (by
                          intro bodyOutcome trace result hBodyTail
                          cases hBodyMode : bodyOutcome.mode with
                          | brk =>
                              simpa only [hBodyMode] using hBodyTail
                          | regular =>
                              simp only [hBodyMode] at hBodyTail ⊢
                              exact
                                OpenExternal.OpenResultResolves.bind_ok_mono
                                  hBodyTail
                                  (fun hPost =>
                                    Block.runScoped_resolves_mono prim program
                                      hFuelLe hPost)
                                  (by
                                    intro postOutcome trace result hPostTail
                                    cases hPostMode : postOutcome.mode with
                                    | regular =>
                                        simp only [hPostMode] at hPostTail ⊢
                                        exact
                                          Stmt.runForLoop_resolves_mono prim
                                            program hFuelLe hPostTail
                                    | brk =>
                                        simpa only [hPostMode] using hPostTail
                                    | cont =>
                                        simpa only [hPostMode] using hPostTail
                                    | leave =>
                                        simpa only [hPostMode] using hPostTail
                                    | halt kind =>
                                        simpa only [hPostMode] using
                                          hPostTail)
                          | cont =>
                              simp only [hBodyMode] at hBodyTail ⊢
                              exact
                                OpenExternal.OpenResultResolves.bind_ok_mono
                                  hBodyTail
                                  (fun hPost =>
                                    Block.runScoped_resolves_mono prim program
                                      hFuelLe hPost)
                                  (by
                                    intro postOutcome trace result hPostTail
                                    cases hPostMode : postOutcome.mode with
                                    | regular =>
                                        simp only [hPostMode] at hPostTail ⊢
                                        exact
                                          Stmt.runForLoop_resolves_mono prim
                                            program hFuelLe hPostTail
                                    | brk =>
                                        simpa only [hPostMode] using hPostTail
                                    | cont =>
                                        simpa only [hPostMode] using hPostTail
                                    | leave =>
                                        simpa only [hPostMode] using hPostTail
                                    | halt kind =>
                                        simpa only [hPostMode] using
                                          hPostTail)
                          | leave =>
                              simpa only [hBodyMode] using hBodyTail
                          | halt kind =>
                              simpa only [hBodyMode] using hBodyTail)
                  | false =>
                    simpa only [hCond] using hCondTail)
  termination_by
    fuel _fuel' _loopCtx _cond _postBase _post _bodyBase _body _state
      _trace _result _hLe _hRun => (fuel, 3, 0)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  theorem Stmt.run_resolves_mono
      (prim : Objects.Source.PrimitiveSemantics)
      (program : Functions.Program) :
      ∀ {fuel fuel' : Nat} {ctx : Ctx} {stmt : Functions.Stmt}
        {state : State} {trace : OpenExternal.OpenTrace}
        {result : Outcome × Ctx},
        fuel ≤ fuel' →
        OpenExternal.OpenResultResolves
          (Stmt.run prim program ctx fuel stmt state) trace (.ok result) →
        OpenExternal.OpenResultResolves
          (Stmt.run prim program ctx fuel' stmt state) trace (.ok result) := by
    intro fuel fuel' ctx stmt state trace result hLe hRun
    cases stmt with
    | expr expr =>
        simpa [Stmt.run] using hRun
    | let_ name value =>
        simpa [Stmt.run] using hRun
    | assign name value =>
        simpa [Stmt.run] using hRun
    | block body =>
        simp only [Stmt.run] at hRun ⊢
        exact
          OpenExternal.OpenResultResolves.bind_ok_mono hRun
            (fun hBody =>
              Block.runScoped_resolves_mono prim program hLe hBody)
            (fun hNext => hNext)
    | if_ cond body =>
        cases fuel with
        | zero =>
            exact
              (invalid_not_resolves_ok
                (by simpa only [Stmt.run] using hRun)).elim
        | succ fuel =>
            cases fuel' with
            | zero =>
                omega
            | succ fuel' =>
                have hFuelLe : fuel ≤ fuel' := Nat.succ_le_succ_iff.mp hLe
                simp only [Stmt.run] at hRun ⊢
                exact
                  OpenExternal.OpenResultResolves.bind_ok_mono hRun
                    (fun hCond => hCond)
                    (by
                      intro condResult trace result hCondTail
                      cases hCond : condResult.2 with
                      | true =>
                        simp only [hCond] at hCondTail ⊢
                        exact
                          OpenExternal.OpenResultResolves.bind_ok_mono
                            hCondTail
                            (fun hBody =>
                              Block.runScoped_resolves_mono prim program
                                hFuelLe hBody)
                            (fun hNext => hNext)
                      | false =>
                        simpa only [hCond] using hCondTail)
    | switch scrutinee cases defaultBody =>
        cases fuel with
        | zero =>
            exact
              (invalid_not_resolves_ok
                (by simpa only [Stmt.run] using hRun)).elim
        | succ fuel =>
            cases fuel' with
            | zero =>
                omega
            | succ fuel' =>
                have hFuelLe : fuel ≤ fuel' := Nat.succ_le_succ_iff.mp hLe
                simp only [Stmt.run] at hRun ⊢
                exact
                  OpenExternal.OpenResultResolves.bind_ok_mono hRun
                    (fun hScrutinee => hScrutinee)
                    (by
                      intro scrutineeResult trace result hScrutineeTail
                      cases hSelected :
                          Functions.Source.Switch.select scrutineeResult.2
                            cases defaultBody with
                      | none =>
                          simpa only [hSelected] using hScrutineeTail
                      | some selected =>
                          simp only [hSelected] at hScrutineeTail ⊢
                          exact
                            OpenExternal.OpenResultResolves.bind_ok_mono
                              hScrutineeTail
                              (fun hBody =>
                                Block.runScoped_resolves_mono prim program
                                  hFuelLe hBody)
                              (fun hNext => hNext))
    | for_ init cond post body =>
        cases fuel with
        | zero =>
            exact
              (invalid_not_resolves_ok
                (by simpa only [Stmt.run] using hRun)).elim
        | succ fuel =>
            cases fuel' with
            | zero =>
                omega
            | succ fuel' =>
                have hFuelLe : fuel ≤ fuel' := Nat.succ_le_succ_iff.mp hLe
                simp only [Stmt.run] at hRun ⊢
                exact
                  OpenExternal.OpenResultResolves.bind_ok_mono hRun
                    (fun hInit =>
                      Block.runOpen_resolves_mono prim program hFuelLe hInit)
                    (by
                      intro initResult trace result hInitTail
                      cases hInitMode : initResult.1.mode with
                      | regular =>
                          simp only [hInitMode] at hInitTail ⊢
                          exact
                            OpenExternal.OpenResultResolves.bind_ok_mono
                              hInitTail
                              (fun hLoop =>
                                Stmt.runForLoop_resolves_mono prim program
                                  hFuelLe hLoop)
                              (fun hNext => hNext)
                      | brk =>
                          simpa only [hInitMode] using hInitTail
                      | cont =>
                          simpa only [hInitMode] using hInitTail
                      | leave =>
                          simpa only [hInitMode] using hInitTail
                      | halt kind =>
                          simpa only [hInitMode] using hInitTail)
    | brk =>
        simpa [Stmt.run] using hRun
    | cont =>
        simpa [Stmt.run] using hRun
    | leave =>
        simpa [Stmt.run] using hRun
    | call targets functionName args =>
        cases fuel with
        | zero =>
            exact
              (invalid_not_resolves_ok
                (by simpa only [Stmt.run] using hRun)).elim
        | succ fuel =>
            cases fuel' with
            | zero =>
                omega
            | succ fuel' =>
                have hFuelLe : fuel ≤ fuel' := Nat.succ_le_succ_iff.mp hLe
                simp only [Stmt.run] at hRun ⊢
                by_cases hTargets : targets.Nodup
                · simp only [hTargets, ↓reduceIte] at hRun ⊢
                  exact
                    OpenExternal.OpenResultResolves.bind_ok_mono hRun
                      (fun hArgs => hArgs)
                      (by
                        intro argResult trace result hArgsTail
                        cases hLookup :
                            Functions.Source.FunList.find? functionName
                              program.functions with
                        | none =>
                            simpa only [hLookup] using hArgsTail
                        | some fn =>
                            simp only [hLookup] at hArgsTail ⊢
                            exact
                              OpenExternal.OpenResultResolves.bind_ok_mono
                                hArgsTail
                                (fun hBody =>
                                  FunDef.runBody_resolves_mono prim program
                                    hFuelLe hBody)
                                (fun hNext => hNext))
                · simpa only [hTargets, ↓reduceIte] using hRun
    | terminal kind =>
        simpa [Stmt.run] using hRun
    | terminalArgs kind args =>
        simpa [Stmt.run] using hRun
  termination_by
    fuel _fuel' _ctx stmt _state _trace _result _hLe _hRun =>
      (fuel, 4, sizeOf stmt)
  decreasing_by
    all_goals simp_wf
    all_goals
      first
      | omega
      | exact Prod.Lex.right _
          (Prod.Lex.left _ _ (by omega))
end

end FunctionsOpen
end CompilerOpen
end SourceBridgeFacts
end Reference
end Yul
end EvmCompiler
