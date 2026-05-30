import EvmCompiler.Yul.Compiler

/-!
Static target-fuel accounting for open Yul expression lowering.

The open CALL proof must choose enough residual target fuel before an external
response is known.  Expression lowering is deterministic up to generated fresh
names, and fresh-name choices do not affect the number of emitted prefix
statements.  This module records that compiler-derived prefix length.
-/

namespace EvmCompiler
namespace Yul
namespace OpenFuelAdequacy

mutual
  /-- Number of generated prefix statements emitted by successful lowering. -/
  def exprPreludeLength : AstExpr → Nat
    | .Lit _value => 0
    | .Var _name => 0
    | .Call (.inr _functionName) args =>
        (if Expr.List.directCallArgsSafe? args then
          0
        else
          exprsBoundPreludeLength args) + 2
    | .Call (.inl _prim) args =>
        exprsBoundPreludeLength args

  /--
  Prefix length for bound argument lowering.  Each argument contributes its
  own prefix plus the generated local that snapshots its value.
  -/
  def exprsBoundPreludeLength : List AstExpr → Nat
    | [] => 0
    | head :: rest =>
        exprsBoundPreludeLength rest + exprPreludeLength head + 1
end

mutual
  theorem lower?_pre_length_eq
      {results : Nat} {state state' : Fresh.State} {expr : AstExpr}
      {pre : List Functions.Stmt} {lower : Locals.Expr results}
      (hLower :
        Expr.lower? results state expr = some (pre, lower, state')) :
      pre.length = exprPreludeLength expr := by
    cases expr with
    | Lit value =>
        simp [Expr.lower?, exprPreludeLength] at hLower ⊢
        exact hLower.1
    | Var name =>
        simp [Expr.lower?, exprPreludeLength] at hLower ⊢
        exact hLower.1
    | Call target args =>
        cases target with
        | inr functionName =>
            cases hUnsupported :
                ObjectBuiltin.unsupported? functionName with
            | true =>
                simp [Expr.lower?, hUnsupported] at hLower
            | false =>
                by_cases hResults : 1 = results
                · cases hDirect : Expr.List.directCallArgsSafe? args with
                  | false =>
                      cases hArgs :
                          Expr.List.lowerBound1? state args with
                      | none =>
                          simp [Expr.lower?, hUnsupported, hResults, hDirect,
                            hArgs] at hLower
                      | some argsResult =>
                          rcases argsResult with
                            ⟨preArgs, lowerArgs, stateArgs⟩
                          cases hFresh : Fresh.fresh? stateArgs with
                          | none =>
                              simp [Expr.lower?, hUnsupported, hResults,
                                hDirect, hArgs, hFresh] at hLower
                          | some freshResult =>
                              rcases freshResult with ⟨tmp, stateFresh⟩
                              simp [Expr.lower?, hUnsupported, hResults,
                                hDirect, hArgs, hFresh] at hLower
                              rcases hLower with
                                ⟨hPre, _hLowerExpr, _hState⟩
                              subst pre
                              simpa [exprPreludeLength, hDirect] using
                                lowerBound1?_pre_length_eq hArgs
                  | true =>
                      cases hArgs : Expr.List.toLocals1? args with
                      | none =>
                          simp [Expr.lower?, hUnsupported, hResults, hDirect,
                            hArgs] at hLower
                      | some lowerArgs =>
                          cases hFresh : Fresh.fresh? state with
                          | none =>
                              simp [Expr.lower?, hUnsupported, hResults,
                                hDirect, hArgs, hFresh] at hLower
                          | some freshResult =>
                              rcases freshResult with ⟨tmp, stateFresh⟩
                              simp [Expr.lower?, hUnsupported, hResults,
                                hDirect, hArgs, hFresh] at hLower
                              rcases hLower with
                                ⟨hPre, _hLowerExpr, _hState⟩
                              subst pre
                              simp [exprPreludeLength, hDirect]
                · simp [Expr.lower?, hUnsupported, hResults] at hLower
        | inl prim =>
            cases hBasic : Prim.toBasicOp? prim with
            | none =>
                simp [Expr.lower?, hBasic] at hLower
            | some op =>
                cases hArgs : Expr.List.lowerBound1? state args with
                | none =>
                    simp [Expr.lower?, hBasic, hArgs] at hLower
                | some argsResult =>
                    rcases argsResult with ⟨preArgs, lowerArgs, stateArgs⟩
                    cases hSeq :
                        Expr.List.toStackSeq? lowerArgs
                          (Expressions.Structured.BasicOp.inputs op) with
                    | none =>
                        simp [Expr.lower?, hBasic, hArgs, hSeq] at hLower
                    | some seq =>
                        by_cases hOutputs :
                            Expressions.Structured.BasicOp.outputs op =
                              results
                        · simp [Expr.lower?, hBasic, hArgs, hSeq, hOutputs]
                            at hLower
                          rcases hLower with
                            ⟨hPre, _hLowerExpr, _hState⟩
                          subst pre
                          simpa [exprPreludeLength] using
                            lowerBound1?_pre_length_eq hArgs
                        · simp [Expr.lower?, hBasic, hArgs, hSeq, hOutputs]
                            at hLower

  theorem lowerBound1?_pre_length_eq
      {state state' : Fresh.State} {exprs : List AstExpr}
      {pre : List Functions.Stmt} {lower : List (Locals.Expr 1)}
      (hLower :
        Expr.List.lowerBound1? state exprs = some (pre, lower, state')) :
      pre.length = exprsBoundPreludeLength exprs := by
    cases exprs with
    | nil =>
        simp [Expr.List.lowerBound1?, exprsBoundPreludeLength] at hLower ⊢
        exact hLower.1
    | cons head rest =>
        cases hRest : Expr.List.lowerBound1? state rest with
        | none =>
            simp [Expr.List.lowerBound1?, hRest] at hLower
        | some restResult =>
            rcases restResult with ⟨preRest, lowerRest, stateRest⟩
            cases hHead : Expr.lower? 1 stateRest head with
            | none =>
                simp [Expr.List.lowerBound1?, hRest, hHead] at hLower
            | some headResult =>
                rcases headResult with ⟨preHead, lowerHead, stateHead⟩
                cases hFresh : Fresh.fresh? stateHead with
                | none =>
                    simp [Expr.List.lowerBound1?, hRest, hHead, hFresh]
                      at hLower
                | some freshResult =>
                    rcases freshResult with ⟨tmp, stateFresh⟩
                    simp [Expr.List.lowerBound1?, hRest, hHead, hFresh]
                      at hLower
                    rcases hLower with ⟨hPre, _hLower, _hState⟩
                    subst pre
                    simp [exprsBoundPreludeLength,
                      lowerBound1?_pre_length_eq hRest,
                      lower?_pre_length_eq hHead, Nat.add_assoc]
end

theorem lower1?_pre_length_eq
    {state state' : Fresh.State} {expr : AstExpr}
    {pre : List Functions.Stmt} {lower : Locals.Expr 1}
    (hLower : Expr.lower1? state expr = some (pre, lower, state')) :
    pre.length = exprPreludeLength expr :=
  lower?_pre_length_eq (by simpa [Expr.lower1?] using hLower)

/--
Split any sufficiently large target clock after the generated prefix and one
following statement.  The residual clock is chosen entirely from the compiled
prefix length and the requested total clock.
-/
theorem exists_residual_of_add_succ_le
    {prefixLength minimumTargetFuel targetFuel : Nat}
    (hFuel : prefixLength + minimumTargetFuel.succ ≤ targetFuel) :
    ∃ residualTargetFuel,
      minimumTargetFuel ≤ residualTargetFuel ∧
        targetFuel = prefixLength + residualTargetFuel.succ := by
  exact ⟨targetFuel - prefixLength - 1, by omega, by omega⟩

/--
Split any sufficiently large target clock after the generated prefix and two
following statements.  Internal user-call expressions use this shape for the
generated result-slot initialization and call statement.
-/
theorem exists_residual_of_add_succ_succ_le
    {prefixLength minimumTargetFuel targetFuel : Nat}
    (hFuel : prefixLength + minimumTargetFuel.succ.succ ≤ targetFuel) :
    ∃ residualTargetFuel,
      minimumTargetFuel ≤ residualTargetFuel ∧
        targetFuel = prefixLength + residualTargetFuel.succ.succ := by
  exact ⟨targetFuel - prefixLength - 2, by omega, by omega⟩

/--
Expression-lowering specialization of `exists_residual_of_add_succ_le`.
-/
theorem exists_residual_of_lower1?_add_succ_le
    {state state' : Fresh.State} {expr : AstExpr}
    {pre : List Functions.Stmt} {lower : Locals.Expr 1}
    {minimumTargetFuel targetFuel : Nat}
    (hLower : Expr.lower1? state expr = some (pre, lower, state'))
    (hFuel : exprPreludeLength expr + minimumTargetFuel.succ ≤ targetFuel) :
    ∃ residualTargetFuel,
      minimumTargetFuel ≤ residualTargetFuel ∧
        targetFuel = pre.length + residualTargetFuel.succ := by
  rw [← lower1?_pre_length_eq hLower] at hFuel
  exact exists_residual_of_add_succ_le hFuel

/--
Expression-lowering specialization of `exists_residual_of_add_succ_succ_le`.
-/
theorem exists_residual_of_lower1?_add_succ_succ_le
    {state state' : Fresh.State} {expr : AstExpr}
    {pre : List Functions.Stmt} {lower : Locals.Expr 1}
    {minimumTargetFuel targetFuel : Nat}
    (hLower : Expr.lower1? state expr = some (pre, lower, state'))
    (hFuel :
      exprPreludeLength expr + minimumTargetFuel.succ.succ ≤ targetFuel) :
    ∃ residualTargetFuel,
      minimumTargetFuel ≤ residualTargetFuel ∧
        targetFuel = pre.length + residualTargetFuel.succ.succ := by
  rw [← lower1?_pre_length_eq hLower] at hFuel
  exact exists_residual_of_add_succ_succ_le hFuel

end OpenFuelAdequacy
end Yul
end EvmCompiler
