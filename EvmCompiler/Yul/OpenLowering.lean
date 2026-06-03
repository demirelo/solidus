import EvmCompiler.Yul.CompilerOpen
import EvmCompiler.Yul.OpenAssembly
import EvmCompiler.Functions.Preservation

/-!
Open external-call lowering boundary above assembly.

`OpenAssembly` now proves that selected source-open assembly traces replay
through compiled emitted blocks.  The remaining adjacent compiler theorem is
one layer higher: selected compiler-open function-block executions must lower to
selected source-open assembly executions on the same external trace.
-/

namespace EvmCompiler
namespace Yul
namespace OpenLowering

def CompilerPrimitiveEVMInstructionResultRel
    (baseStack : OpenExternal.Stack)
    (compilerResult : Objects.Source.State × List Word) :
    Assembly.StepResult → Prop
  | .running evmResult =>
      Reference.SourceBridgeFacts.SourceStateRel.CompilerPrimitiveEVMResultRel
        baseStack compilerResult evmResult
  | .halted _ => False

namespace CompilerPrimitiveEVMInstructionResultRel

theorem running_incrPC
    {baseStack : OpenExternal.Stack}
    {compilerResult : Objects.Source.State × List Word}
    {evmResult : EvmYul.EVM.State}
    (hRel :
      Reference.SourceBridgeFacts.SourceStateRel.CompilerPrimitiveEVMResultRel
        baseStack compilerResult evmResult) :
    CompilerPrimitiveEVMInstructionResultRel baseStack compilerResult
      (.running (EvmYul.EVM.State.incrPC evmResult)) := by
  rcases hRel with ⟨hShared, hStack⟩
  exact ⟨by simpa [EvmYul.EVM.State.incrPC] using hShared,
    by simpa [EvmYul.EVM.State.incrPC] using hStack⟩

end CompilerPrimitiveEVMInstructionResultRel

theorem callKind_ofEVMOperation_toBasicOp_toPrimOp
    (kind : OpenExternal.CallKind) :
    OpenExternal.CallKind.ofEVMOperation?
      kind.toBasicOp.toPrimOp.toEVM = some kind := by
  cases kind <;> rfl

theorem basicOp_eq_toBasicOp_of_callKind
    {op : Structured.BasicOp} {kind : OpenExternal.CallKind}
    (hKind : OpenExternal.CallKind.ofBasicOp? op = some kind) :
    op = kind.toBasicOp := by
  cases op <;> cases kind <;>
    simp [OpenExternal.CallKind.ofBasicOp?,
      OpenExternal.CallKind.toBasicOp] at hKind ⊢

theorem basicOp_toPrimOp_haltKind?_none (op : Structured.BasicOp) :
    (Assembly.Instr.prim op.toPrimOp).haltKind? = none := by
  cases op <;> rfl

theorem primStep_run_pc
    {step : Assembly.PrimStep} {state mid : EvmYul.EVM.State}
    (hRun : step.run state = .ok mid) :
    mid.pc = state.pc + EvmYul.UInt256.ofNat 1 := by
  cases step <;>
    simp [Assembly.PrimStep.run, EvmYul.EVM.execBinOp,
      EvmYul.EVM.execUnOp, EvmYul.EVM.execTriOp,
      EvmYul.EVM.executionEnvOp, EvmYul.EVM.unaryExecutionEnvOp,
      EvmYul.EVM.machineStateOp, EvmYul.EVM.binaryMachineStateOp,
      EvmYul.EVM.binaryMachineStateOp',
      EvmYul.EVM.ternaryMachineStateOp, EvmYul.EVM.stateOp,
      EvmYul.EVM.unaryStateOp, EvmYul.EVM.binaryStateOp,
      EvmYul.EVM.ternaryCopyOp, EvmYul.EVM.quaternaryCopyOp,
      EvmYul.dup, EvmYul.swap] at hRun
  all_goals repeat (first | split at hRun | split)
  all_goals
    simp [EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC] at hRun
  all_goals
    first
    | exact False.elim (Except.noConfusion hRun)
    | cases hRun
      rfl

theorem basicOp_no_callCreate_step_pc
    {op : Structured.BasicOp} {state mid : EvmYul.EVM.State}
    (hNoCallCreate : op.toPrimOp.isCallCreate = false)
    (hStep : Structured.BasicOp.step op state = .ok mid) :
    mid.pc = state.pc + EvmYul.UInt256.ofNat 1 := by
  have hContinuing :
      ∃ step : Assembly.PrimStep,
        op.toPrimOp.continuingStep? = some step := by
    cases op <;>
      simp [Structured.BasicOp.toPrimOp,
        Assembly.PrimOp.continuingStep?,
        Assembly.PrimOp.isCallCreate] at hNoCallCreate ⊢
  rcases hContinuing with ⟨step, hStepSome⟩
  have hRun : step.run state = .ok mid := by
    have hEq :=
      Assembly.PrimOp.step_eq_continuingStep_run hStepSome state
    simpa [Structured.BasicOp.step, Assembly.Target.stepInstr, hEq] using
      hStep
  exact primStep_run_pc hRun

theorem evmOpenCall?_resume_pc
    {state : EvmYul.EVM.State} {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EvmYul.EVM.State}
    (hCall :
      OpenExternal.CallKind.evmOpenCall? state kind = some call)
    (response : OpenExternal.CallResponse) :
    (call.resume response).pc = state.pc := by
  unfold OpenExternal.CallKind.evmOpenCall? at hCall
  cases hSite : kind.evmCallSite? state with
  | none =>
      simp [hSite] at hCall
  | some pair =>
      rcases pair with ⟨rest, site⟩
      simp [hSite] at hCall
      cases hCall
      rfl

def BasicOpOpenSupported (op : Structured.BasicOp) : Prop :=
  op.toPrimOp.isCallCreate = false ∨
    ∃ kind : OpenExternal.CallKind,
      OpenExternal.CallKind.ofBasicOp? op = some kind

mutual
  def LocalsExprOpenSupported {results : Nat} :
      Locals.Expr results → Prop
    | .lit _value => True
    | .var _name => True
    | .code _code => False
    | .prim op args =>
        LocalsExprSeqOpenSupported args ∧ BasicOpOpenSupported op

  def LocalsExprSeqOpenSupported {results : Nat} :
      Locals.ExprSeq results → Prop
    | .nil => True
    | .cons head tail =>
        LocalsExprOpenSupported head ∧
          LocalsExprSeqOpenSupported tail
end

theorem basicOpOpenSupported_of_no_callCreate
    {op : Structured.BasicOp}
    (hNoCallCreate : op.toPrimOp.isCallCreate = false) :
    BasicOpOpenSupported op :=
  Or.inl hNoCallCreate

mutual
  theorem localsExprOpenSupported_of_sourceOwned_no_callCreate :
      ∀ {results : Nat} {expr : Locals.Expr results},
        Locals.Source.Expr.SourceOwned expr →
        expr.usesCallCreate = false →
          LocalsExprOpenSupported expr := by
    intro results expr hOwned hNoCallCreate
    cases expr with
    | lit value =>
        simp [LocalsExprOpenSupported]
    | var name =>
        simp [LocalsExprOpenSupported]
    | code code =>
        simp [Locals.Source.Expr.SourceOwned] at hOwned
    | prim op args =>
        simp [Locals.Source.Expr.SourceOwned] at hOwned
        have hParts :
            args.usesCallCreate = false ∧
              op.toPrimOp.isCallCreate = false := by
          simpa [Locals.Expr.usesCallCreate] using hNoCallCreate
        exact
          ⟨localsExprSeqOpenSupported_of_sourceOwned_no_callCreate
              hOwned hParts.1,
            basicOpOpenSupported_of_no_callCreate hParts.2⟩

  theorem localsExprSeqOpenSupported_of_sourceOwned_no_callCreate :
      ∀ {results : Nat} {exprs : Locals.ExprSeq results},
        Locals.Source.ExprSeq.SourceOwned exprs →
        exprs.usesCallCreate = false →
          LocalsExprSeqOpenSupported exprs := by
    intro results exprs hOwned hNoCallCreate
    cases exprs with
    | nil =>
        simp [LocalsExprSeqOpenSupported]
    | @cons left right head tail =>
        simp [Locals.Source.ExprSeq.SourceOwned] at hOwned
        rcases hOwned with ⟨hHeadOwned, hTailOwned⟩
        have hParts :
            head.usesCallCreate = false ∧
              tail.usesCallCreate = false := by
          simpa [Locals.ExprSeq.usesCallCreate] using hNoCallCreate
        exact
          ⟨localsExprOpenSupported_of_sourceOwned_no_callCreate
              hHeadOwned hParts.1,
            localsExprSeqOpenSupported_of_sourceOwned_no_callCreate
              hTailOwned hParts.2⟩
end

theorem codeSegment_instrAtPc_start_cons
    {asm : Assembly.Program} {instr : Assembly.Instr}
    {suffix : Assembly.Program}
    (segment :
      Structured.Preservation.CodeSegment asm (instr :: suffix)) :
    Assembly.Program.instrAtPc asm
      (Structured.Preservation.CodeSegment.startPc segment).toNat =
        some
          ((Structured.Preservation.CodeSegment.startPc segment).toNat,
            instr) := by
  rcases segment with ⟨pre, post, hAsm, hFits⟩
  subst asm
  have hFitsStart :
      (Assembly.Program.pcAfter pre).toNat =
        Assembly.Program.byteLength pre :=
    Structured.Preservation.AssemblyProgram.PCFitsFrom.start hFits
  unfold Structured.Preservation.CodeSegment.startPc
  unfold Assembly.Program.instrAtPc
  rw [hFitsStart]
  simpa [List.append_assoc] using
    Assembly.Program.instrAtPcFrom_append_boundary_cons
      pre (suffix ++ post) instr 0

theorem codeSegment_right_startPc_eq_left_fallthroughPc
    {asm first second : Assembly.Program}
    (segment :
      Structured.Preservation.CodeSegment asm (first ++ second)) :
    Structured.Preservation.CodeSegment.startPc
        (Structured.Preservation.CodeSegment.right segment) =
      Structured.Preservation.CodeSegment.fallthroughPc
        (Structured.Preservation.CodeSegment.left segment) := by
  rfl

theorem codeSegment_fallthroughPc_empty
    {asm : Assembly.Program}
    (segment : Structured.Preservation.CodeSegment asm []) :
    Structured.Preservation.CodeSegment.fallthroughPc segment =
      Structured.Preservation.CodeSegment.startPc segment := by
  rcases segment with ⟨pre, post, hAsm, hFits⟩
  simp [Structured.Preservation.CodeSegment.fallthroughPc,
    Structured.Preservation.CodeSegment.startPc]

theorem structuredBlock_compileFromCtx_code_cons_code_eq
    (ctx : Structured.CompileContext) (supply : Structured.LabelSupply)
    (code : Structured.Code) (rest : List Structured.Stmt) :
    (Structured.Block.compileFromCtx
        { stmts := Structured.Stmt.code code :: rest } ctx supply).code =
      code.toAssembly ++
        (Structured.Block.compileFromCtx { stmts := rest } ctx supply).code := by
  simp [Structured.Block.compileFromCtx,
    Structured.Stmt.compileFromCtxCore,
    Structured.CompileResult.append]

theorem codeSegment_structuredBlock_code_cons_split
    {asm : Assembly.Program} {ctx : Structured.CompileContext}
    {supply : Structured.LabelSupply} {code : Structured.Code}
    {rest : List Structured.Stmt}
    (segment :
      Structured.Preservation.CodeSegment asm
        (Structured.Block.compileFromCtx
          { stmts := Structured.Stmt.code code :: rest } ctx supply).code) :
    ∃ headSegment :
        Structured.Preservation.CodeSegment asm code.toAssembly,
      ∃ tailSegment :
          Structured.Preservation.CodeSegment asm
            (Structured.Block.compileFromCtx { stmts := rest } ctx supply).code,
        Structured.Preservation.CodeSegment.startPc headSegment =
          Structured.Preservation.CodeSegment.startPc segment ∧
        Structured.Preservation.CodeSegment.startPc tailSegment =
          Structured.Preservation.CodeSegment.fallthroughPc headSegment ∧
        Structured.Preservation.CodeSegment.fallthroughPc tailSegment =
          Structured.Preservation.CodeSegment.fallthroughPc segment := by
  have hCodeEq :
      (Structured.Block.compileFromCtx
          { stmts := Structured.Stmt.code code :: rest } ctx supply).code =
        code.toAssembly ++
          (Structured.Block.compileFromCtx { stmts := rest } ctx supply).code :=
    structuredBlock_compileFromCtx_code_cons_code_eq ctx supply code rest
  let appendSegment :
      Structured.Preservation.CodeSegment asm
        (code.toAssembly ++
          (Structured.Block.compileFromCtx { stmts := rest } ctx supply).code) :=
    Structured.Preservation.CodeSegment.cast_code hCodeEq segment
  let headSegment :
      Structured.Preservation.CodeSegment asm code.toAssembly :=
    Structured.Preservation.CodeSegment.left appendSegment
  let tailSegment :
      Structured.Preservation.CodeSegment asm
        (Structured.Block.compileFromCtx { stmts := rest } ctx supply).code :=
    Structured.Preservation.CodeSegment.right appendSegment
  refine ⟨headSegment, tailSegment, ?_, ?_, ?_⟩
  · simp [headSegment, appendSegment,
      Structured.Preservation.CodeSegment.left,
      Structured.Preservation.CodeSegment.cast_code,
      Structured.Preservation.CodeSegment.startPc]
  · simpa [headSegment, tailSegment] using
      codeSegment_right_startPc_eq_left_fallthroughPc appendSegment
  · simp [tailSegment, appendSegment,
      Structured.Preservation.CodeSegment.right,
      Structured.Preservation.CodeSegment.cast_code,
      Structured.Preservation.CodeSegment.fallthroughPc, hCodeEq]

theorem expressionsStmtList_toStructured_codeStmt_append
    (code : Structured.Code) (rest : List Expressions.Stmt) :
    Expressions.StmtList.toStructured (Locals.codeStmt code ++ rest) =
      Structured.Stmt.code code :: Expressions.StmtList.toStructured rest := by
  simp [Locals.codeStmt, Expressions.StmtList.toStructured,
    Expressions.Stmt.toStructured]

theorem codeSegment_expressions_codeStmt_cons_split
    {asm : Assembly.Program} {ctx : Structured.CompileContext}
    {supply : Structured.LabelSupply} {code : Structured.Code}
    {rest : List Expressions.Stmt}
    (segment :
      Structured.Preservation.CodeSegment asm
        (Structured.Block.compileFromCtx
          { stmts :=
              Expressions.StmtList.toStructured
                (Locals.codeStmt code ++ rest) } ctx supply).code) :
    ∃ headSegment :
        Structured.Preservation.CodeSegment asm code.toAssembly,
      ∃ tailSegment :
          Structured.Preservation.CodeSegment asm
            (Structured.Block.compileFromCtx
              { stmts := Expressions.StmtList.toStructured rest }
              ctx supply).code,
        Structured.Preservation.CodeSegment.startPc headSegment =
          Structured.Preservation.CodeSegment.startPc segment ∧
        Structured.Preservation.CodeSegment.startPc tailSegment =
          Structured.Preservation.CodeSegment.fallthroughPc headSegment ∧
        Structured.Preservation.CodeSegment.fallthroughPc tailSegment =
          Structured.Preservation.CodeSegment.fallthroughPc segment := by
  have hCodeEq :
      (Structured.Block.compileFromCtx
          { stmts :=
              Expressions.StmtList.toStructured
                (Locals.codeStmt code ++ rest) } ctx supply).code =
        (Structured.Block.compileFromCtx
          { stmts :=
              Structured.Stmt.code code ::
                Expressions.StmtList.toStructured rest } ctx supply).code := by
    simp [expressionsStmtList_toStructured_codeStmt_append]
  let segment' :
      Structured.Preservation.CodeSegment asm
        (Structured.Block.compileFromCtx
          { stmts :=
              Structured.Stmt.code code ::
                Expressions.StmtList.toStructured rest } ctx supply).code :=
    Structured.Preservation.CodeSegment.cast_code hCodeEq segment
  rcases codeSegment_structuredBlock_code_cons_split segment' with
    ⟨headSegment, tailSegment, hHeadStart, hTailStart, hTailFall⟩
  refine ⟨headSegment, tailSegment, ?_, hTailStart, ?_⟩
  · simpa [segment', Structured.Preservation.CodeSegment.cast_code,
      Structured.Preservation.CodeSegment.startPc] using hHeadStart
  · simpa [segment', Structured.Preservation.CodeSegment.cast_code,
      Structured.Preservation.CodeSegment.fallthroughPc] using hTailFall

theorem codeSegment_fallthroughPc_singleton
    {asm : Assembly.Program} {instr : Assembly.Instr}
    (segment :
      Structured.Preservation.CodeSegment asm [instr]) :
    Structured.Preservation.CodeSegment.fallthroughPc segment =
      Structured.Preservation.CodeSegment.startPc segment +
        EvmYul.UInt256.ofNat instr.byteSize := by
  rcases segment with ⟨pre, post, hAsm, hFits⟩
  simp [Structured.Preservation.CodeSegment.fallthroughPc,
    Structured.Preservation.CodeSegment.startPc,
    Assembly.Program.pcAfter_snoc]

theorem localsExpr_compileCode_lit_eq
    {ctx : Locals.Ctx} {offset : Nat} {value : Word}
    {code : Structured.Code}
    (hCompile :
      Locals.Expr.compileCode ctx offset (.lit value) = some code) :
    code = [Structured.BasicInstr.push value] := by
  simpa [Locals.Expr.compileCode] using hCompile.symm

theorem localsExpr_compileCode_var_inv
    {ctx : Locals.Ctx} {offset : Nat} {name : Name}
    {code : Structured.Code}
    (hCompile :
      Locals.Expr.compileCode ctx offset (.var name) = some code) :
    ∃ depth op,
      Locals.Layout.lookupDepth? name ctx.layout = some depth ∧
      Locals.StackOp.dup? (offset + depth) = some op ∧
      code = [Structured.BasicInstr.op op] := by
  unfold Locals.Expr.compileCode at hCompile
  cases hDepth : Locals.Layout.lookupDepth? name ctx.layout with
  | none =>
      simp [hDepth] at hCompile
  | some depth =>
      cases hDup : Locals.StackOp.dup? (offset + depth) with
      | none =>
          simp [hDepth, hDup] at hCompile
      | some op =>
          simp [hDepth, hDup] at hCompile
          exact ⟨depth, op, rfl, hDup, hCompile.symm⟩

theorem localsExpr_compileCode_prim_inv
    {ctx : Locals.Ctx} {offset : Nat}
    {op : Structured.BasicOp}
    {args : Locals.ExprSeq (Expressions.Structured.BasicOp.inputs op)}
    {code : Structured.Code}
    (hCompile :
      Locals.Expr.compileCode ctx offset (.prim op args) = some code) :
    ∃ argsCode,
      Locals.ExprSeq.compileCode ctx offset args = some argsCode ∧
      code = argsCode ++ [Structured.BasicInstr.op op] := by
  unfold Locals.Expr.compileCode at hCompile
  cases hArgs : Locals.ExprSeq.compileCode ctx offset args with
  | none =>
      simp [hArgs] at hCompile
  | some argsCode =>
      simp [hArgs] at hCompile
      exact ⟨argsCode, rfl, hCompile.symm⟩

theorem localsExprSeq_compileCode_nil_eq
    {ctx : Locals.Ctx} {offset : Nat} {code : Structured.Code}
    (hCompile :
      Locals.ExprSeq.compileCode ctx offset Locals.ExprSeq.nil = some code) :
    code = [] := by
  simpa [Locals.ExprSeq.compileCode] using hCompile.symm

theorem localsExprSeq_compileCode_cons_inv
    {ctx : Locals.Ctx} {offset left right : Nat}
    {head : Locals.Expr left} {tail : Locals.ExprSeq right}
    {code : Structured.Code}
    (hCompile :
      Locals.ExprSeq.compileCode ctx offset
        (Locals.ExprSeq.cons head tail) = some code) :
    ∃ headCode tailCode,
      Locals.Expr.compileCode ctx offset head = some headCode ∧
      Locals.ExprSeq.compileCode ctx (offset + left) tail = some tailCode ∧
      code = headCode ++ tailCode := by
  unfold Locals.ExprSeq.compileCode at hCompile
  cases hHead : Locals.Expr.compileCode ctx offset head with
  | none =>
      simp [hHead] at hCompile
  | some headCode =>
      cases hTail : Locals.ExprSeq.compileCode ctx (offset + left) tail with
      | none =>
          simp [hHead, hTail] at hCompile
      | some tailCode =>
          simp [hHead, hTail] at hCompile
          exact ⟨headCode, tailCode, rfl, rfl, hCompile.symm⟩

theorem localsBlock_compileOpen_expr_cons_inv
    {ctx finalCtx : Locals.Ctx} {expr : Locals.Expr 0}
    {rest : List Locals.Stmt} {stmts : List Expressions.Stmt}
    (hCompile :
      Locals.Block.compileOpen ctx
          { stmts := Locals.Stmt.expr expr :: rest } =
        some (stmts, finalCtx)) :
    ∃ code restStmts,
      Locals.Expr.compileCode ctx 0 expr = some code ∧
        Locals.Block.compileOpen ctx { stmts := rest } =
          some (restStmts, finalCtx) ∧
        stmts = Locals.codeStmt code ++ restStmts := by
  unfold Locals.Block.compileOpen at hCompile
  cases hCode : Locals.Expr.compileCode ctx 0 expr with
  | none =>
      simp [Locals.Stmt.compile, hCode] at hCompile
  | some code =>
      cases hRest :
          Locals.Block.compileOpen ctx { stmts := rest } with
      | none =>
          simp [Locals.Stmt.compile, hCode, hRest] at hCompile
      | some restResult =>
          rcases restResult with ⟨restStmts, restCtx⟩
          simp [Locals.Stmt.compile, hCode, hRest] at hCompile
          rcases hCompile with ⟨hStmts, hFinalCtx⟩
          exact
            ⟨code, restStmts, rfl,
              by simp [hFinalCtx], hStmts.symm⟩

theorem localsBlock_compileOpen_let_cons_inv
    {ctx finalCtx : Locals.Ctx} {name : Name}
    {value : Locals.Expr 1}
    {rest : List Locals.Stmt} {stmts : List Expressions.Stmt}
    (hCompile :
      Locals.Block.compileOpen ctx
          { stmts := Locals.Stmt.let_ name value :: rest } =
        some (stmts, finalCtx)) :
    ∃ code restStmts,
      Locals.Expr.compileCode ctx 0 value = some code ∧
        Locals.Block.compileOpen (ctx.withLayout (name :: ctx.layout))
          { stmts := rest } = some (restStmts, finalCtx) ∧
        stmts = Locals.codeStmt code ++ restStmts := by
  unfold Locals.Block.compileOpen at hCompile
  cases hCode : Locals.Expr.compileCode ctx 0 value with
  | none =>
      simp [Locals.Stmt.compile, hCode] at hCompile
  | some code =>
      cases hRest :
          Locals.Block.compileOpen
            (ctx.withLayout (name :: ctx.layout)) { stmts := rest } with
      | none =>
          simp [Locals.Stmt.compile, hCode, hRest] at hCompile
      | some restResult =>
          rcases restResult with ⟨restStmts, restCtx⟩
          simp [Locals.Stmt.compile, hCode, hRest] at hCompile
          rcases hCompile with ⟨hStmts, hFinalCtx⟩
          exact
            ⟨code, restStmts, rfl,
              by simp [hFinalCtx], hStmts.symm⟩

theorem localsBlock_compileOpen_assign_cons_inv
    {ctx finalCtx : Locals.Ctx} {name : Name}
    {value : Locals.Expr 1}
    {rest : List Locals.Stmt} {stmts : List Expressions.Stmt}
    (hCompile :
      Locals.Block.compileOpen ctx
          { stmts := Locals.Stmt.assign name value :: rest } =
        some (stmts, finalCtx)) :
    ∃ depth valueCode swapOp restStmts,
      Locals.Layout.lookupDepth? name ctx.layout = some depth ∧
        Locals.Expr.compileCode ctx 0 value = some valueCode ∧
        Locals.StackOp.swap? depth = some swapOp ∧
        Locals.Block.compileOpen ctx { stmts := rest } =
          some (restStmts, finalCtx) ∧
        stmts =
          Locals.codeStmt
            (valueCode ++
              [Structured.BasicInstr.op swapOp,
                Structured.BasicInstr.op Structured.BasicOp.pop]) ++
            restStmts := by
  unfold Locals.Block.compileOpen at hCompile
  cases hDepth : Locals.Layout.lookupDepth? name ctx.layout with
  | none =>
      simp [Locals.Stmt.compile, hDepth] at hCompile
  | some depth =>
      cases hValue :
          Locals.Expr.compileCode ctx 0 value with
      | none =>
          simp [Locals.Stmt.compile, hDepth, hValue] at hCompile
      | some valueCode =>
          cases hSwap : Locals.StackOp.swap? depth with
          | none =>
              simp [Locals.Stmt.compile, hDepth, hValue, hSwap] at hCompile
          | some swapOp =>
              cases hRest :
                  Locals.Block.compileOpen ctx { stmts := rest } with
              | none =>
                  simp [Locals.Stmt.compile, hDepth, hValue, hSwap, hRest]
                    at hCompile
              | some restResult =>
                  rcases restResult with ⟨restStmts, restCtx⟩
                  simp [Locals.Stmt.compile, hDepth, hValue, hSwap, hRest]
                    at hCompile
                  rcases hCompile with ⟨hStmts, hFinalCtx⟩
                  exact
                    ⟨depth, valueCode, swapOp, restStmts, rfl, rfl,
                      hSwap, by simp [hFinalCtx],
                      hStmts.symm⟩

theorem functionsBlock_toLocals_compileOpen_expr_cons_inv
    {returns : List Name} {ctx finalCtx : Locals.Ctx}
    {expr : Functions.Expr 0} {rest : List Functions.Stmt}
    {stmts : List Expressions.Stmt}
    (hCompile :
      Locals.Block.compileOpen ctx
          (Functions.Block.toLocals returns
            { stmts := Functions.Stmt.expr expr :: rest }) =
        some (stmts, finalCtx)) :
    ∃ code restStmts,
      Locals.Expr.compileCode ctx 0 expr = some code ∧
        Locals.Block.compileOpen ctx
          (Functions.Block.toLocals returns { stmts := rest }) =
          some (restStmts, finalCtx) ∧
        stmts = Locals.codeStmt code ++ restStmts := by
  have hCompile' :
      Locals.Block.compileOpen ctx
          { stmts :=
              Locals.Stmt.expr expr ::
                Functions.StmtList.toLocals returns rest } =
        some (stmts, finalCtx) := by
    simpa [Functions.Block.toLocals, Functions.StmtList.toLocals,
      Functions.Stmt.toLocals] using hCompile
  rcases localsBlock_compileOpen_expr_cons_inv hCompile' with
    ⟨code, restStmts, hCode, hRest, hStmts⟩
  refine ⟨code, restStmts, hCode, ?_, hStmts⟩
  simpa [Functions.Block.toLocals] using hRest

theorem functionsBlock_toLocals_compileOpen_let_cons_inv
    {returns : List Name} {ctx finalCtx : Locals.Ctx}
    {name : Name} {value : Functions.Expr 1}
    {rest : List Functions.Stmt} {stmts : List Expressions.Stmt}
    (hCompile :
      Locals.Block.compileOpen ctx
          (Functions.Block.toLocals returns
            { stmts := Functions.Stmt.let_ name value :: rest }) =
        some (stmts, finalCtx)) :
    ∃ code restStmts,
      Locals.Expr.compileCode ctx 0 value = some code ∧
        Locals.Block.compileOpen (ctx.withLayout (name :: ctx.layout))
          (Functions.Block.toLocals returns { stmts := rest }) =
          some (restStmts, finalCtx) ∧
        stmts = Locals.codeStmt code ++ restStmts := by
  have hCompile' :
      Locals.Block.compileOpen ctx
          { stmts :=
              Locals.Stmt.let_ name value ::
                Functions.StmtList.toLocals returns rest } =
        some (stmts, finalCtx) := by
    simpa [Functions.Block.toLocals, Functions.StmtList.toLocals,
      Functions.Stmt.toLocals] using hCompile
  rcases localsBlock_compileOpen_let_cons_inv hCompile' with
    ⟨code, restStmts, hCode, hRest, hStmts⟩
  refine ⟨code, restStmts, hCode, ?_, hStmts⟩
  simpa [Functions.Block.toLocals] using hRest

theorem functionsBlock_toLocals_compileOpen_assign_cons_inv
    {returns : List Name} {ctx finalCtx : Locals.Ctx}
    {name : Name} {value : Functions.Expr 1}
    {rest : List Functions.Stmt} {stmts : List Expressions.Stmt}
    (hCompile :
      Locals.Block.compileOpen ctx
          (Functions.Block.toLocals returns
            { stmts := Functions.Stmt.assign name value :: rest }) =
        some (stmts, finalCtx)) :
    ∃ depth valueCode swapOp restStmts,
      Locals.Layout.lookupDepth? name ctx.layout = some depth ∧
        Locals.Expr.compileCode ctx 0 value = some valueCode ∧
        Locals.StackOp.swap? depth = some swapOp ∧
        Locals.Block.compileOpen ctx
          (Functions.Block.toLocals returns { stmts := rest }) =
          some (restStmts, finalCtx) ∧
        stmts =
          Locals.codeStmt
            (valueCode ++
              [Structured.BasicInstr.op swapOp,
                Structured.BasicInstr.op Structured.BasicOp.pop]) ++
            restStmts := by
  have hCompile' :
      Locals.Block.compileOpen ctx
          { stmts :=
              Locals.Stmt.assign name value ::
                Functions.StmtList.toLocals returns rest } =
        some (stmts, finalCtx) := by
    simpa [Functions.Block.toLocals, Functions.StmtList.toLocals,
      Functions.Stmt.toLocals] using hCompile
  rcases localsBlock_compileOpen_assign_cons_inv hCompile' with
    ⟨depth, valueCode, swapOp, restStmts, hDepth, hValue, hSwap,
      hRest, hStmts⟩
  refine ⟨depth, valueCode, swapOp, restStmts, hDepth, hValue, hSwap,
    ?_, hStmts⟩
  simpa [Functions.Block.toLocals] using hRest

theorem evmState_with_stack_eq_self
    {state : EvmYul.EVM.State} {stack : OpenExternal.Stack}
    (hStack : state.stack = stack) :
    ({ state with stack := stack } : EvmYul.EVM.State) = state := by
  cases state
  simp at hStack ⊢
  exact hStack.symm

theorem compilerPrimitiveOpenCall?_resume_vars
    {compiler : Objects.Source.State}
    {kind : OpenExternal.CallKind} {values : List Word}
    {call : OpenExternal.OpenCall (Objects.Source.State × List Word)}
    (hCall :
      Reference.SourceBridgeFacts.SourceStateRel.compilerPrimitiveOpenCall?
          compiler kind values =
        some call)
    (response : OpenExternal.CallResponse) :
    (call.resume response).1.vars = compiler.vars := by
  unfold
    Reference.SourceBridgeFacts.SourceStateRel.compilerPrimitiveOpenCall?
      at hCall
  cases hPrimitive :
      OpenExternal.CallKind.primitiveSharedOpenCall?
        compiler.shared kind values with
  | none =>
      simp [hPrimitive] at hCall
  | some primitiveCall =>
      simp [hPrimitive] at hCall
      rcases hCall with rfl
      simp [Locals.Source.State.withShared]

theorem compilerOpenPrimitive_eval_resolves_callKind_ok_inv
    {prim : Objects.Source.PrimitiveSemantics}
    {compiler : Objects.Source.State}
    {op : Structured.BasicOp} {kind : OpenExternal.CallKind}
    {values : List Word}
    {compilerCall :
      OpenExternal.OpenCall (Objects.Source.State × List Word)}
    {trace : OpenExternal.OpenTrace}
    {result : Objects.Source.State × List Word}
    (hKind : OpenExternal.CallKind.ofBasicOp? op = some kind)
    (hCall :
      Reference.SourceBridgeFacts.SourceStateRel.compilerPrimitiveOpenCall?
          compiler kind values =
        some compilerCall)
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.Primitive.eval
          prim op compiler values)
        trace (.ok result)) :
    ∃ response : OpenExternal.CallResponse,
      trace = [{ site := compilerCall.site, response := response }] ∧
        result = compilerCall.resume response := by
  have hSuspend :
      Reference.SourceBridgeFacts.CompilerOpen.Primitive.eval
          prim op compiler values =
        .call
          { site := compilerCall.site
            resume := fun response =>
              .done (.ok (compilerCall.resume response)) } :=
    Reference.SourceBridgeFacts.CompilerOpen.Primitive.eval_suspends_of_basicOp
      hKind hCall
  rw [hSuspend] at hResolve
  cases hResolve with
  | call hTail =>
      cases hTail
      exact ⟨_, rfl, rfl⟩

theorem compilerOpenPrimitive_call_stepAtResult
    {prim : Objects.Source.PrimitiveSemantics}
    {compiler : Objects.Source.State}
    {evmState : EvmYul.EVM.State}
    (hShared : evmState.toSharedState = compiler.shared)
    (kind : OpenExternal.CallKind)
    (operands : OpenExternal.CallOperands)
    (baseStack : OpenExternal.Stack)
    (program : Assembly.Program) (pc : Nat) :
    ∃ compilerCall :
        OpenExternal.OpenCall (Objects.Source.State × List Word),
    ∃ evmCall : OpenExternal.OpenCall EvmYul.EVM.State,
      Reference.SourceBridgeFacts.SourceStateRel.compilerPrimitiveOpenCall?
          compiler kind (kind.args operands).reverse =
        some compilerCall ∧
      OpenExternal.CallKind.evmOpenCall?
          ({ evmState with stack := kind.args operands ++ baseStack }
            : EvmYul.EVM.State) kind =
        some evmCall ∧
      OpenExternal.OpenCallRel
        (fun _ => True)
        (Reference.SourceBridgeFacts.SourceStateRel.CompilerPrimitiveEVMResultRel
          baseStack) compilerCall evmCall ∧
      ∀ response : OpenExternal.CallResponse,
        OpenExternal.OpenResultResolves
          (Reference.SourceBridgeFacts.CompilerOpen.Primitive.eval
            prim kind.toBasicOp compiler (kind.args operands).reverse)
          [{ site := compilerCall.site, response := response }]
          (.ok (compilerCall.resume response)) ∧
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openStepAtResult program pc
            (.prim kind.toBasicOp.toPrimOp)
            ({ evmState with stack := kind.args operands ++ baseStack }
              : EvmYul.EVM.State))
          [{ site := compilerCall.site, response := response }]
          (.ok
            (.running (EvmYul.EVM.State.incrPC
              (evmCall.resume response)))) ∧
        CompilerPrimitiveEVMInstructionResultRel baseStack
          (compilerCall.resume response)
          (.running (EvmYul.EVM.State.incrPC
            (evmCall.resume response))) := by
  rcases
      Reference.SourceBridgeFacts.SourceStateRel.compilerPrimitiveOpenCallRel_evmOpenCall_of_args
        (compiler := compiler) (state := evmState) hShared kind operands
        baseStack with
    ⟨compilerCall, evmCall, hCompilerCall, hEVMCall, hCallRel⟩
  refine ⟨compilerCall, evmCall, hCompilerCall, hEVMCall, hCallRel, ?_⟩
  intro response
  have hSourceSuspend :
    Reference.SourceBridgeFacts.CompilerOpen.Primitive.eval prim
          kind.toBasicOp compiler (kind.args operands).reverse =
        .call
          { site := compilerCall.site
            resume := fun response =>
              .done (.ok (compilerCall.resume response)) } :=
    Reference.SourceBridgeFacts.CompilerOpen.Primitive.eval_suspends_toBasicOp
      kind hCompilerCall
  have hSource :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.Primitive.eval
          prim kind.toBasicOp compiler (kind.args operands).reverse)
        [{ site := compilerCall.site, response := response }]
        (.ok (compilerCall.resume response)) := by
    rw [hSourceSuspend]
    exact OpenExternal.OpenResultResolves.call
      OpenExternal.OpenResultResolves.done
  have hTargetRaw :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openStepAtResult program pc
          (.prim kind.toBasicOp.toPrimOp)
          ({ evmState with stack := kind.args operands ++ baseStack }
            : EvmYul.EVM.State))
        [{ site := evmCall.site, response := response }]
        (.ok
          (.running (EvmYul.EVM.State.incrPC
            (evmCall.resume response)))) :=
    OpenAssembly.Source.openStepAtResult_resolves_prim_call
      (program := program) (pc := pc) (op := kind.toBasicOp.toPrimOp)
      (state := { evmState with stack := kind.args operands ++ baseStack })
      (kind := kind) (call := evmCall)
      (callKind_ofEVMOperation_toBasicOp_toPrimOp kind) hEVMCall response
  have hTarget :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openStepAtResult program pc
          (.prim kind.toBasicOp.toPrimOp)
          ({ evmState with stack := kind.args operands ++ baseStack }
            : EvmYul.EVM.State))
        [{ site := compilerCall.site, response := response }]
        (.ok
          (.running (EvmYul.EVM.State.incrPC
            (evmCall.resume response)))) := by
    simpa [hCallRel.sameSite] using hTargetRaw
  have hResponseRel :
      Reference.SourceBridgeFacts.SourceStateRel.CompilerPrimitiveEVMResultRel
        baseStack (compilerCall.resume response) (evmCall.resume response) :=
    OpenExternal.OpenCallRel.preserves_response hCallRel response trivial
  exact
    ⟨hSource, hTarget,
      CompilerPrimitiveEVMInstructionResultRel.running_incrPC hResponseRel⟩

theorem compilerOpenPrimitive_no_callCreate_stepAtResult
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {compiler : Objects.Source.State}
    {evmState : EvmYul.EVM.State}
    (hShared : evmState.toSharedState = compiler.shared)
    (op : Structured.BasicOp)
    (hNoCallCreate : op.toPrimOp.isCallCreate = false)
    (values : List Word)
    (baseStack : OpenExternal.Stack)
    (program : Assembly.Program) (pc : Nat)
    {sharedAfter : EvmYul.SharedState .EVM}
    {valuesAfter : List Word}
    (hEval :
      prim.eval op compiler.shared values = .ok (sharedAfter, valuesAfter)) :
    ∃ evmAfter : EvmYul.EVM.State,
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.Primitive.eval
          prim op compiler values)
        [] (.ok (compiler.withShared sharedAfter, valuesAfter)) ∧
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openStepAtResult program pc (.prim op.toPrimOp)
          ({ evmState with stack := values.reverse ++ baseStack }
            : EvmYul.EVM.State))
        [] (.ok (.running evmAfter)) ∧
      CompilerPrimitiveEVMInstructionResultRel baseStack
        (compiler.withShared sharedAfter, valuesAfter)
        (.running evmAfter) := by
  let state : EvmYul.EVM.State :=
    { evmState with stack := values.reverse ++ baseStack }
  have hStateShared : state.toSharedState = compiler.shared := by
    simpa [state] using hShared
  have hStateStack : state.stack = values.reverse ++ baseStack := by
    simp [state]
  rcases
      hPrim.eval_step_exists
        (op := op) (shared := compiler.shared)
        (shared' := sharedAfter) (values := values)
        (values' := valuesAfter) (evm := state)
        (baseStack := baseStack) hEval hStateShared hStateStack with
    ⟨evmAfter, hStep, hAfterShared, hAfterStack⟩
  have hSource :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.Primitive.eval
          prim op compiler values)
        [] (.ok (compiler.withShared sharedAfter, valuesAfter)) :=
    Reference.SourceBridgeFacts.CompilerOpen.Primitive.eval_resolves_closed_ok_of_not_callKind
      (Reference.SourceBridgeFacts.CompilerOpen.Primitive.callKind_none_of_no_callCreate
        hNoCallCreate)
      hEval
  have hTargetStep :
      Assembly.Source.stepAtResult program pc (.prim op.toPrimOp) state =
        .ok (.running evmAfter) := by
    have hTargetInstr :
        Assembly.Target.stepInstr
          (Assembly.TargetInstr.prim op.toPrimOp) state =
          .ok evmAfter := by
      simpa [Structured.BasicOp.step] using hStep
    simp [Assembly.Source.stepAtResult, Assembly.Source.stepAt,
      hTargetInstr, basicOp_toPrimOp_haltKind?_none op]
  have hTarget :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openStepAtResult program pc (.prim op.toPrimOp)
          ({ evmState with stack := values.reverse ++ baseStack }
            : EvmYul.EVM.State))
        [] (.ok (.running evmAfter)) := by
    simpa [state] using
      OpenAssembly.Source.openStepAtResult_resolves_closed_of_prim_no_callCreate
        (program := program) (pc := pc) (op := op.toPrimOp)
          (state := state) hNoCallCreate hTargetStep
  have hRel :
      Reference.SourceBridgeFacts.SourceStateRel.CompilerPrimitiveEVMResultRel
        baseStack (compiler.withShared sharedAfter, valuesAfter) evmAfter := by
    exact
      ⟨by simpa [Locals.Source.State.withShared] using hAfterShared,
        hAfterStack⟩
  exact ⟨evmAfter, hSource, hTarget, hRel⟩

theorem compilerOpenPrimitive_no_callCreate_stepAtResult_pc
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {compiler : Objects.Source.State}
    {evmState : EvmYul.EVM.State}
    (hShared : evmState.toSharedState = compiler.shared)
    (op : Structured.BasicOp)
    (hNoCallCreate : op.toPrimOp.isCallCreate = false)
    (values : List Word)
    (baseStack : OpenExternal.Stack)
    (program : Assembly.Program) (pc : Nat)
    {sharedAfter : EvmYul.SharedState .EVM}
    {valuesAfter : List Word}
    (hEval :
      prim.eval op compiler.shared values = .ok (sharedAfter, valuesAfter)) :
    ∃ evmAfter : EvmYul.EVM.State,
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.Primitive.eval
          prim op compiler values)
        [] (.ok (compiler.withShared sharedAfter, valuesAfter)) ∧
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openStepAtResult program pc (.prim op.toPrimOp)
          ({ evmState with stack := values.reverse ++ baseStack }
            : EvmYul.EVM.State))
        [] (.ok (.running evmAfter)) ∧
      CompilerPrimitiveEVMInstructionResultRel baseStack
        (compiler.withShared sharedAfter, valuesAfter)
        (.running evmAfter) ∧
      evmAfter.pc =
        ({ evmState with stack := values.reverse ++ baseStack }
          : EvmYul.EVM.State).pc + EvmYul.UInt256.ofNat 1 := by
  let state : EvmYul.EVM.State :=
    { evmState with stack := values.reverse ++ baseStack }
  have hStateShared : state.toSharedState = compiler.shared := by
    simpa [state] using hShared
  have hStateStack : state.stack = values.reverse ++ baseStack := by
    simp [state]
  rcases
      hPrim.eval_step_exists
        (op := op) (shared := compiler.shared)
        (shared' := sharedAfter) (values := values)
        (values' := valuesAfter) (evm := state)
        (baseStack := baseStack) hEval hStateShared hStateStack with
    ⟨evmAfter, hStep, hAfterShared, hAfterStack⟩
  have hSource :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.Primitive.eval
          prim op compiler values)
        [] (.ok (compiler.withShared sharedAfter, valuesAfter)) :=
    Reference.SourceBridgeFacts.CompilerOpen.Primitive.eval_resolves_closed_ok_of_not_callKind
      (Reference.SourceBridgeFacts.CompilerOpen.Primitive.callKind_none_of_no_callCreate
        hNoCallCreate)
      hEval
  have hTargetStep :
      Assembly.Source.stepAtResult program pc (.prim op.toPrimOp) state =
        .ok (.running evmAfter) := by
    have hTargetInstr :
        Assembly.Target.stepInstr
          (Assembly.TargetInstr.prim op.toPrimOp) state =
          .ok evmAfter := by
      simpa [Structured.BasicOp.step] using hStep
    simp [Assembly.Source.stepAtResult, Assembly.Source.stepAt,
      hTargetInstr, basicOp_toPrimOp_haltKind?_none op]
  have hTarget :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openStepAtResult program pc (.prim op.toPrimOp)
          ({ evmState with stack := values.reverse ++ baseStack }
            : EvmYul.EVM.State))
        [] (.ok (.running evmAfter)) := by
    simpa [state] using
      OpenAssembly.Source.openStepAtResult_resolves_closed_of_prim_no_callCreate
        (program := program) (pc := pc) (op := op.toPrimOp)
        (state := state) hNoCallCreate hTargetStep
  have hRel :
      Reference.SourceBridgeFacts.SourceStateRel.CompilerPrimitiveEVMResultRel
        baseStack (compiler.withShared sharedAfter, valuesAfter) evmAfter := by
    exact
      ⟨by simpa [Locals.Source.State.withShared] using hAfterShared,
        hAfterStack⟩
  have hPc :
      evmAfter.pc = state.pc + EvmYul.UInt256.ofNat 1 :=
    basicOp_no_callCreate_step_pc hNoCallCreate hStep
  exact ⟨evmAfter, hSource, hTarget, hRel, by simpa [state] using hPc⟩

theorem compilerOpenPrimitive_no_callCreate_openRunNResult_continue
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {compiler : Objects.Source.State}
    {evmState : EvmYul.EVM.State}
    (hShared : evmState.toSharedState = compiler.shared)
    (op : Structured.BasicOp)
    (hNoCallCreate : op.toPrimOp.isCallCreate = false)
    (values : List Word)
    (baseStack : OpenExternal.Stack)
    (program : Assembly.Program) (pc fuel : Nat)
    (hAt :
      Assembly.Program.instrAtPc program
          (({ evmState with stack := values.reverse ++ baseStack }
            : EvmYul.EVM.State).pc.toNat) =
        some (pc, Assembly.Instr.prim op.toPrimOp))
    {sharedAfter : EvmYul.SharedState .EVM}
    {valuesAfter : List Word}
    (hEval :
      prim.eval op compiler.shared values = .ok (sharedAfter, valuesAfter)) :
    ∃ evmAfter : EvmYul.EVM.State,
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.Primitive.eval
          prim op compiler values)
        [] (.ok (compiler.withShared sharedAfter, valuesAfter)) ∧
      CompilerPrimitiveEVMInstructionResultRel baseStack
        (compiler.withShared sharedAfter, valuesAfter)
        (.running evmAfter) ∧
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program fuel evmAfter)
          tailTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program (fuel + 1)
            ({ evmState with stack := values.reverse ++ baseStack }
              : EvmYul.EVM.State))
          tailTrace result := by
  rcases
      compilerOpenPrimitive_no_callCreate_stepAtResult
        (prim := prim) hPrim (compiler := compiler)
        (evmState := evmState) hShared op hNoCallCreate values baseStack
        program pc hEval with
    ⟨evmAfter, hSource, hTargetStep, hRel⟩
  refine ⟨evmAfter, hSource, hRel, ?_⟩
  intro tailTrace result hRest
  have hTargetRun :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openRunNResult program (fuel + 1)
          ({ evmState with stack := values.reverse ++ baseStack }
            : EvmYul.EVM.State))
        ([] ++ tailTrace) result :=
    OpenAssembly.Source.openRunNResult_current_stepAt_running_continue
      (program := program) (fuel := fuel)
      (state := ({ evmState with stack := values.reverse ++ baseStack }
        : EvmYul.EVM.State))
      (mid := evmAfter) (pc := pc) (instr := .prim op.toPrimOp)
      hAt hTargetStep hRest
  simpa using hTargetRun

theorem compilerOpenPrimitive_call_openRunNResult_continue
    {prim : Objects.Source.PrimitiveSemantics}
    {compiler : Objects.Source.State}
    {evmState : EvmYul.EVM.State}
    (hShared : evmState.toSharedState = compiler.shared)
    (kind : OpenExternal.CallKind)
    (operands : OpenExternal.CallOperands)
    (baseStack : OpenExternal.Stack)
    (program : Assembly.Program) (pc fuel : Nat)
    (hAt :
      Assembly.Program.instrAtPc program
          (({ evmState with stack := kind.args operands ++ baseStack }
            : EvmYul.EVM.State).pc.toNat) =
        some (pc, Assembly.Instr.prim kind.toBasicOp.toPrimOp)) :
    ∃ compilerCall :
        OpenExternal.OpenCall (Objects.Source.State × List Word),
    ∃ evmCall : OpenExternal.OpenCall EvmYul.EVM.State,
      Reference.SourceBridgeFacts.SourceStateRel.compilerPrimitiveOpenCall?
          compiler kind (kind.args operands).reverse =
        some compilerCall ∧
      OpenExternal.CallKind.evmOpenCall?
          ({ evmState with stack := kind.args operands ++ baseStack }
            : EvmYul.EVM.State) kind =
        some evmCall ∧
      OpenExternal.OpenCallRel
        (fun _ => True)
        (Reference.SourceBridgeFacts.SourceStateRel.CompilerPrimitiveEVMResultRel
          baseStack) compilerCall evmCall ∧
      ∀ (response : OpenExternal.CallResponse)
        {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program fuel
            (EvmYul.EVM.State.incrPC (evmCall.resume response)))
          tailTrace result →
        OpenExternal.OpenResultResolves
          (Reference.SourceBridgeFacts.CompilerOpen.Primitive.eval
            prim kind.toBasicOp compiler (kind.args operands).reverse)
          [{ site := compilerCall.site, response := response }]
          (.ok (compilerCall.resume response)) ∧
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program (fuel + 1)
            ({ evmState with stack := kind.args operands ++ baseStack }
              : EvmYul.EVM.State))
          ({ site := compilerCall.site, response := response } :: tailTrace)
          result ∧
        CompilerPrimitiveEVMInstructionResultRel baseStack
          (compilerCall.resume response)
          (.running (EvmYul.EVM.State.incrPC
            (evmCall.resume response))) := by
  rcases
      compilerOpenPrimitive_call_stepAtResult
        (prim := prim) (compiler := compiler) (evmState := evmState)
        hShared kind operands baseStack program pc with
    ⟨compilerCall, evmCall, hCompilerCall, hEVMCall, hCallRel, hStep⟩
  refine ⟨compilerCall, evmCall, hCompilerCall, hEVMCall, hCallRel, ?_⟩
  intro response tailTrace result hRest
  rcases hStep response with ⟨hSource, _hStepTarget, hResultRel⟩
  have hTargetRaw :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openRunNResult program (fuel + 1)
          ({ evmState with stack := kind.args operands ++ baseStack }
            : EvmYul.EVM.State))
        ({ site := evmCall.site, response := response } :: tailTrace)
        result :=
    OpenAssembly.Source.openRunNResult_current_prim_call_continue
      (program := program)
      (state := ({ evmState with stack := kind.args operands ++ baseStack }
        : EvmYul.EVM.State))
      (fuel := fuel) (pc := pc) (op := kind.toBasicOp.toPrimOp)
      (kind := kind) (call := evmCall)
      hAt (callKind_ofEVMOperation_toBasicOp_toPrimOp kind) hEVMCall
      response hRest
  have hTarget :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openRunNResult program (fuel + 1)
          ({ evmState with stack := kind.args operands ++ baseStack }
            : EvmYul.EVM.State))
        ({ site := compilerCall.site, response := response } :: tailTrace)
        result := by
    simpa [hCallRel.sameSite] using hTargetRaw
  exact ⟨hSource, hTarget, hResultRel⟩

theorem compilerOpenPrimitive_callKind_openRunNResult_continue
    {prim : Objects.Source.PrimitiveSemantics}
    {compiler : Objects.Source.State}
    {evmState : EvmYul.EVM.State}
    (hShared : evmState.toSharedState = compiler.shared)
    {op : Structured.BasicOp} {kind : OpenExternal.CallKind}
    (hKind : OpenExternal.CallKind.ofBasicOp? op = some kind)
    (values : List Word)
    (hValuesLen :
      values.length = Expressions.Structured.BasicOp.inputs op)
    (baseStack : OpenExternal.Stack)
    (program : Assembly.Program) (pc fuel : Nat)
    (hAt :
      Assembly.Program.instrAtPc program
          (({ evmState with stack := values.reverse ++ baseStack }
            : EvmYul.EVM.State).pc.toNat) =
        some (pc, Assembly.Instr.prim op.toPrimOp)) :
    ∃ operands : OpenExternal.CallOperands,
    ∃ compilerCall :
        OpenExternal.OpenCall (Objects.Source.State × List Word),
    ∃ evmCall : OpenExternal.OpenCall EvmYul.EVM.State,
      values = (kind.args operands).reverse ∧
      Reference.SourceBridgeFacts.SourceStateRel.compilerPrimitiveOpenCall?
          compiler kind values =
        some compilerCall ∧
      OpenExternal.CallKind.evmOpenCall?
          ({ evmState with stack := values.reverse ++ baseStack }
            : EvmYul.EVM.State) kind =
        some evmCall ∧
      OpenExternal.OpenCallRel
        (fun _ => True)
        (Reference.SourceBridgeFacts.SourceStateRel.CompilerPrimitiveEVMResultRel
          baseStack) compilerCall evmCall ∧
      ∀ (response : OpenExternal.CallResponse)
        {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program fuel
            (EvmYul.EVM.State.incrPC (evmCall.resume response)))
          tailTrace result →
        OpenExternal.OpenResultResolves
          (Reference.SourceBridgeFacts.CompilerOpen.Primitive.eval
            prim op compiler values)
          [{ site := compilerCall.site, response := response }]
          (.ok (compilerCall.resume response)) ∧
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program (fuel + 1)
            ({ evmState with stack := values.reverse ++ baseStack }
              : EvmYul.EVM.State))
          ({ site := compilerCall.site, response := response } :: tailTrace)
          result ∧
        CompilerPrimitiveEVMInstructionResultRel baseStack
          (compilerCall.resume response)
          (.running (EvmYul.EVM.State.incrPC
            (evmCall.resume response))) := by
  have hOp : op = kind.toBasicOp :=
    basicOp_eq_toBasicOp_of_callKind hKind
  subst op
  have hLen : values.length = kind.inputArity := by
    simpa using hValuesLen
  rcases
      OpenExternal.CallKind.exists_operands_of_reverse_args_length
        kind hLen with
    ⟨operands, hValues⟩
  subst values
  have hAtCall :
      Assembly.Program.instrAtPc program
          (({ evmState with stack := kind.args operands ++ baseStack }
            : EvmYul.EVM.State).pc.toNat) =
        some (pc, Assembly.Instr.prim kind.toBasicOp.toPrimOp) := by
    simpa [List.reverse_reverse] using hAt
  rcases
      compilerOpenPrimitive_call_openRunNResult_continue
        (prim := prim) (compiler := compiler) (evmState := evmState)
        hShared kind operands baseStack program pc fuel hAtCall with
    ⟨compilerCall, evmCall, hCompilerCall, hEVMCall, hCallRel, hCont⟩
  refine
    ⟨operands, compilerCall, evmCall, rfl, ?_, ?_, hCallRel, ?_⟩
  · simpa using hCompilerCall
  · simpa [List.reverse_reverse] using hEVMCall
  · intro response tailTrace result hRest
    rcases hCont response hRest with
      ⟨hSource, hTarget, hResultRel⟩
    exact
      ⟨hSource, by simpa [List.reverse_reverse] using hTarget,
        hResultRel⟩

theorem compilerOpenPrimitive_no_callCreate_state_openRunNResult_continue
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {compiler : Objects.Source.State}
    {state : EvmYul.EVM.State}
    (hShared : state.toSharedState = compiler.shared)
    (op : Structured.BasicOp)
    (hNoCallCreate : op.toPrimOp.isCallCreate = false)
    (values : List Word)
    (baseStack : OpenExternal.Stack)
    (hStack : state.stack = values.reverse ++ baseStack)
    (program : Assembly.Program) (pc fuel : Nat)
    (hAt :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some (pc, Assembly.Instr.prim op.toPrimOp))
    {sharedAfter : EvmYul.SharedState .EVM}
    {valuesAfter : List Word}
    (hEval :
      prim.eval op compiler.shared values = .ok (sharedAfter, valuesAfter)) :
    ∃ evmAfter : EvmYul.EVM.State,
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.Primitive.eval
          prim op compiler values)
        [] (.ok (compiler.withShared sharedAfter, valuesAfter)) ∧
      CompilerPrimitiveEVMInstructionResultRel baseStack
        (compiler.withShared sharedAfter, valuesAfter)
        (.running evmAfter) ∧
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program fuel evmAfter)
          tailTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program (fuel + 1) state)
          tailTrace result := by
  have hStateEq :
      ({ state with stack := values.reverse ++ baseStack }
        : EvmYul.EVM.State) = state :=
    evmState_with_stack_eq_self hStack
  have hAt' :
      Assembly.Program.instrAtPc program
          (({ state with stack := values.reverse ++ baseStack }
            : EvmYul.EVM.State).pc.toNat) =
        some (pc, Assembly.Instr.prim op.toPrimOp) := by
    simpa [hStateEq] using hAt
  rcases
      compilerOpenPrimitive_no_callCreate_openRunNResult_continue
        (prim := prim) hPrim (compiler := compiler)
        (evmState := state) hShared op hNoCallCreate values baseStack
        program pc fuel hAt' hEval with
    ⟨evmAfter, hSource, hRel, hCont⟩
  refine ⟨evmAfter, hSource, hRel, ?_⟩
  intro tailTrace result hRest
  simpa [hStateEq] using hCont hRest

theorem compilerOpenPrimitive_callKind_state_openRunNResult_continue
    {prim : Objects.Source.PrimitiveSemantics}
    {compiler : Objects.Source.State}
    {state : EvmYul.EVM.State}
    (hShared : state.toSharedState = compiler.shared)
    {op : Structured.BasicOp} {kind : OpenExternal.CallKind}
    (hKind : OpenExternal.CallKind.ofBasicOp? op = some kind)
    (values : List Word)
    (hValuesLen :
      values.length = Expressions.Structured.BasicOp.inputs op)
    (baseStack : OpenExternal.Stack)
    (hStack : state.stack = values.reverse ++ baseStack)
    (program : Assembly.Program) (pc fuel : Nat)
    (hAt :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some (pc, Assembly.Instr.prim op.toPrimOp)) :
    ∃ operands : OpenExternal.CallOperands,
    ∃ compilerCall :
        OpenExternal.OpenCall (Objects.Source.State × List Word),
    ∃ evmCall : OpenExternal.OpenCall EvmYul.EVM.State,
      values = (kind.args operands).reverse ∧
      Reference.SourceBridgeFacts.SourceStateRel.compilerPrimitiveOpenCall?
          compiler kind values =
        some compilerCall ∧
      OpenExternal.CallKind.evmOpenCall? state kind =
        some evmCall ∧
      OpenExternal.OpenCallRel
        (fun _ => True)
        (Reference.SourceBridgeFacts.SourceStateRel.CompilerPrimitiveEVMResultRel
          baseStack) compilerCall evmCall ∧
      ∀ (response : OpenExternal.CallResponse)
        {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program fuel
            (EvmYul.EVM.State.incrPC (evmCall.resume response)))
          tailTrace result →
        OpenExternal.OpenResultResolves
          (Reference.SourceBridgeFacts.CompilerOpen.Primitive.eval
            prim op compiler values)
          [{ site := compilerCall.site, response := response }]
          (.ok (compilerCall.resume response)) ∧
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program (fuel + 1) state)
          ({ site := compilerCall.site, response := response } :: tailTrace)
          result ∧
        CompilerPrimitiveEVMInstructionResultRel baseStack
          (compilerCall.resume response)
          (.running (EvmYul.EVM.State.incrPC
            (evmCall.resume response))) := by
  have hStateEq :
      ({ state with stack := values.reverse ++ baseStack }
        : EvmYul.EVM.State) = state :=
    evmState_with_stack_eq_self hStack
  have hAt' :
      Assembly.Program.instrAtPc program
          (({ state with stack := values.reverse ++ baseStack }
            : EvmYul.EVM.State).pc.toNat) =
        some (pc, Assembly.Instr.prim op.toPrimOp) := by
    simpa [hStateEq] using hAt
  rcases
      compilerOpenPrimitive_callKind_openRunNResult_continue
        (prim := prim) (compiler := compiler) (evmState := state)
        hShared hKind values hValuesLen baseStack program pc fuel hAt' with
    ⟨operands, compilerCall, evmCall, hValues, hCompilerCall,
      hEVMCall, hCallRel, hCont⟩
  refine
    ⟨operands, compilerCall, evmCall, hValues, hCompilerCall, ?_,
      hCallRel, ?_⟩
  · simpa [hStateEq] using hEVMCall
  · intro response tailTrace result hRest
    rcases hCont response hRest with
      ⟨hSource, hTarget, hResultRel⟩
    exact ⟨hSource, by simpa [hStateEq] using hTarget, hResultRel⟩

theorem compilerOpenPrimitive_no_callCreate_stackPrefix_openRunNResult_continue
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {layout : List Name}
    {compiler : Objects.Source.State}
    {state : EvmYul.EVM.State}
    (op : Structured.BasicOp)
    (hNoCallCreate : op.toPrimOp.isCallCreate = false)
    (values : List Word)
    (stackPrefix : List Word)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler
        (values.reverse ++ stackPrefix) state)
    (program : Assembly.Program) (pc fuel : Nat)
    (hAt :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some (pc, Assembly.Instr.prim op.toPrimOp))
    {sharedAfter : EvmYul.SharedState .EVM}
    {valuesAfter : List Word}
    (hEval :
      prim.eval op compiler.shared values = .ok (sharedAfter, valuesAfter)) :
    ∃ evmAfter : EvmYul.EVM.State,
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.Primitive.eval
          prim op compiler values)
        [] (.ok (compiler.withShared sharedAfter, valuesAfter)) ∧
      Locals.SourceLowering.StackPrefixRel layout
        (compiler.withShared sharedAfter) (valuesAfter.reverse ++ stackPrefix)
        evmAfter ∧
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program fuel evmAfter)
          tailTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program (fuel + 1) state)
          tailTrace result := by
  rcases hPrefixRel with
    ⟨hShared, storeBase, hStack, hStoreRel⟩
  have hStackState : state.stack = values.reverse ++
      (stackPrefix ++ storeBase) := by
    rw [hStack]
    simp [List.append_assoc]
  rcases
      compilerOpenPrimitive_no_callCreate_state_openRunNResult_continue
        (prim := prim) hPrim (compiler := compiler) (state := state)
        hShared op hNoCallCreate values (stackPrefix ++ storeBase)
        hStackState program pc fuel hAt hEval with
    ⟨evmAfter, hSource, hResultRel, hCont⟩
  have hAfterPrefix :
      Locals.SourceLowering.StackPrefixRel layout
        (compiler.withShared sharedAfter) (valuesAfter.reverse ++ stackPrefix)
        evmAfter := by
    rcases hResultRel with ⟨hAfterShared, hAfterStack⟩
    refine ⟨?_, storeBase, ?_, ?_⟩
    · simpa [Locals.Source.State.withShared] using hAfterShared
    · rw [hAfterStack]
      simp [List.append_assoc]
    · simpa [Locals.Source.State.withShared] using hStoreRel
  exact ⟨evmAfter, hSource, hAfterPrefix, hCont⟩

theorem compilerOpenPrimitive_no_callCreate_stackPrefix_openRunNResult_continue_pc
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {layout : List Name}
    {compiler : Objects.Source.State}
    {state : EvmYul.EVM.State}
    (op : Structured.BasicOp)
    (hNoCallCreate : op.toPrimOp.isCallCreate = false)
    (values : List Word)
    (stackPrefix : List Word)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler
        (values.reverse ++ stackPrefix) state)
    (program : Assembly.Program) (pc fuel : Nat)
    (hAt :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some (pc, Assembly.Instr.prim op.toPrimOp))
    {sharedAfter : EvmYul.SharedState .EVM}
    {valuesAfter : List Word}
    (hEval :
      prim.eval op compiler.shared values = .ok (sharedAfter, valuesAfter)) :
    ∃ evmAfter : EvmYul.EVM.State,
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.Primitive.eval
          prim op compiler values)
        [] (.ok (compiler.withShared sharedAfter, valuesAfter)) ∧
      Locals.SourceLowering.StackPrefixRel layout
        (compiler.withShared sharedAfter) (valuesAfter.reverse ++ stackPrefix)
        evmAfter ∧
      evmAfter.pc = state.pc + EvmYul.UInt256.ofNat 1 ∧
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program fuel evmAfter)
          tailTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program (fuel + 1) state)
          tailTrace result := by
  rcases hPrefixRel with
    ⟨hShared, storeBase, hStack, hStoreRel⟩
  have hStackState : state.stack = values.reverse ++
      (stackPrefix ++ storeBase) := by
    rw [hStack]
    simp [List.append_assoc]
  have hStateEq :
      ({ state with stack := values.reverse ++ (stackPrefix ++ storeBase) }
        : EvmYul.EVM.State) = state :=
    evmState_with_stack_eq_self hStackState
  rcases
      compilerOpenPrimitive_no_callCreate_stepAtResult_pc
        (prim := prim) hPrim (compiler := compiler) (evmState := state)
        hShared op hNoCallCreate values (stackPrefix ++ storeBase)
        program pc hEval with
    ⟨evmAfter, hSource, hTargetStep, hResultRel, hPc⟩
  have hAfterPrefix :
      Locals.SourceLowering.StackPrefixRel layout
        (compiler.withShared sharedAfter) (valuesAfter.reverse ++ stackPrefix)
        evmAfter := by
    rcases hResultRel with ⟨hAfterShared, hAfterStack⟩
    refine ⟨?_, storeBase, ?_, ?_⟩
    · simpa [Locals.Source.State.withShared] using hAfterShared
    · rw [hAfterStack]
      simp [List.append_assoc]
    · simpa [Locals.Source.State.withShared] using hStoreRel
  refine ⟨evmAfter, hSource, hAfterPrefix, ?_, ?_⟩
  · simpa [hStateEq] using hPc
  · intro tailTrace result hRest
    have hTargetStepState :
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openStepAtResult program pc
            (.prim op.toPrimOp) state)
          [] (.ok (.running evmAfter)) := by
      simpa [hStateEq] using hTargetStep
    simpa using
      OpenAssembly.Source.openRunNResult_current_stepAt_running_continue
        (program := program) (fuel := fuel) (state := state)
        (mid := evmAfter) (pc := pc) (instr := .prim op.toPrimOp)
        hAt hTargetStepState hRest

theorem compilerOpenPrimitive_callKind_stackPrefix_openRunNResult_continue
    {prim : Objects.Source.PrimitiveSemantics}
    {layout : List Name}
    {compiler : Objects.Source.State}
    {state : EvmYul.EVM.State}
    {op : Structured.BasicOp} {kind : OpenExternal.CallKind}
    (hKind : OpenExternal.CallKind.ofBasicOp? op = some kind)
    (values : List Word)
    (hValuesLen :
      values.length = Expressions.Structured.BasicOp.inputs op)
    (stackPrefix : List Word)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler
        (values.reverse ++ stackPrefix) state)
    (program : Assembly.Program) (pc fuel : Nat)
    (hAt :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some (pc, Assembly.Instr.prim op.toPrimOp)) :
    ∃ operands : OpenExternal.CallOperands,
    ∃ compilerCall :
        OpenExternal.OpenCall (Objects.Source.State × List Word),
    ∃ evmCall : OpenExternal.OpenCall EvmYul.EVM.State,
      values = (kind.args operands).reverse ∧
      Reference.SourceBridgeFacts.SourceStateRel.compilerPrimitiveOpenCall?
          compiler kind values =
        some compilerCall ∧
      OpenExternal.CallKind.evmOpenCall? state kind =
        some evmCall ∧
      (∀ response : OpenExternal.CallResponse,
        Locals.SourceLowering.StackPrefixRel layout
          (compilerCall.resume response).1
          ((compilerCall.resume response).2.reverse ++ stackPrefix)
          (EvmYul.EVM.State.incrPC (evmCall.resume response))) ∧
      ∀ (response : OpenExternal.CallResponse)
        {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program fuel
            (EvmYul.EVM.State.incrPC (evmCall.resume response)))
          tailTrace result →
        OpenExternal.OpenResultResolves
          (Reference.SourceBridgeFacts.CompilerOpen.Primitive.eval
            prim op compiler values)
          [{ site := compilerCall.site, response := response }]
          (.ok (compilerCall.resume response)) ∧
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program (fuel + 1) state)
          ({ site := compilerCall.site, response := response } :: tailTrace)
          result := by
  rcases hPrefixRel with
    ⟨hShared, storeBase, hStack, hStoreRel⟩
  have hStackState : state.stack = values.reverse ++
      (stackPrefix ++ storeBase) := by
    rw [hStack]
    simp [List.append_assoc]
  rcases
      compilerOpenPrimitive_callKind_state_openRunNResult_continue
        (prim := prim) (compiler := compiler) (state := state)
        hShared hKind values hValuesLen (stackPrefix ++ storeBase)
        hStackState program pc fuel hAt with
    ⟨operands, compilerCall, evmCall, hValues, hCompilerCall,
      hEVMCall, hCallRel, hCont⟩
  have hResponsePrefix :
      ∀ response : OpenExternal.CallResponse,
        Locals.SourceLowering.StackPrefixRel layout
          (compilerCall.resume response).1
          ((compilerCall.resume response).2.reverse ++ stackPrefix)
          (EvmYul.EVM.State.incrPC (evmCall.resume response)) := by
    intro response
    have hResponseRel :
        Reference.SourceBridgeFacts.SourceStateRel.CompilerPrimitiveEVMResultRel
          (stackPrefix ++ storeBase) (compilerCall.resume response)
          (evmCall.resume response) :=
      OpenExternal.OpenCallRel.preserves_response hCallRel response trivial
    rcases hResponseRel with ⟨hResponseShared, hResponseStack⟩
    have hVars :
        (compilerCall.resume response).1.vars = compiler.vars :=
      compilerPrimitiveOpenCall?_resume_vars hCompilerCall response
    refine ⟨?_, storeBase, ?_, ?_⟩
    · simpa [EvmYul.EVM.State.incrPC] using hResponseShared
    · simpa [EvmYul.EVM.State.incrPC, List.append_assoc] using
        hResponseStack
    · simpa [hVars] using hStoreRel
  refine
    ⟨operands, compilerCall, evmCall, hValues, hCompilerCall, hEVMCall,
      hResponsePrefix, ?_⟩
  intro response tailTrace result hRest
  rcases hCont response hRest with
    ⟨hSource, hTarget, _hResultRel⟩
  exact ⟨hSource, hTarget⟩

theorem compilerOpenPrimitive_stackPrefix_openRunNResult_continue_of_resolves_ok
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {layout : List Name}
    {compiler compilerAfter : Objects.Source.State}
    {state : EvmYul.EVM.State}
    (op : Structured.BasicOp)
    (hSupported :
      op.toPrimOp.isCallCreate = false ∨
        ∃ kind : OpenExternal.CallKind,
          OpenExternal.CallKind.ofBasicOp? op = some kind)
    (values : List Word)
    (hValuesLen :
      values.length = Expressions.Structured.BasicOp.inputs op)
    (stackPrefix : List Word)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler
        (values.reverse ++ stackPrefix) state)
    (program : Assembly.Program) (pc fuel : Nat)
    (hAt :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some (pc, Assembly.Instr.prim op.toPrimOp))
    {valuesAfter : List Word}
    {trace : OpenExternal.OpenTrace}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.Primitive.eval
          prim op compiler values)
        trace (.ok (compilerAfter, valuesAfter))) :
    ∃ evmAfter : EvmYul.EVM.State,
      Locals.SourceLowering.StackPrefixRel layout compilerAfter
        (valuesAfter.reverse ++ stackPrefix) evmAfter ∧
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program fuel evmAfter)
          tailTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program (fuel + 1) state)
          (trace ++ tailTrace) result := by
  cases hKind : OpenExternal.CallKind.ofBasicOp? op with
  | none =>
      have hNoCallCreate :
          op.toPrimOp.isCallCreate = false := by
        rcases hSupported with hNoCallCreate | ⟨kind, hSome⟩
        · exact hNoCallCreate
        · rw [hKind] at hSome
          cases hSome
      rw [Reference.SourceBridgeFacts.CompilerOpen.Primitive.eval_of_not_callKind
        hKind] at hResolve
      cases hEval : prim.eval op compiler.shared values with
      | error err =>
          simp [hEval] at hResolve
          cases hResolve
      | ok primResult =>
          rcases primResult with ⟨sharedAfter, valuesAfter'⟩
          simp [hEval] at hResolve
          cases hResolve
          rcases
              compilerOpenPrimitive_no_callCreate_stackPrefix_openRunNResult_continue
                (prim := prim) hPrim (layout := layout)
                (compiler := compiler) (state := state)
                op hNoCallCreate values stackPrefix hPrefixRel
                program pc fuel hAt hEval with
            ⟨evmAfter, _hSource, hAfterPrefix, hCont⟩
          refine ⟨evmAfter, hAfterPrefix, ?_⟩
          intro tailTrace result hRest
          simpa using hCont hRest
  | some kind =>
      rcases
          compilerOpenPrimitive_callKind_stackPrefix_openRunNResult_continue
            (prim := prim) (layout := layout) (compiler := compiler)
            (state := state) hKind values hValuesLen stackPrefix
            hPrefixRel program pc fuel hAt with
        ⟨operands, compilerCall, evmCall, hValues, hCompilerCall,
          _hEVMCall, hResponsePrefix, hCont⟩
      rcases
          compilerOpenPrimitive_eval_resolves_callKind_ok_inv
            (prim := prim) (compiler := compiler) hKind hCompilerCall
            hResolve with
        ⟨response, hTrace, hResult⟩
      have hCompilerAfter :
          compilerAfter = (compilerCall.resume response).1 := by
        simpa using congrArg Prod.fst hResult
      have hValuesAfter :
          valuesAfter = (compilerCall.resume response).2 := by
        simpa using congrArg Prod.snd hResult
      refine
        ⟨EvmYul.EVM.State.incrPC (evmCall.resume response),
          ?_, ?_⟩
      · simpa [hCompilerAfter, hValuesAfter] using
          hResponsePrefix response
      intro tailTrace result hRest
      rcases hCont response hRest with
        ⟨_hSource, hTarget⟩
      simpa [hTrace] using hTarget

theorem compilerOpenPrimitive_stackPrefix_openRunNResult_continue_pc_of_resolves_ok
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {layout : List Name}
    {compiler compilerAfter : Objects.Source.State}
    {state : EvmYul.EVM.State}
    (op : Structured.BasicOp)
    (hSupported :
      op.toPrimOp.isCallCreate = false ∨
        ∃ kind : OpenExternal.CallKind,
          OpenExternal.CallKind.ofBasicOp? op = some kind)
    (values : List Word)
    (hValuesLen :
      values.length = Expressions.Structured.BasicOp.inputs op)
    (stackPrefix : List Word)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler
        (values.reverse ++ stackPrefix) state)
    (program : Assembly.Program) (pc fuel : Nat)
    (hAt :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some (pc, Assembly.Instr.prim op.toPrimOp))
    {valuesAfter : List Word}
    {trace : OpenExternal.OpenTrace}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.Primitive.eval
          prim op compiler values)
        trace (.ok (compilerAfter, valuesAfter))) :
    ∃ evmAfter : EvmYul.EVM.State,
      Locals.SourceLowering.StackPrefixRel layout compilerAfter
        (valuesAfter.reverse ++ stackPrefix) evmAfter ∧
      evmAfter.pc = state.pc + EvmYul.UInt256.ofNat 1 ∧
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program fuel evmAfter)
          tailTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program (fuel + 1) state)
          (trace ++ tailTrace) result := by
  cases hKind : OpenExternal.CallKind.ofBasicOp? op with
  | none =>
      have hNoCallCreate :
          op.toPrimOp.isCallCreate = false := by
        rcases hSupported with hNoCallCreate | ⟨kind, hSome⟩
        · exact hNoCallCreate
        · rw [hKind] at hSome
          cases hSome
      rw [Reference.SourceBridgeFacts.CompilerOpen.Primitive.eval_of_not_callKind
        hKind] at hResolve
      cases hEval : prim.eval op compiler.shared values with
      | error err =>
          simp [hEval] at hResolve
          cases hResolve
      | ok primResult =>
          rcases primResult with ⟨sharedAfter, valuesAfter'⟩
          simp [hEval] at hResolve
          cases hResolve
          rcases
              compilerOpenPrimitive_no_callCreate_stackPrefix_openRunNResult_continue_pc
                (prim := prim) hPrim (layout := layout)
                (compiler := compiler) (state := state)
                op hNoCallCreate values stackPrefix hPrefixRel
                program pc fuel hAt hEval with
            ⟨evmAfter, _hSource, hAfterPrefix, hAfterPc, hCont⟩
          refine ⟨evmAfter, hAfterPrefix, hAfterPc, ?_⟩
          intro tailTrace result hRest
          simpa using hCont hRest
  | some kind =>
      rcases
          compilerOpenPrimitive_callKind_stackPrefix_openRunNResult_continue
            (prim := prim) (layout := layout) (compiler := compiler)
            (state := state) hKind values hValuesLen stackPrefix
            hPrefixRel program pc fuel hAt with
        ⟨operands, compilerCall, evmCall, hValues, hCompilerCall,
          hEVMCall, hResponsePrefix, hCont⟩
      rcases
          compilerOpenPrimitive_eval_resolves_callKind_ok_inv
            (prim := prim) (compiler := compiler) hKind hCompilerCall
            hResolve with
        ⟨response, hTrace, hResult⟩
      have hCompilerAfter :
          compilerAfter = (compilerCall.resume response).1 := by
        simpa using congrArg Prod.fst hResult
      have hValuesAfter :
          valuesAfter = (compilerCall.resume response).2 := by
        simpa using congrArg Prod.snd hResult
      have hAfterPc :
          (EvmYul.EVM.State.incrPC (evmCall.resume response)).pc =
            state.pc + EvmYul.UInt256.ofNat 1 := by
        simp [EvmYul.EVM.State.incrPC,
          evmOpenCall?_resume_pc hEVMCall response]
      refine
        ⟨EvmYul.EVM.State.incrPC (evmCall.resume response),
          ?_, hAfterPc, ?_⟩
      · simpa [hCompilerAfter, hValuesAfter] using
          hResponsePrefix response
      intro tailTrace result hRest
      rcases hCont response hRest with
        ⟨_hSource, hTarget⟩
      simpa [hTrace] using hTarget

theorem compilerOpenPrimitive_eval_resolves_ok_length
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {compiler compilerAfter : Objects.Source.State}
    {op : Structured.BasicOp} {values valuesAfter : List Word}
    {trace : OpenExternal.OpenTrace}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.Primitive.eval
          prim op compiler values)
        trace (.ok (compilerAfter, valuesAfter))) :
    valuesAfter.length = Expressions.Structured.BasicOp.outputs op := by
  unfold Reference.SourceBridgeFacts.CompilerOpen.Primitive.eval at hResolve
  cases hOpen :
      Reference.SourceBridgeFacts.CompilerOpen.Primitive.openCall?
        compiler op values with
  | none =>
      simp [hOpen] at hResolve
      cases hEval : prim.eval op compiler.shared values with
      | error err =>
          simp [hEval] at hResolve
          cases hResolve
      | ok primResult =>
          rcases primResult with ⟨sharedAfter, valuesAfter'⟩
          simp [hEval] at hResolve
          cases hResolve
          exact hPrim.eval_length hEval
  | some call =>
      simp [hOpen] at hResolve
      cases hResolve with
      | @call call' response _trace _result hTail =>
          cases hCallResult : call.resume response with
          | error err =>
              simp [hCallResult] at hTail
              cases hTail
          | ok resultPair =>
              rcases resultPair with ⟨compilerAfter', valuesAfter'⟩
              simp [hCallResult] at hTail
              cases hTail
              unfold
                Reference.SourceBridgeFacts.CompilerOpen.Primitive.openCall?
                at hOpen
              cases hKind : OpenExternal.CallKind.ofBasicOp? op with
              | none =>
                  simp [hKind] at hOpen
              | some kind =>
                  cases hCompilerCall :
                      Reference.SourceBridgeFacts.SourceStateRel.compilerPrimitiveOpenCall?
                        compiler kind values with
                  | none =>
                      simp [hKind, hCompilerCall] at hOpen
                  | some compilerCall =>
                      simp [hKind, hCompilerCall] at hOpen
                      rcases hOpen with rfl
                      have hOp : op = kind.toBasicOp :=
                        basicOp_eq_toBasicOp_of_callKind hKind
                      cases hOp
                      have hPairEq :
                          compilerCall.resume response =
                            (compilerAfter, valuesAfter) :=
                        Except.ok.inj hCallResult
                      have hResumeLen :
                          (compilerCall.resume response).2.length = 1 := by
                        unfold
                          Reference.SourceBridgeFacts.SourceStateRel.compilerPrimitiveOpenCall?
                          at hCompilerCall
                        cases hPrimitiveCall :
                            OpenExternal.CallKind.primitiveSharedOpenCall?
                              compiler.shared kind values with
                        | none =>
                            simp [hPrimitiveCall] at hCompilerCall
                        | some primitiveCall =>
                            simp [hPrimitiveCall] at hCompilerCall
                            rcases hCompilerCall with rfl
                            unfold
                              OpenExternal.CallKind.primitiveSharedOpenCall?
                              at hPrimitiveCall
                            cases hSite :
                                OpenExternal.CallKind.primitiveCallSite?
                                  compiler.shared kind values with
                            | none =>
                                simp [hSite] at hPrimitiveCall
                            | some site =>
                                simp [hSite] at hPrimitiveCall
                                rcases hPrimitiveCall with rfl
                                simp
                      simpa [hPairEq,
                        OpenExternal.CallKind.outputs_toBasicOp] using
                        hResumeLen

mutual
  theorem compilerOpenLocalsExpr_eval_resolves_ok_length_of_sourceOwned
      {prim : Objects.Source.PrimitiveSemantics}
      (hPrim : Locals.SourceLowering.PrimitiveSound prim) :
      ∀ {results : Nat} {expr : Locals.Expr results}
        {compiler compilerAfter : Objects.Source.State}
        {valuesAfter : List Word} {trace : OpenExternal.OpenTrace},
        Locals.Source.Expr.SourceOwned expr →
        OpenExternal.OpenResultResolves
          (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.eval
            prim expr compiler)
          trace (.ok (compilerAfter, valuesAfter)) →
        valuesAfter.length = results := by
    intro results expr compiler compilerAfter valuesAfter trace hOwned hResolve
    cases expr with
    | lit value =>
        rw [Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.eval] at hResolve
        cases hResolve
        simp
    | var name =>
        rw [Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.eval] at hResolve
        cases hLookup : compiler.vars name with
        | none =>
            simp [hLookup, Reference.SourceBridgeFacts.CompilerOpen.invalid]
              at hResolve
            cases hResolve
        | some value =>
            simp [hLookup] at hResolve
            cases hResolve
            simp
    | code code =>
        simp [Locals.Source.Expr.SourceOwned] at hOwned
    | prim op args =>
        rw [Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.eval] at hResolve
        simp [Locals.Source.Expr.SourceOwned] at hOwned
        rcases OpenExternal.OpenResultResolves.bind_inv hResolve with
          hArgsError | hArgsOk
        · rcases hArgsError with ⟨err, _hArgs, hResult⟩
          cases hResult
        · rcases hArgsOk with
            ⟨argsTrace, primTrace, argResult, _hTrace, _hResolveArgs,
              hResolvePrim⟩
          rcases argResult with ⟨compilerAfterArgs, argValues⟩
          exact
            compilerOpenPrimitive_eval_resolves_ok_length
              (prim := prim) hPrim hResolvePrim

  theorem compilerOpenLocalsExprSeq_eval_resolves_ok_length_of_sourceOwned
      {prim : Objects.Source.PrimitiveSemantics}
      (hPrim : Locals.SourceLowering.PrimitiveSound prim) :
      ∀ {results : Nat} {exprs : Locals.ExprSeq results}
        {compiler compilerAfter : Objects.Source.State}
        {valuesAfter : List Word} {trace : OpenExternal.OpenTrace},
        Locals.Source.ExprSeq.SourceOwned exprs →
        OpenExternal.OpenResultResolves
          (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.evalSeq
            prim exprs compiler)
          trace (.ok (compilerAfter, valuesAfter)) →
        valuesAfter.length = results := by
    intro results exprs compiler compilerAfter valuesAfter trace hOwned hResolve
    cases exprs with
    | nil =>
        rw [Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.evalSeq] at hResolve
        cases hResolve
        simp
    | @cons left right head tail =>
        simp [Locals.Source.ExprSeq.SourceOwned] at hOwned
        rcases hOwned with ⟨hHeadOwned, hTailOwned⟩
        rw [Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.evalSeq] at hResolve
        rcases OpenExternal.OpenResultResolves.bind_inv hResolve with
          hHeadError | hHeadOk
        · rcases hHeadError with ⟨err, _hHead, hResult⟩
          cases hResult
        · rcases hHeadOk with
            ⟨headTrace, tailAndDoneTrace, headResult, _hTrace,
              hResolveHead, hResolveTailBind⟩
          rcases headResult with ⟨compilerAfterHead, headValues⟩
          rcases OpenExternal.OpenResultResolves.bind_inv hResolveTailBind with
            hTailError | hTailOk
          · rcases hTailError with ⟨err, _hTail, hResult⟩
            cases hResult
          · rcases hTailOk with
              ⟨tailTrace, doneTrace, tailResult, _hTailAndDoneTrace,
                hResolveTail, hResolveDone⟩
            rcases tailResult with ⟨compilerAfterTail, tailValues⟩
            cases hResolveDone
            have hHeadLen :
                headValues.length = left :=
              compilerOpenLocalsExpr_eval_resolves_ok_length_of_sourceOwned
                hPrim hHeadOwned hResolveHead
            have hTailLen :
                tailValues.length = right :=
              compilerOpenLocalsExprSeq_eval_resolves_ok_length_of_sourceOwned
                hPrim hTailOwned hResolveTail
            simp [hHeadLen, hTailLen]
end

theorem compilerOpenLocalsExpr_prim_stackPrefix_openRunNResult_continue_of_args
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {layout : List Name}
    {compiler compilerAfter : Objects.Source.State}
    {state : EvmYul.EVM.State}
    {op : Structured.BasicOp}
    {args : Locals.ExprSeq (Expressions.Structured.BasicOp.inputs op)}
    (hSupported :
      op.toPrimOp.isCallCreate = false ∨
        ∃ kind : OpenExternal.CallKind,
          OpenExternal.CallKind.ofBasicOp? op = some kind)
    (stackPrefix : List Word)
    (program : Assembly.Program)
    (primitiveTailFuel expressionFuel : Nat)
    (hArgsLength :
      ∀ {argsTrace : OpenExternal.OpenTrace}
        {compilerAfterArgs : Objects.Source.State} {argValues : List Word},
        OpenExternal.OpenResultResolves
          (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.evalSeq
            prim args compiler)
          argsTrace (.ok (compilerAfterArgs, argValues)) →
        argValues.length = Expressions.Structured.BasicOp.inputs op)
    (hArgsSound :
      ∀ {argsTrace : OpenExternal.OpenTrace}
        {compilerAfterArgs : Objects.Source.State} {argValues : List Word},
        OpenExternal.OpenResultResolves
          (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.evalSeq
            prim args compiler)
          argsTrace (.ok (compilerAfterArgs, argValues)) →
        ∃ evmAfterArgs : EvmYul.EVM.State,
        ∃ pc : Nat,
          Locals.SourceLowering.StackPrefixRel layout compilerAfterArgs
            (argValues.reverse ++ stackPrefix) evmAfterArgs ∧
          Assembly.Program.instrAtPc program evmAfterArgs.pc.toNat =
            some (pc, Assembly.Instr.prim op.toPrimOp) ∧
          ∀ {tailTrace : OpenExternal.OpenTrace}
            {result : Except EVMException Assembly.StepResult},
            OpenExternal.OpenResultResolves
              (OpenAssembly.Source.openRunNResult program
                (primitiveTailFuel + 1) evmAfterArgs)
              tailTrace result →
            OpenExternal.OpenResultResolves
              (OpenAssembly.Source.openRunNResult program expressionFuel state)
              (argsTrace ++ tailTrace) result)
    {valuesAfter : List Word}
    {trace : OpenExternal.OpenTrace}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.eval
          prim (.prim op args) compiler)
        trace (.ok (compilerAfter, valuesAfter))) :
    ∃ evmAfter : EvmYul.EVM.State,
      Locals.SourceLowering.StackPrefixRel layout compilerAfter
        (valuesAfter.reverse ++ stackPrefix) evmAfter ∧
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program primitiveTailFuel
            evmAfter)
          tailTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program expressionFuel state)
          (trace ++ tailTrace) result := by
  rw [Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.eval] at hResolve
  rcases OpenExternal.OpenResultResolves.bind_inv hResolve with
    hArgsError | hArgsOk
  · rcases hArgsError with ⟨err, _hArgs, hResult⟩
    cases hResult
  · rcases hArgsOk with
      ⟨argsTrace, primTrace, argResult, hTrace, hResolveArgs,
        hResolvePrim⟩
    rcases argResult with ⟨compilerAfterArgs, argValues⟩
    rcases hArgsSound hResolveArgs with
      ⟨evmAfterArgs, pc, hArgsPrefix, hAt, hArgsCont⟩
    have hArgValuesLen :
        argValues.length = Expressions.Structured.BasicOp.inputs op :=
      hArgsLength hResolveArgs
    rcases
        compilerOpenPrimitive_stackPrefix_openRunNResult_continue_of_resolves_ok
          (prim := prim) hPrim (layout := layout)
          (compiler := compilerAfterArgs) (compilerAfter := compilerAfter)
          (state := evmAfterArgs) op hSupported argValues hArgValuesLen
          stackPrefix hArgsPrefix program pc primitiveTailFuel hAt
          hResolvePrim with
      ⟨evmAfter, hAfterPrefix, hPrimCont⟩
    refine ⟨evmAfter, hAfterPrefix, ?_⟩
    intro tailTrace result hRest
    have hPrimitiveAndTail :
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program
            (primitiveTailFuel + 1) evmAfterArgs)
          (primTrace ++ tailTrace) result :=
      hPrimCont hRest
    have hFull := hArgsCont hPrimitiveAndTail
    subst trace
    simpa [List.append_assoc] using hFull

theorem compilerOpenLocalsExpr_prim_stackPrefix_openRunNResult_continue_fallthrough_of_args
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {layout : List Name}
    {compiler compilerAfter : Objects.Source.State}
    {state : EvmYul.EVM.State}
    {op : Structured.BasicOp}
    {args : Locals.ExprSeq (Expressions.Structured.BasicOp.inputs op)}
    (hSupported :
      op.toPrimOp.isCallCreate = false ∨
        ∃ kind : OpenExternal.CallKind,
          OpenExternal.CallKind.ofBasicOp? op = some kind)
    (stackPrefix : List Word)
    (program : Assembly.Program)
    (primitiveTailFuel expressionFuel : Nat)
    (finalFallthroughPc : Word)
    (hArgsLength :
      ∀ {argsTrace : OpenExternal.OpenTrace}
        {compilerAfterArgs : Objects.Source.State} {argValues : List Word},
        OpenExternal.OpenResultResolves
          (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.evalSeq
            prim args compiler)
          argsTrace (.ok (compilerAfterArgs, argValues)) →
        argValues.length = Expressions.Structured.BasicOp.inputs op)
    (hArgsSound :
      ∀ {argsTrace : OpenExternal.OpenTrace}
        {compilerAfterArgs : Objects.Source.State} {argValues : List Word},
        OpenExternal.OpenResultResolves
          (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.evalSeq
            prim args compiler)
          argsTrace (.ok (compilerAfterArgs, argValues)) →
        ∃ evmAfterArgs : EvmYul.EVM.State,
        ∃ pc : Nat,
          Locals.SourceLowering.StackPrefixRel layout compilerAfterArgs
            (argValues.reverse ++ stackPrefix) evmAfterArgs ∧
          Assembly.Program.instrAtPc program evmAfterArgs.pc.toNat =
            some (pc, Assembly.Instr.prim op.toPrimOp) ∧
          evmAfterArgs.pc + EvmYul.UInt256.ofNat 1 =
            finalFallthroughPc ∧
          ∀ {tailTrace : OpenExternal.OpenTrace}
            {result : Except EVMException Assembly.StepResult},
            OpenExternal.OpenResultResolves
              (OpenAssembly.Source.openRunNResult program
                (primitiveTailFuel + 1) evmAfterArgs)
              tailTrace result →
            OpenExternal.OpenResultResolves
              (OpenAssembly.Source.openRunNResult program expressionFuel state)
              (argsTrace ++ tailTrace) result)
    {valuesAfter : List Word}
    {trace : OpenExternal.OpenTrace}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.eval
          prim (.prim op args) compiler)
        trace (.ok (compilerAfter, valuesAfter))) :
    ∃ evmAfter : EvmYul.EVM.State,
      Locals.SourceLowering.StackPrefixRel layout compilerAfter
        (valuesAfter.reverse ++ stackPrefix) evmAfter ∧
      evmAfter.pc = finalFallthroughPc ∧
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program primitiveTailFuel
            evmAfter)
          tailTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program expressionFuel state)
          (trace ++ tailTrace) result := by
  rw [Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.eval] at hResolve
  rcases OpenExternal.OpenResultResolves.bind_inv hResolve with
    hArgsError | hArgsOk
  · rcases hArgsError with ⟨err, _hArgs, hResult⟩
    cases hResult
  · rcases hArgsOk with
      ⟨argsTrace, primTrace, argResult, hTrace, hResolveArgs,
        hResolvePrim⟩
    rcases argResult with ⟨compilerAfterArgs, argValues⟩
    rcases hArgsSound hResolveArgs with
      ⟨evmAfterArgs, pc, hArgsPrefix, hAt, hArgsFallthrough,
        hArgsCont⟩
    have hArgValuesLen :
        argValues.length = Expressions.Structured.BasicOp.inputs op :=
      hArgsLength hResolveArgs
    rcases
        compilerOpenPrimitive_stackPrefix_openRunNResult_continue_pc_of_resolves_ok
          (prim := prim) hPrim (layout := layout)
          (compiler := compilerAfterArgs) (compilerAfter := compilerAfter)
          (state := evmAfterArgs) op hSupported argValues hArgValuesLen
          stackPrefix hArgsPrefix program pc primitiveTailFuel hAt
          hResolvePrim with
      ⟨evmAfter, hAfterPrefix, hAfterPc, hPrimCont⟩
    refine ⟨evmAfter, hAfterPrefix, ?_, ?_⟩
    · exact hAfterPc.trans hArgsFallthrough
    · intro tailTrace result hRest
      have hPrimitiveAndTail :
          OpenExternal.OpenResultResolves
            (OpenAssembly.Source.openRunNResult program
              (primitiveTailFuel + 1) evmAfterArgs)
            (primTrace ++ tailTrace) result :=
        hPrimCont hRest
      have hFull := hArgsCont hPrimitiveAndTail
      subst trace
      simpa [List.append_assoc] using hFull

theorem compilerOpenLocalsExpr_prim_stackPrefix_openRunNResult_continue_of_sourceOwned_args
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {layout : List Name}
    {compiler compilerAfter : Objects.Source.State}
    {state : EvmYul.EVM.State}
    {op : Structured.BasicOp}
    {args : Locals.ExprSeq (Expressions.Structured.BasicOp.inputs op)}
    (hArgsOwned : Locals.Source.ExprSeq.SourceOwned args)
    (hSupported :
      op.toPrimOp.isCallCreate = false ∨
        ∃ kind : OpenExternal.CallKind,
          OpenExternal.CallKind.ofBasicOp? op = some kind)
    (stackPrefix : List Word)
    (program : Assembly.Program)
    (primitiveTailFuel expressionFuel : Nat)
    (hArgsSound :
      ∀ {argsTrace : OpenExternal.OpenTrace}
        {compilerAfterArgs : Objects.Source.State} {argValues : List Word},
        OpenExternal.OpenResultResolves
          (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.evalSeq
            prim args compiler)
          argsTrace (.ok (compilerAfterArgs, argValues)) →
        ∃ evmAfterArgs : EvmYul.EVM.State,
        ∃ pc : Nat,
          Locals.SourceLowering.StackPrefixRel layout compilerAfterArgs
            (argValues.reverse ++ stackPrefix) evmAfterArgs ∧
          Assembly.Program.instrAtPc program evmAfterArgs.pc.toNat =
            some (pc, Assembly.Instr.prim op.toPrimOp) ∧
          ∀ {tailTrace : OpenExternal.OpenTrace}
            {result : Except EVMException Assembly.StepResult},
            OpenExternal.OpenResultResolves
              (OpenAssembly.Source.openRunNResult program
                (primitiveTailFuel + 1) evmAfterArgs)
              tailTrace result →
            OpenExternal.OpenResultResolves
              (OpenAssembly.Source.openRunNResult program expressionFuel state)
              (argsTrace ++ tailTrace) result)
    {valuesAfter : List Word}
    {trace : OpenExternal.OpenTrace}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.eval
          prim (.prim op args) compiler)
        trace (.ok (compilerAfter, valuesAfter))) :
    ∃ evmAfter : EvmYul.EVM.State,
      Locals.SourceLowering.StackPrefixRel layout compilerAfter
        (valuesAfter.reverse ++ stackPrefix) evmAfter ∧
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program primitiveTailFuel
            evmAfter)
          tailTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program expressionFuel state)
          (trace ++ tailTrace) result :=
  compilerOpenLocalsExpr_prim_stackPrefix_openRunNResult_continue_of_args
    (prim := prim) hPrim (layout := layout) (compiler := compiler)
    (compilerAfter := compilerAfter) (state := state) (op := op)
    (args := args) hSupported stackPrefix program primitiveTailFuel
    expressionFuel
    (fun hResolveArgs =>
      compilerOpenLocalsExprSeq_eval_resolves_ok_length_of_sourceOwned
        hPrim hArgsOwned hResolveArgs)
    hArgsSound hResolve

theorem compilerOpenLocalsExpr_prim_stackPrefix_openRunNResult_continue_fallthrough_of_compileCode_args
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {ctx : Locals.Ctx} {offset : Nat}
    {layout : List Name}
    {compiler compilerAfter : Objects.Source.State}
    {state : EvmYul.EVM.State}
    {op : Structured.BasicOp}
    {args : Locals.ExprSeq (Expressions.Structured.BasicOp.inputs op)}
    {code : Structured.Code}
    (hCompile :
      Locals.Expr.compileCode ctx offset (.prim op args) = some code)
    (hArgsOwned : Locals.Source.ExprSeq.SourceOwned args)
    (hSupported :
      op.toPrimOp.isCallCreate = false ∨
        ∃ kind : OpenExternal.CallKind,
          OpenExternal.CallKind.ofBasicOp? op = some kind)
    (stackPrefix : List Word)
    (program : Assembly.Program)
    (primitiveTailFuel expressionFuel : Nat)
    (segment :
      Structured.Preservation.CodeSegment program code.toAssembly)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment)
    (hArgsSound :
      ∀ {argsCode : Structured.Code},
        Locals.ExprSeq.compileCode ctx offset args = some argsCode →
        (argsSegment :
          Structured.Preservation.CodeSegment program argsCode.toAssembly) →
        state.pc =
          Structured.Preservation.CodeSegment.startPc argsSegment →
        ∀ {argsTrace : OpenExternal.OpenTrace}
          {compilerAfterArgs : Objects.Source.State}
          {argValues : List Word},
          OpenExternal.OpenResultResolves
            (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.evalSeq
              prim args compiler)
            argsTrace (.ok (compilerAfterArgs, argValues)) →
          ∃ evmAfterArgs : EvmYul.EVM.State,
            Locals.SourceLowering.StackPrefixRel layout compilerAfterArgs
              (argValues.reverse ++ stackPrefix) evmAfterArgs ∧
            evmAfterArgs.pc =
              Structured.Preservation.CodeSegment.fallthroughPc
                argsSegment ∧
            ∀ {tailTrace : OpenExternal.OpenTrace}
              {result : Except EVMException Assembly.StepResult},
              OpenExternal.OpenResultResolves
                (OpenAssembly.Source.openRunNResult program
                  (primitiveTailFuel + 1) evmAfterArgs)
                tailTrace result →
              OpenExternal.OpenResultResolves
                (OpenAssembly.Source.openRunNResult program expressionFuel
                  state)
                (argsTrace ++ tailTrace) result)
    {valuesAfter : List Word}
    {trace : OpenExternal.OpenTrace}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.eval
          prim (.prim op args) compiler)
        trace (.ok (compilerAfter, valuesAfter))) :
    ∃ evmAfter : EvmYul.EVM.State,
      Locals.SourceLowering.StackPrefixRel layout compilerAfter
        (valuesAfter.reverse ++ stackPrefix) evmAfter ∧
      evmAfter.pc =
        Structured.Preservation.CodeSegment.fallthroughPc segment ∧
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program primitiveTailFuel
            evmAfter)
          tailTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program expressionFuel state)
          (trace ++ tailTrace) result := by
  rcases localsExpr_compileCode_prim_inv hCompile with
    ⟨argsCode, hArgsCompile, hCode⟩
  have hAssemblyCode :
      code.toAssembly =
        argsCode.toAssembly ++ [Assembly.Instr.prim op.toPrimOp] := by
    simp [hCode, Structured.Code.toAssembly,
      Structured.BasicInstr.toAssembly]
  let appendSegment :
      Structured.Preservation.CodeSegment program
        (argsCode.toAssembly ++ [Assembly.Instr.prim op.toPrimOp]) :=
    Structured.Preservation.CodeSegment.cast_code hAssemblyCode segment
  let argsSegment :
      Structured.Preservation.CodeSegment program argsCode.toAssembly :=
    Structured.Preservation.CodeSegment.left appendSegment
  let primSegment :
      Structured.Preservation.CodeSegment program
        [Assembly.Instr.prim op.toPrimOp] :=
    Structured.Preservation.CodeSegment.right appendSegment
  have hArgsPc :
      state.pc =
        Structured.Preservation.CodeSegment.startPc argsSegment := by
    simpa [argsSegment, appendSegment,
      Structured.Preservation.CodeSegment.left,
      Structured.Preservation.CodeSegment.cast_code,
      Structured.Preservation.CodeSegment.startPc] using hPc
  have hPrimStart :
      Structured.Preservation.CodeSegment.startPc primSegment =
        Structured.Preservation.CodeSegment.fallthroughPc argsSegment :=
    codeSegment_right_startPc_eq_left_fallthroughPc appendSegment
  have hPrimFallSegment :
      Structured.Preservation.CodeSegment.fallthroughPc primSegment =
        Structured.Preservation.CodeSegment.fallthroughPc segment := by
    simp [primSegment, appendSegment,
      Structured.Preservation.CodeSegment.right,
      Structured.Preservation.CodeSegment.cast_code,
      Structured.Preservation.CodeSegment.fallthroughPc,
      hAssemblyCode, List.append_assoc]
  have hPrimFall :
      Structured.Preservation.CodeSegment.fallthroughPc primSegment =
        Structured.Preservation.CodeSegment.startPc primSegment +
          EvmYul.UInt256.ofNat 1 := by
    simpa [Assembly.Instr.byteSize] using
      codeSegment_fallthroughPc_singleton primSegment
  exact
    compilerOpenLocalsExpr_prim_stackPrefix_openRunNResult_continue_fallthrough_of_args
      (prim := prim) hPrim (layout := layout) (compiler := compiler)
      (compilerAfter := compilerAfter) (state := state) (op := op)
      (args := args) hSupported stackPrefix program primitiveTailFuel
      expressionFuel
      (Structured.Preservation.CodeSegment.fallthroughPc segment)
      (fun hResolveArgs =>
        compilerOpenLocalsExprSeq_eval_resolves_ok_length_of_sourceOwned
          hPrim hArgsOwned hResolveArgs)
      (fun {argsTrace compilerAfterArgs argValues} hResolveArgs => by
        rcases hArgsSound hArgsCompile argsSegment hArgsPc hResolveArgs with
          ⟨evmAfterArgs, hArgsPrefix, hArgsAfterPc, hArgsCont⟩
        have hAtPrimPc :
            evmAfterArgs.pc =
              Structured.Preservation.CodeSegment.startPc primSegment := by
          rw [hArgsAfterPc]
          exact hPrimStart.symm
        have hAt :
            Assembly.Program.instrAtPc program evmAfterArgs.pc.toNat =
              some
                ((Structured.Preservation.CodeSegment.startPc
                    primSegment).toNat,
                  Assembly.Instr.prim op.toPrimOp) := by
          simpa [hAtPrimPc] using
            codeSegment_instrAtPc_start_cons primSegment
        have hArgsFall :
            evmAfterArgs.pc + EvmYul.UInt256.ofNat 1 =
              Structured.Preservation.CodeSegment.fallthroughPc
                segment := by
          rw [hAtPrimPc]
          rw [← hPrimFall]
          exact hPrimFallSegment
        exact
          ⟨evmAfterArgs,
            (Structured.Preservation.CodeSegment.startPc primSegment).toNat,
            hArgsPrefix, hAt, hArgsFall, hArgsCont⟩)
      hResolve

theorem compilerOpenLocalsExpr_lit_stackPrefix_openRunNResult_continue
    {prim : Objects.Source.PrimitiveSemantics}
    {layout : List Name}
    {compiler compilerAfter : Objects.Source.State}
    {state : EvmYul.EVM.State}
    (value : Word)
    (stackPrefix : List Word)
    (program : Assembly.Program) (pc fuel : Nat)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler stackPrefix state)
    (hAt :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some (pc, Assembly.Instr.push value))
    {valuesAfter : List Word}
    {trace : OpenExternal.OpenTrace}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.eval
          prim (.lit value) compiler)
        trace (.ok (compilerAfter, valuesAfter))) :
    ∃ evmAfter : EvmYul.EVM.State,
      Locals.SourceLowering.StackPrefixRel layout compilerAfter
        (valuesAfter.reverse ++ stackPrefix) evmAfter ∧
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program fuel evmAfter)
          tailTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program (fuel + 1) state)
          (trace ++ tailTrace) result := by
  rw [Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.eval] at hResolve
  cases hResolve
  rcases hPrefixRel with ⟨hShared, baseStack, hStack, hStackRel⟩
  let evmAfter :=
    state.replaceStackAndIncrPC (state.stack.push value) (pcΔ := 33)
  have hStep :
      Assembly.Source.stepAtResult program pc (.push value) state =
        .ok (.running evmAfter) := by
    simp [Assembly.Source.stepAtResult, Assembly.Source.stepAt,
      Assembly.Instr.haltKind?, Assembly.Target.stepInstr, evmAfter]
  have hOpenStep :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openStepAtResult program pc (.push value) state)
        [] (.ok (.running evmAfter)) :=
    OpenAssembly.Source.openStepAtResult_resolves_closed_of_non_prim
      (program := program) (pc := pc) (instr := .push value)
      (state := state) (result := .running evmAfter)
      (by intro op hEq; cases hEq) hStep
  refine ⟨evmAfter, ?_, ?_⟩
  · constructor
    · simpa [evmAfter, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC] using hShared
    · refine ⟨baseStack, ?_, hStackRel⟩
      simp [evmAfter, hStack, EvmYul.Stack.push,
        EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]
  · intro tailTrace result hRest
    simpa using
      OpenAssembly.Source.openRunNResult_current_stepAt_running_continue
        (program := program) (fuel := fuel) (state := state)
        (mid := evmAfter) (pc := pc) (instr := .push value)
        hAt hOpenStep hRest

theorem compilerOpenLocalsExpr_lit_stackPrefix_openRunNResult_continue_of_compileCode
    {prim : Objects.Source.PrimitiveSemantics}
    {ctx : Locals.Ctx} {offset : Nat}
    {layout : List Name}
    {compiler compilerAfter : Objects.Source.State}
    {state : EvmYul.EVM.State}
    {value : Word}
    {code : Structured.Code}
    (hCompile :
      Locals.Expr.compileCode ctx offset (.lit value) = some code)
    (stackPrefix : List Word)
    (program : Assembly.Program) (fuel : Nat)
    (segment :
      Structured.Preservation.CodeSegment program code.toAssembly)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler stackPrefix state)
    {valuesAfter : List Word}
    {trace : OpenExternal.OpenTrace}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.eval
          prim (.lit value) compiler)
        trace (.ok (compilerAfter, valuesAfter))) :
    ∃ evmAfter : EvmYul.EVM.State,
      Locals.SourceLowering.StackPrefixRel layout compilerAfter
        (valuesAfter.reverse ++ stackPrefix) evmAfter ∧
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program fuel evmAfter)
          tailTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program (fuel + 1) state)
          (trace ++ tailTrace) result := by
  have hCode :
      code = [Structured.BasicInstr.push value] :=
    localsExpr_compileCode_lit_eq hCompile
  have hAssemblyCode :
      code.toAssembly = [Assembly.Instr.push value] := by
    simp [hCode, Structured.Code.toAssembly,
      Structured.BasicInstr.toAssembly]
  let pushSegment :
      Structured.Preservation.CodeSegment program
        [Assembly.Instr.push value] :=
    Structured.Preservation.CodeSegment.cast_code hAssemblyCode segment
  have hPcPush :
      state.pc =
        Structured.Preservation.CodeSegment.startPc pushSegment := by
    simpa [pushSegment, Structured.Preservation.CodeSegment.cast_code,
      Structured.Preservation.CodeSegment.startPc] using hPc
  have hAt :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some
          ((Structured.Preservation.CodeSegment.startPc pushSegment).toNat,
            Assembly.Instr.push value) := by
    simpa [hPcPush] using codeSegment_instrAtPc_start_cons pushSegment
  exact
    compilerOpenLocalsExpr_lit_stackPrefix_openRunNResult_continue
      (prim := prim) (layout := layout) (compiler := compiler)
      (compilerAfter := compilerAfter) (state := state) value stackPrefix
      program
      ((Structured.Preservation.CodeSegment.startPc pushSegment).toNat)
      fuel hPrefixRel hAt hResolve

theorem compilerOpenLocalsExpr_lit_stackPrefix_openRunNResult_continue_fallthrough_of_compileCode
    {prim : Objects.Source.PrimitiveSemantics}
    {ctx : Locals.Ctx} {offset : Nat}
    {layout : List Name}
    {compiler compilerAfter : Objects.Source.State}
    {state : EvmYul.EVM.State}
    {value : Word}
    {code : Structured.Code}
    (hCompile :
      Locals.Expr.compileCode ctx offset (.lit value) = some code)
    (stackPrefix : List Word)
    (program : Assembly.Program) (fuel : Nat)
    (segment :
      Structured.Preservation.CodeSegment program code.toAssembly)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler stackPrefix state)
    {valuesAfter : List Word}
    {trace : OpenExternal.OpenTrace}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.eval
          prim (.lit value) compiler)
        trace (.ok (compilerAfter, valuesAfter))) :
    ∃ evmAfter : EvmYul.EVM.State,
      Locals.SourceLowering.StackPrefixRel layout compilerAfter
        (valuesAfter.reverse ++ stackPrefix) evmAfter ∧
      evmAfter.pc =
        Structured.Preservation.CodeSegment.fallthroughPc segment ∧
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program fuel evmAfter)
          tailTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program (fuel + 1) state)
          (trace ++ tailTrace) result := by
  have hCode :
      code = [Structured.BasicInstr.push value] :=
    localsExpr_compileCode_lit_eq hCompile
  have hAssemblyCode :
      code.toAssembly = [Assembly.Instr.push value] := by
    simp [hCode, Structured.Code.toAssembly,
      Structured.BasicInstr.toAssembly]
  let pushSegment :
      Structured.Preservation.CodeSegment program
        [Assembly.Instr.push value] :=
    Structured.Preservation.CodeSegment.cast_code hAssemblyCode segment
  have hPcPush :
      state.pc =
        Structured.Preservation.CodeSegment.startPc pushSegment := by
    simpa [pushSegment, Structured.Preservation.CodeSegment.cast_code,
      Structured.Preservation.CodeSegment.startPc] using hPc
  have hAt :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some
          ((Structured.Preservation.CodeSegment.startPc pushSegment).toNat,
            Assembly.Instr.push value) := by
    simpa [hPcPush] using codeSegment_instrAtPc_start_cons pushSegment
  rw [Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.eval] at hResolve
  cases hResolve
  rcases hPrefixRel with ⟨hShared, baseStack, hStack, hStackRel⟩
  let evmAfter :=
    state.replaceStackAndIncrPC (state.stack.push value) (pcΔ := 33)
  have hStep :
      Assembly.Source.stepAtResult program
          ((Structured.Preservation.CodeSegment.startPc pushSegment).toNat)
          (.push value) state =
        .ok (.running evmAfter) := by
    simp [Assembly.Source.stepAtResult, Assembly.Source.stepAt,
      Assembly.Instr.haltKind?, Assembly.Target.stepInstr, evmAfter]
  have hOpenStep :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openStepAtResult program
          ((Structured.Preservation.CodeSegment.startPc pushSegment).toNat)
          (.push value) state)
        [] (.ok (.running evmAfter)) :=
    OpenAssembly.Source.openStepAtResult_resolves_closed_of_non_prim
      (program := program)
      (pc := (Structured.Preservation.CodeSegment.startPc pushSegment).toNat)
      (instr := .push value)
      (state := state) (result := .running evmAfter)
      (by intro op hEq; cases hEq) hStep
  have hAfterPc :
      evmAfter.pc =
        Structured.Preservation.CodeSegment.startPc pushSegment +
          EvmYul.UInt256.ofNat 33 := by
    simp [evmAfter, hPcPush, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC]
  have hFallPush :
      Structured.Preservation.CodeSegment.fallthroughPc pushSegment =
        Structured.Preservation.CodeSegment.startPc pushSegment +
          EvmYul.UInt256.ofNat 33 := by
    simpa [Assembly.Instr.byteSize, Assembly.Instr.push32Size] using
      codeSegment_fallthroughPc_singleton pushSegment
  have hFallSegment :
      Structured.Preservation.CodeSegment.fallthroughPc pushSegment =
        Structured.Preservation.CodeSegment.fallthroughPc segment := by
    simp [pushSegment, Structured.Preservation.CodeSegment.cast_code,
      Structured.Preservation.CodeSegment.fallthroughPc, hAssemblyCode]
  refine ⟨evmAfter, ?_, ?_, ?_⟩
  · constructor
    · simpa [evmAfter, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC] using hShared
    · refine ⟨baseStack, ?_, hStackRel⟩
      simp [evmAfter, hStack, EvmYul.Stack.push,
        EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]
  · rw [hFallSegment.symm, hFallPush]
    exact hAfterPc
  · intro tailTrace result hRest
    simpa using
      OpenAssembly.Source.openRunNResult_current_stepAt_running_continue
        (program := program) (fuel := fuel) (state := state)
        (mid := evmAfter)
        (pc := (Structured.Preservation.CodeSegment.startPc pushSegment).toNat)
        (instr := .push value)
        hAt hOpenStep hRest

theorem compilerOpenLocalsExpr_var_stackPrefix_openRunNResult_continue
    {prim : Objects.Source.PrimitiveSemantics}
    {layout : List Name}
    {compiler compilerAfter : Objects.Source.State}
    {state : EvmYul.EVM.State}
    {name : Name} {idx offset : Nat} {op : Structured.BasicOp}
    (hName : layout[idx]? = some name)
    (stackPrefix : List Word)
    (hPrefixLen : stackPrefix.length = offset)
    (hBound : offset + idx + 1 ≤ 16)
    (hDup : Locals.StackOp.dup? (offset + idx + 1) = some op)
    (program : Assembly.Program) (pc fuel : Nat)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler stackPrefix state)
    (hAt :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some (pc, Assembly.Instr.prim op.toPrimOp))
    {valuesAfter : List Word}
    {trace : OpenExternal.OpenTrace}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.eval
          prim (.var name) compiler)
        trace (.ok (compilerAfter, valuesAfter))) :
    ∃ evmAfter : EvmYul.EVM.State,
      Locals.SourceLowering.StackPrefixRel layout compilerAfter
        (valuesAfter.reverse ++ stackPrefix) evmAfter ∧
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program fuel evmAfter)
          tailTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program (fuel + 1) state)
          (trace ++ tailTrace) result := by
  rw [Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.eval] at hResolve
  cases hLookup : compiler.vars name with
  | none =>
      simp [hLookup, Reference.SourceBridgeFacts.CompilerOpen.invalid] at hResolve
      cases hResolve
  | some value =>
      simp [hLookup] at hResolve
      cases hResolve
      rcases hPrefixRel with ⟨hShared, baseStack, hStack, hStackRel⟩
      have hBaseAt : baseStack[idx]? = some value := by
        have hLookupBase := hStackRel.2 hName
        simpa [hLookup] using hLookupBase
      subst offset
      have hStackAt :
          state.stack[stackPrefix.length + idx]? = some value := by
        rw [hStack]
        rw [List.getElem?_append_right]
        · simpa using hBaseAt
        · simp
      let evmAfter := state.replaceStackAndIncrPC (value :: state.stack)
      let depth := stackPrefix.length + (idx + 1)
      have hDupDepth : Locals.StackOp.dup? depth = some op := by
        simpa [depth, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          hDup
      have hNoCallCreate : op.toPrimOp.isCallCreate = false :=
        Locals.CompilerFacts.StackOp.dup?_not_callCreate depth hDupDepth
      have hDupValue :
          EvmYul.dup depth state = .ok evmAfter := by
        have hDupValue' :=
          Locals.Direct.evm_dup_succ_get? (state := state)
            (idx := stackPrefix.length + idx) hStackAt
        simpa [depth, evmAfter, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hDupValue'
      have hStepOp : Structured.BasicOp.step op state = .ok evmAfter := by
        have hOne : 1 ≤ depth := by
          unfold depth
          omega
        have hDepthBound : depth ≤ 16 := by
          simpa [depth, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            hBound
        rcases
            Locals.Direct.stackOp_dup?_step_eq_dup
              (n := depth) hOne hDepthBound state with
          ⟨op', hDup', hStepEq⟩
        have hOp : op = op' := by
          rw [hDupDepth] at hDup'
          cases hDup'
          rfl
        rw [hOp, hStepEq]
        exact hDupValue
      have hStepAt :
          Assembly.Source.stepAt program pc (.prim op.toPrimOp) state =
            .ok evmAfter := by
        simpa [Assembly.Source.stepAt, Structured.BasicOp.step] using hStepOp
      have hStepResult :
          Assembly.Source.stepAtResult program pc (.prim op.toPrimOp) state =
            .ok (.running evmAfter) := by
        simp [Assembly.Source.stepAtResult, hStepAt,
          basicOp_toPrimOp_haltKind?_none op]
      have hOpenStep :
          OpenExternal.OpenResultResolves
            (OpenAssembly.Source.openStepAtResult program pc
              (.prim op.toPrimOp) state)
            [] (.ok (.running evmAfter)) :=
        OpenAssembly.Source.openStepAtResult_resolves_closed_of_prim_no_callCreate
          (program := program) (pc := pc) (op := op.toPrimOp)
          (state := state) (result := .running evmAfter)
          hNoCallCreate hStepResult
      refine ⟨evmAfter, ?_, ?_⟩
      · constructor
        · simpa [evmAfter, EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC] using hShared
        · refine ⟨baseStack, ?_, hStackRel⟩
          simp [evmAfter, hStack, EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
      · intro tailTrace result hRest
        simpa using
          OpenAssembly.Source.openRunNResult_current_stepAt_running_continue
            (program := program) (fuel := fuel) (state := state)
            (mid := evmAfter) (pc := pc) (instr := .prim op.toPrimOp)
            hAt hOpenStep hRest

theorem compilerOpenLocalsExpr_var_stackPrefix_openRunNResult_continue_of_compileCode
    {prim : Objects.Source.PrimitiveSemantics}
    {ctx : Locals.Ctx} {offset : Nat}
    {layout : List Name}
    {compiler compilerAfter : Objects.Source.State}
    {state : EvmYul.EVM.State}
    {name : Name}
    {code : Structured.Code}
    (hCompile :
      Locals.Expr.compileCode ctx offset (.var name) = some code)
    (hCtxLayout : ctx.layout = layout)
    (hNoDup : layout.Nodup)
    (hAccess : Locals.SourceLowering.Expr.Accessible layout offset
      (.var name))
    (stackPrefix : List Word)
    (hPrefixLen : stackPrefix.length = offset)
    (program : Assembly.Program) (fuel : Nat)
    (segment :
      Structured.Preservation.CodeSegment program code.toAssembly)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler stackPrefix state)
    {valuesAfter : List Word}
    {trace : OpenExternal.OpenTrace}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.eval
          prim (.var name) compiler)
        trace (.ok (compilerAfter, valuesAfter))) :
    ∃ evmAfter : EvmYul.EVM.State,
      Locals.SourceLowering.StackPrefixRel layout compilerAfter
        (valuesAfter.reverse ++ stackPrefix) evmAfter ∧
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program fuel evmAfter)
          tailTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program (fuel + 1) state)
          (trace ++ tailTrace) result := by
  rcases localsExpr_compileCode_var_inv hCompile with
    ⟨depth, op, hDepth, hDup, hCode⟩
  rcases hAccess with ⟨idx, hName, hBound⟩
  have hDepthIdx :
      Locals.Layout.lookupDepth? name ctx.layout = some (idx + 1) := by
    simpa [hCtxLayout] using
      (Locals.Layout.lookupDepth?_of_get?_nodup hName hNoDup)
  rw [hDepthIdx] at hDepth
  cases hDepth
  have hDupIdx :
      Locals.StackOp.dup? (offset + idx + 1) = some op := by
    simpa [Nat.add_assoc] using hDup
  have hAssemblyCode :
      code.toAssembly = [Assembly.Instr.prim op.toPrimOp] := by
    simp [hCode, Structured.Code.toAssembly,
      Structured.BasicInstr.toAssembly]
  let opSegment :
      Structured.Preservation.CodeSegment program
        [Assembly.Instr.prim op.toPrimOp] :=
    Structured.Preservation.CodeSegment.cast_code hAssemblyCode segment
  have hPcOp :
      state.pc =
        Structured.Preservation.CodeSegment.startPc opSegment := by
    simpa [opSegment, Structured.Preservation.CodeSegment.cast_code,
      Structured.Preservation.CodeSegment.startPc] using hPc
  have hAt :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some
          ((Structured.Preservation.CodeSegment.startPc opSegment).toNat,
            Assembly.Instr.prim op.toPrimOp) := by
    simpa [hPcOp] using codeSegment_instrAtPc_start_cons opSegment
  exact
    compilerOpenLocalsExpr_var_stackPrefix_openRunNResult_continue
      (prim := prim) (layout := layout) (compiler := compiler)
      (compilerAfter := compilerAfter) (state := state) (name := name)
      (idx := idx) (offset := offset) (op := op) hName stackPrefix
      hPrefixLen hBound hDupIdx program
      ((Structured.Preservation.CodeSegment.startPc opSegment).toNat)
      fuel hPrefixRel hAt hResolve

theorem compilerOpenLocalsExpr_var_stackPrefix_openRunNResult_continue_fallthrough_of_compileCode
    {prim : Objects.Source.PrimitiveSemantics}
    {ctx : Locals.Ctx} {offset : Nat}
    {layout : List Name}
    {compiler compilerAfter : Objects.Source.State}
    {state : EvmYul.EVM.State}
    {name : Name}
    {code : Structured.Code}
    (hCompile :
      Locals.Expr.compileCode ctx offset (.var name) = some code)
    (hCtxLayout : ctx.layout = layout)
    (hNoDup : layout.Nodup)
    (hAccess : Locals.SourceLowering.Expr.Accessible layout offset
      (.var name))
    (stackPrefix : List Word)
    (hPrefixLen : stackPrefix.length = offset)
    (program : Assembly.Program) (fuel : Nat)
    (segment :
      Structured.Preservation.CodeSegment program code.toAssembly)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler stackPrefix state)
    {valuesAfter : List Word}
    {trace : OpenExternal.OpenTrace}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.eval
          prim (.var name) compiler)
        trace (.ok (compilerAfter, valuesAfter))) :
    ∃ evmAfter : EvmYul.EVM.State,
      Locals.SourceLowering.StackPrefixRel layout compilerAfter
        (valuesAfter.reverse ++ stackPrefix) evmAfter ∧
      evmAfter.pc =
        Structured.Preservation.CodeSegment.fallthroughPc segment ∧
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program fuel evmAfter)
          tailTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program (fuel + 1) state)
          (trace ++ tailTrace) result := by
  rcases localsExpr_compileCode_var_inv hCompile with
    ⟨depth, op, hDepth, hDup, hCode⟩
  rcases hAccess with ⟨idx, hName, hBound⟩
  have hDepthIdx :
      Locals.Layout.lookupDepth? name ctx.layout = some (idx + 1) := by
    simpa [hCtxLayout] using
      (Locals.Layout.lookupDepth?_of_get?_nodup hName hNoDup)
  rw [hDepthIdx] at hDepth
  cases hDepth
  have hDupIdx :
      Locals.StackOp.dup? (offset + idx + 1) = some op := by
    simpa [Nat.add_assoc] using hDup
  have hAssemblyCode :
      code.toAssembly = [Assembly.Instr.prim op.toPrimOp] := by
    simp [hCode, Structured.Code.toAssembly,
      Structured.BasicInstr.toAssembly]
  let opSegment :
      Structured.Preservation.CodeSegment program
        [Assembly.Instr.prim op.toPrimOp] :=
    Structured.Preservation.CodeSegment.cast_code hAssemblyCode segment
  have hPcOp :
      state.pc =
        Structured.Preservation.CodeSegment.startPc opSegment := by
    simpa [opSegment, Structured.Preservation.CodeSegment.cast_code,
      Structured.Preservation.CodeSegment.startPc] using hPc
  have hAt :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some
          ((Structured.Preservation.CodeSegment.startPc opSegment).toNat,
            Assembly.Instr.prim op.toPrimOp) := by
    simpa [hPcOp] using codeSegment_instrAtPc_start_cons opSegment
  rw [Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.eval] at hResolve
  cases hLookup : compiler.vars name with
  | none =>
      simp [hLookup, Reference.SourceBridgeFacts.CompilerOpen.invalid] at hResolve
      cases hResolve
  | some value =>
      simp [hLookup] at hResolve
      cases hResolve
      rcases hPrefixRel with ⟨hShared, baseStack, hStack, hStackRel⟩
      have hBaseAt : baseStack[idx]? = some value := by
        have hLookupBase := hStackRel.2 hName
        simpa [hLookup] using hLookupBase
      subst offset
      have hStackAt :
          state.stack[stackPrefix.length + idx]? = some value := by
        rw [hStack]
        rw [List.getElem?_append_right]
        · simpa using hBaseAt
        · simp
      let evmAfter := state.replaceStackAndIncrPC (value :: state.stack)
      let depth := stackPrefix.length + (idx + 1)
      have hDupDepth : Locals.StackOp.dup? depth = some op := by
        simpa [depth, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          hDupIdx
      have hNoCallCreate : op.toPrimOp.isCallCreate = false :=
        Locals.CompilerFacts.StackOp.dup?_not_callCreate depth hDupDepth
      have hDupValue :
          EvmYul.dup depth state = .ok evmAfter := by
        have hDupValue' :=
          Locals.Direct.evm_dup_succ_get? (state := state)
            (idx := stackPrefix.length + idx) hStackAt
        simpa [depth, evmAfter, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hDupValue'
      have hStepOp : Structured.BasicOp.step op state = .ok evmAfter := by
        have hOne : 1 ≤ depth := by
          unfold depth
          omega
        have hDepthBound : depth ≤ 16 := by
          simpa [depth, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            hBound
        rcases
            Locals.Direct.stackOp_dup?_step_eq_dup
              (n := depth) hOne hDepthBound state with
          ⟨op', hDup', hStepEq⟩
        have hOp : op = op' := by
          rw [hDupDepth] at hDup'
          cases hDup'
          rfl
        rw [hOp, hStepEq]
        exact hDupValue
      have hStepAt :
          Assembly.Source.stepAt program
              ((Structured.Preservation.CodeSegment.startPc opSegment).toNat)
              (.prim op.toPrimOp) state =
            .ok evmAfter := by
        simpa [Assembly.Source.stepAt, Structured.BasicOp.step] using hStepOp
      have hStepResult :
          Assembly.Source.stepAtResult program
              ((Structured.Preservation.CodeSegment.startPc opSegment).toNat)
              (.prim op.toPrimOp) state =
            .ok (.running evmAfter) := by
        simp [Assembly.Source.stepAtResult, hStepAt,
          basicOp_toPrimOp_haltKind?_none op]
      have hOpenStep :
          OpenExternal.OpenResultResolves
            (OpenAssembly.Source.openStepAtResult program
              ((Structured.Preservation.CodeSegment.startPc opSegment).toNat)
              (.prim op.toPrimOp) state)
            [] (.ok (.running evmAfter)) :=
        OpenAssembly.Source.openStepAtResult_resolves_closed_of_prim_no_callCreate
          (program := program)
          (pc := (Structured.Preservation.CodeSegment.startPc opSegment).toNat)
          (op := op.toPrimOp)
          (state := state) (result := .running evmAfter)
          hNoCallCreate hStepResult
      have hAfterPc :
          evmAfter.pc =
            Structured.Preservation.CodeSegment.startPc opSegment +
              EvmYul.UInt256.ofNat 1 := by
        simp [evmAfter, hPcOp, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC]
      have hFallOp :
          Structured.Preservation.CodeSegment.fallthroughPc opSegment =
            Structured.Preservation.CodeSegment.startPc opSegment +
              EvmYul.UInt256.ofNat 1 := by
        simpa [Assembly.Instr.byteSize] using
          codeSegment_fallthroughPc_singleton opSegment
      have hFallSegment :
          Structured.Preservation.CodeSegment.fallthroughPc opSegment =
            Structured.Preservation.CodeSegment.fallthroughPc segment := by
        simp [opSegment, Structured.Preservation.CodeSegment.cast_code,
          Structured.Preservation.CodeSegment.fallthroughPc, hAssemblyCode]
      refine ⟨evmAfter, ?_, ?_, ?_⟩
      · constructor
        · simpa [evmAfter, EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC] using hShared
        · refine ⟨baseStack, ?_, hStackRel⟩
          simp [evmAfter, hStack, EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
      · rw [hFallSegment.symm, hFallOp]
        exact hAfterPc
      · intro tailTrace result hRest
        simpa using
          OpenAssembly.Source.openRunNResult_current_stepAt_running_continue
            (program := program) (fuel := fuel) (state := state)
            (mid := evmAfter)
            (pc := (Structured.Preservation.CodeSegment.startPc opSegment).toNat)
            (instr := .prim op.toPrimOp)
            hAt hOpenStep hRest

theorem compilerOpenLocalsExprSeq_nil_stackPrefix_openRunNResult_continue
    {prim : Objects.Source.PrimitiveSemantics}
    {layout : List Name}
    {compiler compilerAfter : Objects.Source.State}
    {state : EvmYul.EVM.State}
    (stackPrefix : List Word)
    (program : Assembly.Program) (fuel : Nat)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler stackPrefix state)
    {valuesAfter : List Word}
    {trace : OpenExternal.OpenTrace}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.evalSeq
          prim Locals.ExprSeq.nil compiler)
        trace (.ok (compilerAfter, valuesAfter))) :
    ∃ evmAfter : EvmYul.EVM.State,
      Locals.SourceLowering.StackPrefixRel layout compilerAfter
        (valuesAfter.reverse ++ stackPrefix) evmAfter ∧
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program fuel evmAfter)
          tailTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program fuel state)
          (trace ++ tailTrace) result := by
  rw [Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.evalSeq] at hResolve
  cases hResolve
  refine ⟨state, ?_, ?_⟩
  · simpa using hPrefixRel
  · intro tailTrace result hRest
    simpa using hRest

theorem compilerOpenLocalsExprSeq_nil_stackPrefix_openRunNResult_continue_of_compileCode
    {prim : Objects.Source.PrimitiveSemantics}
    {ctx : Locals.Ctx} {offset : Nat}
    {layout : List Name}
    {compiler compilerAfter : Objects.Source.State}
    {state : EvmYul.EVM.State}
    {code : Structured.Code}
    (hCompile :
      Locals.ExprSeq.compileCode ctx offset Locals.ExprSeq.nil = some code)
    (stackPrefix : List Word)
    (program : Assembly.Program) (fuel : Nat)
    (_segment :
      Structured.Preservation.CodeSegment program code.toAssembly)
    (_hPc :
      state.pc =
        Structured.Preservation.CodeSegment.startPc _segment)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler stackPrefix state)
    {valuesAfter : List Word}
    {trace : OpenExternal.OpenTrace}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.evalSeq
          prim Locals.ExprSeq.nil compiler)
        trace (.ok (compilerAfter, valuesAfter))) :
    ∃ evmAfter : EvmYul.EVM.State,
      Locals.SourceLowering.StackPrefixRel layout compilerAfter
        (valuesAfter.reverse ++ stackPrefix) evmAfter ∧
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program fuel evmAfter)
          tailTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program fuel state)
          (trace ++ tailTrace) result := by
  have hCode : code = [] :=
    localsExprSeq_compileCode_nil_eq hCompile
  exact
    compilerOpenLocalsExprSeq_nil_stackPrefix_openRunNResult_continue
      (prim := prim) (layout := layout) (compiler := compiler)
      (compilerAfter := compilerAfter) (state := state) stackPrefix program
      fuel hPrefixRel hResolve

theorem compilerOpenLocalsExprSeq_nil_stackPrefix_openRunNResult_continue_fallthrough_of_compileCode
    {prim : Objects.Source.PrimitiveSemantics}
    {ctx : Locals.Ctx} {offset : Nat}
    {layout : List Name}
    {compiler compilerAfter : Objects.Source.State}
    {state : EvmYul.EVM.State}
    {code : Structured.Code}
    (hCompile :
      Locals.ExprSeq.compileCode ctx offset Locals.ExprSeq.nil = some code)
    (stackPrefix : List Word)
    (program : Assembly.Program) (fuel : Nat)
    (segment :
      Structured.Preservation.CodeSegment program code.toAssembly)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler stackPrefix state)
    {valuesAfter : List Word}
    {trace : OpenExternal.OpenTrace}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.evalSeq
          prim Locals.ExprSeq.nil compiler)
        trace (.ok (compilerAfter, valuesAfter))) :
    ∃ evmAfter : EvmYul.EVM.State,
      Locals.SourceLowering.StackPrefixRel layout compilerAfter
        (valuesAfter.reverse ++ stackPrefix) evmAfter ∧
      evmAfter.pc =
        Structured.Preservation.CodeSegment.fallthroughPc segment ∧
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program fuel evmAfter)
          tailTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program fuel state)
          (trace ++ tailTrace) result := by
  have hCode : code = [] :=
    localsExprSeq_compileCode_nil_eq hCompile
  have hFall :
      Structured.Preservation.CodeSegment.fallthroughPc segment =
        Structured.Preservation.CodeSegment.startPc segment := by
    rcases segment with ⟨pre, post, hAsm, hFits⟩
    simp [Structured.Preservation.CodeSegment.fallthroughPc,
      Structured.Preservation.CodeSegment.startPc, hCode,
      Structured.Code.toAssembly]
  rw [Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.evalSeq] at hResolve
  cases hResolve
  refine ⟨state, ?_, ?_, ?_⟩
  · simpa using hPrefixRel
  · simpa [hFall] using hPc
  · intro tailTrace result hRest
    simpa using hRest

theorem compilerOpenLocalsExprSeq_cons_stackPrefix_openRunNResult_continue_of_head_tail
    {prim : Objects.Source.PrimitiveSemantics}
    {layout : List Name}
    {compiler compilerAfter : Objects.Source.State}
    {state : EvmYul.EVM.State}
    {left right : Nat}
    {head : Locals.Expr left}
    {tail : Locals.ExprSeq right}
    (stackPrefix : List Word)
    (program : Assembly.Program)
    (finalTailFuel tailFuel seqFuel : Nat)
    (hHeadSound :
      ∀ {headTrace : OpenExternal.OpenTrace}
        {compilerAfterHead : Objects.Source.State}
        {headValues : List Word},
        OpenExternal.OpenResultResolves
          (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.eval
            prim head compiler)
          headTrace (.ok (compilerAfterHead, headValues)) →
        ∃ evmAfterHead : EvmYul.EVM.State,
          Locals.SourceLowering.StackPrefixRel layout compilerAfterHead
            (headValues.reverse ++ stackPrefix) evmAfterHead ∧
          ∀ {tailTrace : OpenExternal.OpenTrace}
            {result : Except EVMException Assembly.StepResult},
            OpenExternal.OpenResultResolves
              (OpenAssembly.Source.openRunNResult program tailFuel
                evmAfterHead)
              tailTrace result →
            OpenExternal.OpenResultResolves
              (OpenAssembly.Source.openRunNResult program seqFuel state)
              (headTrace ++ tailTrace) result)
    (hTailSound :
      ∀ {compilerAfterHead compilerAfterTail : Objects.Source.State}
        {headValues tailValues : List Word}
        {evmAfterHead : EvmYul.EVM.State}
        {tailTrace : OpenExternal.OpenTrace},
        Locals.SourceLowering.StackPrefixRel layout compilerAfterHead
          (headValues.reverse ++ stackPrefix) evmAfterHead →
        OpenExternal.OpenResultResolves
          (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.evalSeq
            prim tail compilerAfterHead)
          tailTrace (.ok (compilerAfterTail, tailValues)) →
        ∃ evmAfterTail : EvmYul.EVM.State,
          Locals.SourceLowering.StackPrefixRel layout compilerAfterTail
            (tailValues.reverse ++ headValues.reverse ++ stackPrefix)
            evmAfterTail ∧
          ∀ {restTrace : OpenExternal.OpenTrace}
            {result : Except EVMException Assembly.StepResult},
            OpenExternal.OpenResultResolves
              (OpenAssembly.Source.openRunNResult program finalTailFuel
                evmAfterTail)
              restTrace result →
            OpenExternal.OpenResultResolves
              (OpenAssembly.Source.openRunNResult program tailFuel
                evmAfterHead)
              (tailTrace ++ restTrace) result)
    {valuesAfter : List Word}
    {trace : OpenExternal.OpenTrace}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.evalSeq
          prim (Locals.ExprSeq.cons head tail) compiler)
        trace (.ok (compilerAfter, valuesAfter))) :
    ∃ evmAfter : EvmYul.EVM.State,
      Locals.SourceLowering.StackPrefixRel layout compilerAfter
        (valuesAfter.reverse ++ stackPrefix) evmAfter ∧
      ∀ {restTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program finalTailFuel evmAfter)
          restTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program seqFuel state)
          (trace ++ restTrace) result := by
  rw [Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.evalSeq] at hResolve
  rcases OpenExternal.OpenResultResolves.bind_inv hResolve with
    hHeadError | hHeadOk
  · rcases hHeadError with ⟨err, _hHead, hResult⟩
    cases hResult
  · rcases hHeadOk with
      ⟨headTrace, tailAndDoneTrace, headResult, hTrace, hResolveHead,
        hResolveTailBind⟩
    rcases headResult with ⟨compilerAfterHead, headValues⟩
    rcases OpenExternal.OpenResultResolves.bind_inv hResolveTailBind with
      hTailError | hTailOk
    · rcases hTailError with ⟨err, _hTail, hResult⟩
      cases hResult
    · rcases hTailOk with
        ⟨tailTrace, doneTrace, tailResult, hTailAndDoneTrace,
          hResolveTail, hResolveDone⟩
      rcases tailResult with ⟨compilerAfterTail, tailValues⟩
      cases hResolveDone
      rcases hHeadSound hResolveHead with
        ⟨evmAfterHead, hHeadRel, hHeadCont⟩
      rcases hTailSound hHeadRel hResolveTail with
        ⟨evmAfterTail, hTailRel, hTailCont⟩
      refine ⟨evmAfterTail, ?_, ?_⟩
      · simpa [List.reverse_append, List.append_assoc] using hTailRel
      · intro restTrace result hRest
        have hTailAndRest :
            OpenExternal.OpenResultResolves
              (OpenAssembly.Source.openRunNResult program tailFuel
                evmAfterHead)
              (tailTrace ++ restTrace) result :=
          hTailCont hRest
        have hFull := hHeadCont hTailAndRest
        subst tailAndDoneTrace
        subst trace
        simpa [List.append_assoc] using hFull

theorem compilerOpenLocalsExprSeq_cons_stackPrefix_openRunNResult_continue_fallthrough_of_head_tail
    {prim : Objects.Source.PrimitiveSemantics}
    {layout : List Name}
    {compiler compilerAfter : Objects.Source.State}
    {state : EvmYul.EVM.State}
    {left right : Nat}
    {head : Locals.Expr left}
    {tail : Locals.ExprSeq right}
    (stackPrefix : List Word)
    (program : Assembly.Program)
    (finalTailFuel tailFuel seqFuel : Nat)
    (headFallthroughPc tailStartPc finalFallthroughPc : Word)
    (hHeadToTail : headFallthroughPc = tailStartPc)
    (hHeadSound :
      ∀ {headTrace : OpenExternal.OpenTrace}
        {compilerAfterHead : Objects.Source.State}
        {headValues : List Word},
        OpenExternal.OpenResultResolves
          (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.eval
            prim head compiler)
          headTrace (.ok (compilerAfterHead, headValues)) →
        ∃ evmAfterHead : EvmYul.EVM.State,
          Locals.SourceLowering.StackPrefixRel layout compilerAfterHead
            (headValues.reverse ++ stackPrefix) evmAfterHead ∧
          evmAfterHead.pc = headFallthroughPc ∧
          ∀ {tailTrace : OpenExternal.OpenTrace}
            {result : Except EVMException Assembly.StepResult},
            OpenExternal.OpenResultResolves
              (OpenAssembly.Source.openRunNResult program tailFuel
                evmAfterHead)
              tailTrace result →
            OpenExternal.OpenResultResolves
              (OpenAssembly.Source.openRunNResult program seqFuel state)
              (headTrace ++ tailTrace) result)
    (hTailSound :
      ∀ {compilerAfterHead compilerAfterTail : Objects.Source.State}
        {headValues tailValues : List Word}
        {evmAfterHead : EvmYul.EVM.State}
        {tailTrace : OpenExternal.OpenTrace},
        Locals.SourceLowering.StackPrefixRel layout compilerAfterHead
          (headValues.reverse ++ stackPrefix) evmAfterHead →
        evmAfterHead.pc = tailStartPc →
        OpenExternal.OpenResultResolves
          (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.evalSeq
            prim tail compilerAfterHead)
          tailTrace (.ok (compilerAfterTail, tailValues)) →
        ∃ evmAfterTail : EvmYul.EVM.State,
          Locals.SourceLowering.StackPrefixRel layout compilerAfterTail
            (tailValues.reverse ++ headValues.reverse ++ stackPrefix)
            evmAfterTail ∧
          evmAfterTail.pc = finalFallthroughPc ∧
          ∀ {restTrace : OpenExternal.OpenTrace}
            {result : Except EVMException Assembly.StepResult},
            OpenExternal.OpenResultResolves
              (OpenAssembly.Source.openRunNResult program finalTailFuel
                evmAfterTail)
              restTrace result →
            OpenExternal.OpenResultResolves
              (OpenAssembly.Source.openRunNResult program tailFuel
                evmAfterHead)
              (tailTrace ++ restTrace) result)
    {valuesAfter : List Word}
    {trace : OpenExternal.OpenTrace}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.evalSeq
          prim (Locals.ExprSeq.cons head tail) compiler)
        trace (.ok (compilerAfter, valuesAfter))) :
    ∃ evmAfter : EvmYul.EVM.State,
      Locals.SourceLowering.StackPrefixRel layout compilerAfter
        (valuesAfter.reverse ++ stackPrefix) evmAfter ∧
      evmAfter.pc = finalFallthroughPc ∧
      ∀ {restTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program finalTailFuel evmAfter)
          restTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program seqFuel state)
          (trace ++ restTrace) result := by
  rw [Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.evalSeq] at hResolve
  rcases OpenExternal.OpenResultResolves.bind_inv hResolve with
    hHeadError | hHeadOk
  · rcases hHeadError with ⟨err, _hHead, hResult⟩
    cases hResult
  · rcases hHeadOk with
      ⟨headTrace, tailAndDoneTrace, headResult, hTrace, hResolveHead,
        hResolveTailBind⟩
    rcases headResult with ⟨compilerAfterHead, headValues⟩
    rcases OpenExternal.OpenResultResolves.bind_inv hResolveTailBind with
      hTailError | hTailOk
    · rcases hTailError with ⟨err, _hTail, hResult⟩
      cases hResult
    · rcases hTailOk with
        ⟨tailTrace, doneTrace, tailResult, hTailAndDoneTrace,
          hResolveTail, hResolveDone⟩
      rcases tailResult with ⟨compilerAfterTail, tailValues⟩
      cases hResolveDone
      rcases hHeadSound hResolveHead with
        ⟨evmAfterHead, hHeadRel, hHeadPc, hHeadCont⟩
      have hAtTail : evmAfterHead.pc = tailStartPc := by
        simpa [hHeadToTail] using hHeadPc
      rcases hTailSound hHeadRel hAtTail hResolveTail with
        ⟨evmAfterTail, hTailRel, hTailPc, hTailCont⟩
      refine ⟨evmAfterTail, ?_, hTailPc, ?_⟩
      · simpa [List.reverse_append, List.append_assoc] using hTailRel
      · intro restTrace result hRest
        have hTailAndRest :
            OpenExternal.OpenResultResolves
              (OpenAssembly.Source.openRunNResult program tailFuel
                evmAfterHead)
              (tailTrace ++ restTrace) result :=
          hTailCont hRest
        have hFull := hHeadCont hTailAndRest
        subst tailAndDoneTrace
        subst trace
        simpa [List.append_assoc] using hFull

theorem compilerOpenLocalsExprSeq_cons_stackPrefix_openRunNResult_continue_fallthrough_of_compileCode_head_tail
    {prim : Objects.Source.PrimitiveSemantics}
    {ctx : Locals.Ctx} {offset : Nat}
    {layout : List Name}
    {compiler compilerAfter : Objects.Source.State}
    {state : EvmYul.EVM.State}
    {left right : Nat}
    {head : Locals.Expr left}
    {tail : Locals.ExprSeq right}
    {code : Structured.Code}
    (hCompile :
      Locals.ExprSeq.compileCode ctx offset
        (Locals.ExprSeq.cons head tail) = some code)
    (stackPrefix : List Word)
    (program : Assembly.Program)
    (finalTailFuel tailFuel seqFuel : Nat)
    (segment :
      Structured.Preservation.CodeSegment program code.toAssembly)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment)
    (hHeadSound :
      ∀ {headCode : Structured.Code},
        Locals.Expr.compileCode ctx offset head = some headCode →
        (headSegment :
          Structured.Preservation.CodeSegment program headCode.toAssembly) →
        state.pc =
          Structured.Preservation.CodeSegment.startPc headSegment →
        ∀ {headTrace : OpenExternal.OpenTrace}
          {compilerAfterHead : Objects.Source.State}
          {headValues : List Word},
          OpenExternal.OpenResultResolves
            (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.eval
              prim head compiler)
            headTrace (.ok (compilerAfterHead, headValues)) →
          ∃ evmAfterHead : EvmYul.EVM.State,
            Locals.SourceLowering.StackPrefixRel layout compilerAfterHead
              (headValues.reverse ++ stackPrefix) evmAfterHead ∧
            evmAfterHead.pc =
              Structured.Preservation.CodeSegment.fallthroughPc
                headSegment ∧
            ∀ {tailTrace : OpenExternal.OpenTrace}
              {result : Except EVMException Assembly.StepResult},
              OpenExternal.OpenResultResolves
                (OpenAssembly.Source.openRunNResult program tailFuel
                  evmAfterHead)
                tailTrace result →
              OpenExternal.OpenResultResolves
                (OpenAssembly.Source.openRunNResult program seqFuel state)
                (headTrace ++ tailTrace) result)
    (hTailSound :
      ∀ {tailCode : Structured.Code},
        Locals.ExprSeq.compileCode ctx (offset + left) tail =
          some tailCode →
        (tailSegment :
          Structured.Preservation.CodeSegment program tailCode.toAssembly) →
        ∀ {compilerAfterHead compilerAfterTail : Objects.Source.State}
          {headValues tailValues : List Word}
          {evmAfterHead : EvmYul.EVM.State}
          {tailTrace : OpenExternal.OpenTrace},
          evmAfterHead.pc =
            Structured.Preservation.CodeSegment.startPc tailSegment →
          Locals.SourceLowering.StackPrefixRel layout compilerAfterHead
            (headValues.reverse ++ stackPrefix) evmAfterHead →
          OpenExternal.OpenResultResolves
            (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.evalSeq
              prim tail compilerAfterHead)
            tailTrace (.ok (compilerAfterTail, tailValues)) →
          ∃ evmAfterTail : EvmYul.EVM.State,
            Locals.SourceLowering.StackPrefixRel layout compilerAfterTail
              (tailValues.reverse ++ headValues.reverse ++ stackPrefix)
              evmAfterTail ∧
            evmAfterTail.pc =
              Structured.Preservation.CodeSegment.fallthroughPc
                tailSegment ∧
            ∀ {restTrace : OpenExternal.OpenTrace}
              {result : Except EVMException Assembly.StepResult},
              OpenExternal.OpenResultResolves
                (OpenAssembly.Source.openRunNResult program finalTailFuel
                  evmAfterTail)
                restTrace result →
              OpenExternal.OpenResultResolves
                (OpenAssembly.Source.openRunNResult program tailFuel
                  evmAfterHead)
                (tailTrace ++ restTrace) result)
    {valuesAfter : List Word}
    {trace : OpenExternal.OpenTrace}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.evalSeq
          prim (Locals.ExprSeq.cons head tail) compiler)
        trace (.ok (compilerAfter, valuesAfter))) :
    ∃ evmAfter : EvmYul.EVM.State,
      Locals.SourceLowering.StackPrefixRel layout compilerAfter
        (valuesAfter.reverse ++ stackPrefix) evmAfter ∧
      evmAfter.pc =
        Structured.Preservation.CodeSegment.fallthroughPc segment ∧
      ∀ {restTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program finalTailFuel evmAfter)
          restTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program seqFuel state)
          (trace ++ restTrace) result := by
  rcases localsExprSeq_compileCode_cons_inv hCompile with
    ⟨headCode, tailCode, hHeadCompile, hTailCompile, hCode⟩
  have hAssemblyCode :
      code.toAssembly = headCode.toAssembly ++ tailCode.toAssembly := by
    simp [hCode, Structured.Code.toAssembly]
  let appendSegment :
      Structured.Preservation.CodeSegment program
        (headCode.toAssembly ++ tailCode.toAssembly) :=
    Structured.Preservation.CodeSegment.cast_code hAssemblyCode segment
  let headSegment :
      Structured.Preservation.CodeSegment program headCode.toAssembly :=
    Structured.Preservation.CodeSegment.left appendSegment
  let tailSegment :
      Structured.Preservation.CodeSegment program tailCode.toAssembly :=
    Structured.Preservation.CodeSegment.right appendSegment
  have hHeadPc :
      state.pc =
        Structured.Preservation.CodeSegment.startPc headSegment := by
    simpa [headSegment, appendSegment,
      Structured.Preservation.CodeSegment.left,
      Structured.Preservation.CodeSegment.cast_code,
      Structured.Preservation.CodeSegment.startPc] using hPc
  have hHeadToTail :
      Structured.Preservation.CodeSegment.fallthroughPc headSegment =
        Structured.Preservation.CodeSegment.startPc tailSegment := by
    exact
      (codeSegment_right_startPc_eq_left_fallthroughPc
        appendSegment).symm
  have hTailFallSegment :
      Structured.Preservation.CodeSegment.fallthroughPc tailSegment =
        Structured.Preservation.CodeSegment.fallthroughPc segment := by
    simp [tailSegment, appendSegment,
      Structured.Preservation.CodeSegment.right,
      Structured.Preservation.CodeSegment.cast_code,
      Structured.Preservation.CodeSegment.fallthroughPc,
      hAssemblyCode, List.append_assoc]
  rcases
      compilerOpenLocalsExprSeq_cons_stackPrefix_openRunNResult_continue_fallthrough_of_head_tail
        (prim := prim) (layout := layout) (compiler := compiler)
        (compilerAfter := compilerAfter) (state := state)
        (left := left) (right := right) (head := head) (tail := tail)
        stackPrefix program finalTailFuel tailFuel seqFuel
        (Structured.Preservation.CodeSegment.fallthroughPc headSegment)
        (Structured.Preservation.CodeSegment.startPc tailSegment)
        (Structured.Preservation.CodeSegment.fallthroughPc tailSegment)
        hHeadToTail
        (fun {headTrace compilerAfterHead headValues} hResolveHead =>
          hHeadSound hHeadCompile headSegment hHeadPc hResolveHead)
        (fun {compilerAfterHead compilerAfterTail headValues tailValues
              evmAfterHead tailTrace}
            hHeadRel hAtTail hResolveTail =>
          hTailSound hTailCompile tailSegment hAtTail hHeadRel
            hResolveTail)
        hResolve with
    ⟨evmAfter, hRel, hPcTail, hCont⟩
  refine ⟨evmAfter, hRel, ?_, hCont⟩
  simpa [hTailFallSegment] using hPcTail

mutual
  theorem compilerOpenLocalsExpr_stackPrefix_openRunNResult_continue_fallthrough_of_compileCode
      {prim : Objects.Source.PrimitiveSemantics}
      (hPrim : Locals.SourceLowering.PrimitiveSound prim) :
      ∀ {results : Nat} {expr : Locals.Expr results}
        {ctx : Locals.Ctx} {offset : Nat} {layout : List Name}
        {compiler compilerAfter : Objects.Source.State}
        {state : EvmYul.EVM.State} {code : Structured.Code},
        Locals.Source.Expr.SourceOwned expr →
        LocalsExprOpenSupported expr →
        Locals.SourceLowering.Expr.Accessible layout offset expr →
        Locals.Expr.compileCode ctx offset expr = some code →
        ctx.layout = layout →
        layout.Nodup →
        (stackPrefix : List Word) →
        stackPrefix.length = offset →
        (program : Assembly.Program) →
        (tailFuel : Nat) →
        (segment :
          Structured.Preservation.CodeSegment program code.toAssembly) →
        state.pc = Structured.Preservation.CodeSegment.startPc segment →
        Locals.SourceLowering.StackPrefixRel layout compiler stackPrefix
          state →
        ∀ {valuesAfter : List Word} {trace : OpenExternal.OpenTrace},
          OpenExternal.OpenResultResolves
            (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.eval
              prim expr compiler)
            trace (.ok (compilerAfter, valuesAfter)) →
          ∃ evmAfter : EvmYul.EVM.State,
            Locals.SourceLowering.StackPrefixRel layout compilerAfter
              (valuesAfter.reverse ++ stackPrefix) evmAfter ∧
            evmAfter.pc =
              Structured.Preservation.CodeSegment.fallthroughPc segment ∧
            ∀ {tailTrace : OpenExternal.OpenTrace}
              {result : Except EVMException Assembly.StepResult},
              OpenExternal.OpenResultResolves
                (OpenAssembly.Source.openRunNResult program tailFuel
                  evmAfter)
                tailTrace result →
              OpenExternal.OpenResultResolves
                (OpenAssembly.Source.openRunNResult program
                  (code.length + tailFuel) state)
                (trace ++ tailTrace) result := by
    intro results expr
    cases expr with
    | lit value =>
        intro ctx offset layout compiler compilerAfter state code
          _hOwned _hSupported _hAccess hCompile _hCtxLayout _hNoDup
          stackPrefix _hPrefixLen program tailFuel segment hPc hPrefixRel
          valuesAfter trace hResolve
        rcases
            compilerOpenLocalsExpr_lit_stackPrefix_openRunNResult_continue_fallthrough_of_compileCode
              (prim := prim) (ctx := ctx) (offset := offset)
              (layout := layout) (compiler := compiler)
              (compilerAfter := compilerAfter) (state := state)
              (value := value) hCompile stackPrefix program tailFuel
              segment hPc hPrefixRel hResolve with
          ⟨evmAfter, hRel, hAfterPc, hCont⟩
        refine ⟨evmAfter, hRel, hAfterPc, ?_⟩
        intro tailTrace result hRest
        have hCode :
            code = [Structured.BasicInstr.push value] :=
          localsExpr_compileCode_lit_eq hCompile
        have hFuel : tailFuel + 1 = code.length + tailFuel := by
          simp [hCode, Nat.add_comm]
        simpa [hFuel] using hCont hRest
    | var name =>
        intro ctx offset layout compiler compilerAfter state code
          _hOwned _hSupported hAccess hCompile hCtxLayout hNoDup
          stackPrefix hPrefixLen program tailFuel segment hPc hPrefixRel
          valuesAfter trace hResolve
        rcases
            compilerOpenLocalsExpr_var_stackPrefix_openRunNResult_continue_fallthrough_of_compileCode
              (prim := prim) (ctx := ctx) (offset := offset)
              (layout := layout) (compiler := compiler)
              (compilerAfter := compilerAfter) (state := state)
              (name := name) hCompile hCtxLayout hNoDup hAccess
              stackPrefix hPrefixLen program tailFuel segment hPc
              hPrefixRel hResolve with
          ⟨evmAfter, hRel, hAfterPc, hCont⟩
        refine ⟨evmAfter, hRel, hAfterPc, ?_⟩
        intro tailTrace result hRest
        rcases localsExpr_compileCode_var_inv hCompile with
          ⟨depth, op, _hDepth, _hDup, hCode⟩
        have hFuel : tailFuel + 1 = code.length + tailFuel := by
          simp [hCode, Nat.add_comm]
        simpa [hFuel] using hCont hRest
    | code code' =>
        intro ctx offset layout compiler compilerAfter state code
          hOwned _hSupported _hAccess _hCompile _hCtxLayout _hNoDup
          stackPrefix _hPrefixLen program tailFuel segment hPc hPrefixRel
          valuesAfter trace hResolve
        simp [Locals.Source.Expr.SourceOwned] at hOwned
    | prim op args =>
        intro ctx offset layout compiler compilerAfter state code
          hOwned hSupported hAccess hCompile hCtxLayout hNoDup
          stackPrefix hPrefixLen program tailFuel segment hPc hPrefixRel
          valuesAfter trace hResolve
        have hArgsOwned : Locals.Source.ExprSeq.SourceOwned args := by
          simpa [Locals.Source.Expr.SourceOwned] using hOwned
        simp [LocalsExprOpenSupported] at hSupported
        rcases hSupported with ⟨hArgsSupported, hOpSupported⟩
        rcases
            compilerOpenLocalsExpr_prim_stackPrefix_openRunNResult_continue_fallthrough_of_compileCode_args
              (prim := prim) hPrim (ctx := ctx) (offset := offset)
              (layout := layout) (compiler := compiler)
              (compilerAfter := compilerAfter) (state := state)
              (op := op) (args := args) hCompile hArgsOwned hOpSupported
              stackPrefix program tailFuel (code.length + tailFuel)
              segment hPc
              (fun {argsCode} hArgsCompile argsSegment hArgsPc
                  {argsTrace compilerAfterArgs argValues}
                  hResolveArgs => by
                rcases
                    compilerOpenLocalsExprSeq_stackPrefix_openRunNResult_continue_fallthrough_of_compileCode
                      hPrim hArgsOwned hArgsSupported hAccess
                      hArgsCompile hCtxLayout hNoDup stackPrefix
                      hPrefixLen program (tailFuel + 1) argsSegment
                      hArgsPc hPrefixRel hResolveArgs with
                  ⟨evmAfterArgs, hArgsRel, hArgsAfterPc, hArgsCont⟩
                refine ⟨evmAfterArgs, hArgsRel, hArgsAfterPc, ?_⟩
                intro tailTrace result hRest
                have hFuel :
                    argsCode.length + (tailFuel + 1) =
                      code.length + tailFuel := by
                  rcases localsExpr_compileCode_prim_inv hCompile with
                    ⟨argsCode', hArgsCompile', hCode⟩
                  rw [hArgsCompile] at hArgsCompile'
                  cases hArgsCompile'
                  simp [hCode, Nat.add_comm, Nat.add_left_comm]
                simpa [hFuel] using hArgsCont hRest)
              hResolve with
          ⟨evmAfter, hRel, hAfterPc, hCont⟩
        exact ⟨evmAfter, hRel, hAfterPc, hCont⟩

  theorem compilerOpenLocalsExprSeq_stackPrefix_openRunNResult_continue_fallthrough_of_compileCode
      {prim : Objects.Source.PrimitiveSemantics}
      (hPrim : Locals.SourceLowering.PrimitiveSound prim) :
      ∀ {results : Nat} {exprs : Locals.ExprSeq results}
        {ctx : Locals.Ctx} {offset : Nat} {layout : List Name}
        {compiler compilerAfter : Objects.Source.State}
        {state : EvmYul.EVM.State} {code : Structured.Code},
        Locals.Source.ExprSeq.SourceOwned exprs →
        LocalsExprSeqOpenSupported exprs →
        Locals.SourceLowering.ExprSeq.Accessible layout offset exprs →
        Locals.ExprSeq.compileCode ctx offset exprs = some code →
        ctx.layout = layout →
        layout.Nodup →
        (stackPrefix : List Word) →
        stackPrefix.length = offset →
        (program : Assembly.Program) →
        (tailFuel : Nat) →
        (segment :
          Structured.Preservation.CodeSegment program code.toAssembly) →
        state.pc = Structured.Preservation.CodeSegment.startPc segment →
        Locals.SourceLowering.StackPrefixRel layout compiler stackPrefix
          state →
        ∀ {valuesAfter : List Word} {trace : OpenExternal.OpenTrace},
          OpenExternal.OpenResultResolves
            (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.evalSeq
              prim exprs compiler)
            trace (.ok (compilerAfter, valuesAfter)) →
          ∃ evmAfter : EvmYul.EVM.State,
            Locals.SourceLowering.StackPrefixRel layout compilerAfter
              (valuesAfter.reverse ++ stackPrefix) evmAfter ∧
            evmAfter.pc =
              Structured.Preservation.CodeSegment.fallthroughPc segment ∧
            ∀ {tailTrace : OpenExternal.OpenTrace}
              {result : Except EVMException Assembly.StepResult},
              OpenExternal.OpenResultResolves
                (OpenAssembly.Source.openRunNResult program tailFuel
                  evmAfter)
                tailTrace result →
              OpenExternal.OpenResultResolves
                (OpenAssembly.Source.openRunNResult program
                  (code.length + tailFuel) state)
                (trace ++ tailTrace) result := by
    intro results exprs
    cases exprs with
    | nil =>
        intro ctx offset layout compiler compilerAfter state code
          _hOwned _hSupported _hAccess hCompile _hCtxLayout _hNoDup
          stackPrefix _hPrefixLen program tailFuel segment hPc hPrefixRel
          valuesAfter trace hResolve
        rcases
            compilerOpenLocalsExprSeq_nil_stackPrefix_openRunNResult_continue_fallthrough_of_compileCode
              (prim := prim) (ctx := ctx) (offset := offset)
              (layout := layout) (compiler := compiler)
              (compilerAfter := compilerAfter) (state := state)
              hCompile stackPrefix program tailFuel segment hPc hPrefixRel
              hResolve with
          ⟨evmAfter, hRel, hAfterPc, hCont⟩
        refine ⟨evmAfter, hRel, hAfterPc, ?_⟩
        intro tailTrace result hRest
        have hCode : code = [] :=
          localsExprSeq_compileCode_nil_eq hCompile
        simpa [hCode] using hCont hRest
    | @cons left right head tail =>
        intro ctx offset layout compiler compilerAfter state code
          hOwned hSupported hAccess hCompile hCtxLayout hNoDup
          stackPrefix hPrefixLen program tailFuel segment hPc hPrefixRel
          valuesAfter trace hResolve
        simp [Locals.Source.ExprSeq.SourceOwned] at hOwned
        rcases hOwned with ⟨hHeadOwned, hTailOwned⟩
        simp [LocalsExprSeqOpenSupported] at hSupported
        rcases hSupported with ⟨hHeadSupported, hTailSupported⟩
        simp [Locals.SourceLowering.ExprSeq.Accessible] at hAccess
        rcases hAccess with ⟨hHeadAccess, hTailAccess⟩
        rcases localsExprSeq_compileCode_cons_inv hCompile with
          ⟨headCode, tailCode, hHeadCompile, hTailCompile, hCode⟩
        have hAssemblyCode :
            code.toAssembly =
              headCode.toAssembly ++ tailCode.toAssembly := by
          simp [hCode, Structured.Code.toAssembly]
        let appendSegment :
            Structured.Preservation.CodeSegment program
              (headCode.toAssembly ++ tailCode.toAssembly) :=
          Structured.Preservation.CodeSegment.cast_code hAssemblyCode segment
        let headSegment :
            Structured.Preservation.CodeSegment program
              headCode.toAssembly :=
          Structured.Preservation.CodeSegment.left appendSegment
        let tailSegment :
            Structured.Preservation.CodeSegment program
              tailCode.toAssembly :=
          Structured.Preservation.CodeSegment.right appendSegment
        have hHeadPc :
            state.pc =
              Structured.Preservation.CodeSegment.startPc headSegment := by
          simpa [headSegment, appendSegment,
            Structured.Preservation.CodeSegment.left,
            Structured.Preservation.CodeSegment.cast_code,
            Structured.Preservation.CodeSegment.startPc] using hPc
        have hHeadToTail :
            Structured.Preservation.CodeSegment.fallthroughPc headSegment =
              Structured.Preservation.CodeSegment.startPc tailSegment :=
          (codeSegment_right_startPc_eq_left_fallthroughPc appendSegment).symm
        have hTailFallSegment :
            Structured.Preservation.CodeSegment.fallthroughPc tailSegment =
              Structured.Preservation.CodeSegment.fallthroughPc segment := by
          simp [tailSegment, appendSegment,
            Structured.Preservation.CodeSegment.right,
            Structured.Preservation.CodeSegment.cast_code,
            Structured.Preservation.CodeSegment.fallthroughPc,
            hAssemblyCode, List.append_assoc]
        rw [Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.evalSeq] at hResolve
        rcases OpenExternal.OpenResultResolves.bind_inv hResolve with
          hHeadError | hHeadOk
        · rcases hHeadError with ⟨err, _hHead, hResult⟩
          cases hResult
        · rcases hHeadOk with
            ⟨headTrace, tailAndDoneTrace, headResult, hTrace,
              hResolveHead, hResolveTailBind⟩
          rcases headResult with ⟨compilerAfterHead, headValues⟩
          rcases OpenExternal.OpenResultResolves.bind_inv
              hResolveTailBind with
            hTailError | hTailOk
          · rcases hTailError with ⟨err, _hTail, hResult⟩
            cases hResult
          · rcases hTailOk with
              ⟨tailTrace, doneTrace, tailResult, hTailAndDoneTrace,
                hResolveTail, hResolveDone⟩
            rcases tailResult with ⟨compilerAfterTail, tailValues⟩
            cases hResolveDone
            rcases
                compilerOpenLocalsExpr_stackPrefix_openRunNResult_continue_fallthrough_of_compileCode
                  hPrim hHeadOwned hHeadSupported hHeadAccess
                  hHeadCompile hCtxLayout hNoDup stackPrefix hPrefixLen
                  program (tailCode.length + tailFuel) headSegment
                  hHeadPc hPrefixRel hResolveHead with
              ⟨evmAfterHead, hHeadRel, hHeadAfterPc, hHeadCont⟩
            have hHeadLen :
                headValues.length = left :=
              compilerOpenLocalsExpr_eval_resolves_ok_length_of_sourceOwned
                hPrim hHeadOwned hResolveHead
            have hTailPrefixLen :
                (headValues.reverse ++ stackPrefix).length =
                  offset + left := by
              simp [List.length_reverse, hHeadLen, hPrefixLen,
                Nat.add_comm]
            have hTailPc :
                evmAfterHead.pc =
                  Structured.Preservation.CodeSegment.startPc tailSegment := by
              rw [hHeadAfterPc]
              exact hHeadToTail
            rcases
                compilerOpenLocalsExprSeq_stackPrefix_openRunNResult_continue_fallthrough_of_compileCode
                  hPrim hTailOwned hTailSupported hTailAccess
                  hTailCompile hCtxLayout hNoDup
                  (headValues.reverse ++ stackPrefix) hTailPrefixLen
                  program tailFuel tailSegment hTailPc hHeadRel
                  hResolveTail with
              ⟨evmAfterTail, hTailRel, hTailAfterPc, hTailCont⟩
            refine ⟨evmAfterTail, ?_, ?_, ?_⟩
            · simpa [List.reverse_append, List.append_assoc] using
                hTailRel
            · simpa [hTailFallSegment] using hTailAfterPc
            · intro restTrace result hRest
              have hTailAndRest :
                  OpenExternal.OpenResultResolves
                    (OpenAssembly.Source.openRunNResult program
                      (tailCode.length + tailFuel) evmAfterHead)
                    (tailTrace ++ restTrace) result :=
                hTailCont hRest
              have hFull := hHeadCont hTailAndRest
              have hFuel :
                  headCode.length + (tailCode.length + tailFuel) =
                    code.length + tailFuel := by
                simp [hCode, Nat.add_assoc]
              subst tailAndDoneTrace
              subst trace
              simpa [List.append_assoc, hFuel] using hFull
end

theorem stackPrefixRel_singleton_to_cons_insert
    {layout : List Name} {source : Objects.Source.State}
    {evm : EvmYul.EVM.State} {name : Name} {value : Word}
    (hFresh : name ∉ layout)
    (hRel :
      Locals.SourceLowering.StackPrefixRel layout source [value] evm) :
    Locals.SourceLowering.StackPrefixRel (name :: layout)
      (source.insert name value) [] evm := by
  rcases hRel with ⟨hShared, baseStack, hStack, hStore⟩
  refine ⟨by simpa [Locals.Source.State.insert] using hShared,
    value :: baseStack, ?_, ?_⟩
  · simp [hStack]
  · simpa [Locals.Source.State.insert] using
      (Locals.SourceLowering.StackStoreRel.cons_insert
        (layout := layout) (store := source.vars)
        (stack := baseStack) (name := name) (value := value)
        hFresh hStore)

theorem compilerOpenLocalsExpr_zero_stackPrefix_openRunNResult_continue_fallthrough_of_compileCode
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {expr : Locals.Expr 0}
    {ctx : Locals.Ctx} {layout : List Name}
    {compiler compilerAfter : Objects.Source.State}
    {state : EvmYul.EVM.State} {code : Structured.Code}
    (hOwned : Locals.Source.Expr.SourceOwned expr)
    (hSupported : LocalsExprOpenSupported expr)
    (hAccess : Locals.SourceLowering.Expr.Accessible layout 0 expr)
    (hCompile : Locals.Expr.compileCode ctx 0 expr = some code)
    (hCtxLayout : ctx.layout = layout)
    (hNoDup : layout.Nodup)
    (program : Assembly.Program)
    (tailFuel : Nat)
    (segment :
      Structured.Preservation.CodeSegment program code.toAssembly)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler [] state)
    {valuesAfter : List Word} {trace : OpenExternal.OpenTrace}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.eval
          prim expr compiler)
        trace (.ok (compilerAfter, valuesAfter))) :
    ∃ evmAfter : EvmYul.EVM.State,
      Locals.SourceLowering.StackPrefixRel layout compilerAfter []
        evmAfter ∧
      evmAfter.pc =
        Structured.Preservation.CodeSegment.fallthroughPc segment ∧
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program tailFuel evmAfter)
          tailTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program
            (code.length + tailFuel) state)
          (trace ++ tailTrace) result := by
  rcases
      compilerOpenLocalsExpr_stackPrefix_openRunNResult_continue_fallthrough_of_compileCode
        hPrim hOwned hSupported hAccess hCompile hCtxLayout hNoDup
        [] rfl program tailFuel segment hPc hPrefixRel hResolve with
    ⟨evmAfter, hRel, hAfterPc, hCont⟩
  have hValuesLen :
      valuesAfter.length = 0 :=
    compilerOpenLocalsExpr_eval_resolves_ok_length_of_sourceOwned
      hPrim hOwned hResolve
  have hValuesNil : valuesAfter = [] := by
    cases valuesAfter with
    | nil => rfl
    | cons _ _ =>
        simp at hValuesLen
  refine ⟨evmAfter, ?_, hAfterPc, hCont⟩
  simpa [hValuesNil] using hRel

theorem compilerOpenLocalsExpr_evalOne_resolves_ok_inv
    {prim : Objects.Source.PrimitiveSemantics}
    {results : Nat} {expr : Locals.Expr results}
    {compiler compilerAfter : Objects.Source.State}
    {value : Word} {trace : OpenExternal.OpenTrace}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.evalOne
          prim expr compiler)
        trace (.ok (compilerAfter, value))) :
    OpenExternal.OpenResultResolves
      (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.eval
        prim expr compiler)
      trace (.ok (compilerAfter, [value])) := by
  rw [Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.evalOne] at hResolve
  rcases OpenExternal.OpenResultResolves.bind_inv hResolve with
    hEvalError | hEvalOk
  · rcases hEvalError with ⟨err, _hEval, hResult⟩
    cases hResult
  · rcases hEvalOk with
      ⟨evalTrace, doneTrace, evalResult, hTrace, hEval, hDone⟩
    rcases evalResult with ⟨compilerAfterEval, values⟩
    cases values with
    | nil =>
        simp [Reference.SourceBridgeFacts.CompilerOpen.invalid] at hDone
        cases hDone
    | cons head tail =>
        cases tail with
        | nil =>
            simp at hDone
            cases hDone
            subst trace
            simpa using hEval
        | cons second rest =>
            simp [Reference.SourceBridgeFacts.CompilerOpen.invalid] at hDone
            cases hDone

theorem compilerOpenLocalsExpr_one_insert_openRunNResult_continue_fallthrough_of_compileCode
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {expr : Locals.Expr 1}
    {ctx : Locals.Ctx} {layout : List Name}
    {compiler compilerAfter : Objects.Source.State}
    {state : EvmYul.EVM.State} {code : Structured.Code}
    {name : Name} {value : Word}
    (hOwned : Locals.Source.Expr.SourceOwned expr)
    (hSupported : LocalsExprOpenSupported expr)
    (hAccess : Locals.SourceLowering.Expr.Accessible layout 0 expr)
    (hCompile : Locals.Expr.compileCode ctx 0 expr = some code)
    (hCtxLayout : ctx.layout = layout)
    (hNoDup : layout.Nodup)
    (hFresh : name ∉ layout)
    (program : Assembly.Program)
    (tailFuel : Nat)
    (segment :
      Structured.Preservation.CodeSegment program code.toAssembly)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler [] state)
    {trace : OpenExternal.OpenTrace}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.eval
          prim expr compiler)
        trace (.ok (compilerAfter, [value]))) :
    ∃ evmAfter : EvmYul.EVM.State,
      Locals.SourceLowering.StackPrefixRel (name :: layout)
        (compilerAfter.insert name value) [] evmAfter ∧
      evmAfter.pc =
        Structured.Preservation.CodeSegment.fallthroughPc segment ∧
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program tailFuel evmAfter)
          tailTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program
            (code.length + tailFuel) state)
          (trace ++ tailTrace) result := by
  rcases
      compilerOpenLocalsExpr_stackPrefix_openRunNResult_continue_fallthrough_of_compileCode
        hPrim hOwned hSupported hAccess hCompile hCtxLayout hNoDup
        [] rfl program tailFuel segment hPc hPrefixRel hResolve with
    ⟨evmAfter, hRel, hAfterPc, hCont⟩
  refine ⟨evmAfter, ?_, hAfterPc, hCont⟩
  exact stackPrefixRel_singleton_to_cons_insert hFresh (by simpa using hRel)

theorem compilerOpenLocalsExpr_evalOne_insert_openRunNResult_continue_fallthrough_of_compileCode
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {expr : Locals.Expr 1}
    {ctx : Locals.Ctx} {layout : List Name}
    {compiler compilerAfter : Objects.Source.State}
    {state : EvmYul.EVM.State} {code : Structured.Code}
    {name : Name} {value : Word}
    (hOwned : Locals.Source.Expr.SourceOwned expr)
    (hSupported : LocalsExprOpenSupported expr)
    (hAccess : Locals.SourceLowering.Expr.Accessible layout 0 expr)
    (hCompile : Locals.Expr.compileCode ctx 0 expr = some code)
    (hCtxLayout : ctx.layout = layout)
    (hNoDup : layout.Nodup)
    (hFresh : name ∉ layout)
    (program : Assembly.Program)
    (tailFuel : Nat)
    (segment :
      Structured.Preservation.CodeSegment program code.toAssembly)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler [] state)
    {trace : OpenExternal.OpenTrace}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.evalOne
          prim expr compiler)
        trace (.ok (compilerAfter, value))) :
    ∃ evmAfter : EvmYul.EVM.State,
      Locals.SourceLowering.StackPrefixRel (name :: layout)
        (compilerAfter.insert name value) [] evmAfter ∧
      evmAfter.pc =
        Structured.Preservation.CodeSegment.fallthroughPc segment ∧
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program tailFuel evmAfter)
          tailTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program
            (code.length + tailFuel) state)
          (trace ++ tailTrace) result := by
  exact
    compilerOpenLocalsExpr_one_insert_openRunNResult_continue_fallthrough_of_compileCode
      hPrim hOwned hSupported hAccess hCompile hCtxLayout hNoDup hFresh
      program tailFuel segment hPc hPrefixRel
      (compilerOpenLocalsExpr_evalOne_resolves_ok_inv hResolve)

theorem compilerOpenAssignTail_stackPrefix_openRunNResult_continue_fallthrough
    {layout : List Name} {source : Objects.Source.State}
    {state : EvmYul.EVM.State}
    {name : Name} {idx : Nat} {value : Word}
    {swapOp : Structured.BasicOp}
    (hNoDup : layout.Nodup)
    (hName : layout[idx]? = some name)
    (hBound : idx + 1 ≤ 16)
    (hSwap : Locals.StackOp.swap? (idx + 1) = some swapOp)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout source [value] state)
    (program : Assembly.Program) (tailFuel : Nat)
    (segment :
      Structured.Preservation.CodeSegment program
        ([Assembly.Instr.prim swapOp.toPrimOp] ++
          [Assembly.Instr.prim Structured.BasicOp.pop.toPrimOp]))
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment) :
    ∃ evmAfter : EvmYul.EVM.State,
      Locals.SourceLowering.StackPrefixRel layout
        (source.withVars (Locals.Source.Store.insert source.vars name value))
        [] evmAfter ∧
      evmAfter.pc =
        Structured.Preservation.CodeSegment.fallthroughPc segment ∧
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program tailFuel evmAfter)
          tailTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program
            (2 + tailFuel) state)
          tailTrace result := by
  rcases hPrefixRel with ⟨hShared, baseStack, hStack, hStoreRel⟩
  rcases Locals.SourceLowering.StackStoreRel.lookup_value hStoreRel hName with
    ⟨oldAtIdx, hOld, _hOldStore⟩
  let swappedEVM :=
    state.replaceStackAndIncrPC
      (oldAtIdx :: baseStack.take idx ++ [value] ++
        baseStack.drop (idx + 1))
  let finalStack :=
    baseStack.take idx ++ value :: baseStack.drop (idx + 1)
  let finalEVM := swappedEVM.replaceStackAndIncrPC finalStack
  let swapSegment :
      Structured.Preservation.CodeSegment program
        [Assembly.Instr.prim swapOp.toPrimOp] :=
    Structured.Preservation.CodeSegment.left segment
  let popSegment :
      Structured.Preservation.CodeSegment program
        [Assembly.Instr.prim Structured.BasicOp.pop.toPrimOp] :=
    Structured.Preservation.CodeSegment.right segment
  have hPcSwap :
      state.pc =
        Structured.Preservation.CodeSegment.startPc swapSegment := by
    simpa [swapSegment, Structured.Preservation.CodeSegment.left,
      Structured.Preservation.CodeSegment.startPc] using hPc
  have hAtSwap :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some
          ((Structured.Preservation.CodeSegment.startPc swapSegment).toNat,
            Assembly.Instr.prim swapOp.toPrimOp) := by
    simpa [hPcSwap] using codeSegment_instrAtPc_start_cons swapSegment
  have hSwapRun :
      EvmYul.swap (idx + 1) state = .ok swappedEVM := by
    simpa [swappedEVM, hStack] using
      (Locals.SourceLowering.Assignment.evm_swap_assign_get?
        (state := state) (locals := baseStack) (idx := idx)
        (old := oldAtIdx) (value := value)
        (by simpa using hStack) hOld)
  have hSwapStep :
      Structured.BasicOp.step swapOp state = .ok swappedEVM := by
    rcases
        Locals.SourceLowering.Assignment.stackOp_swap?_step_eq_swap
          (n := idx + 1) (by omega) hBound state with
      ⟨op', hSwap', hStepEq⟩
    have hOp : swapOp = op' := by
      rw [hSwap] at hSwap'
      cases hSwap'
      rfl
    rw [hOp, hStepEq]
    exact hSwapRun
  have hSwapNoCall :
      swapOp.toPrimOp.isCallCreate = false :=
    Locals.CompilerFacts.StackOp.swap?_not_callCreate (idx + 1) hSwap
  have hSwapStepAt :
      Assembly.Source.stepAt program
          ((Structured.Preservation.CodeSegment.startPc swapSegment).toNat)
          (.prim swapOp.toPrimOp) state =
        .ok swappedEVM := by
    simpa [Assembly.Source.stepAt, Structured.BasicOp.step] using
      hSwapStep
  have hSwapStepResult :
      Assembly.Source.stepAtResult program
          ((Structured.Preservation.CodeSegment.startPc swapSegment).toNat)
          (.prim swapOp.toPrimOp) state =
        .ok (.running swappedEVM) := by
    simp [Assembly.Source.stepAtResult, hSwapStepAt,
      basicOp_toPrimOp_haltKind?_none swapOp]
  have hOpenSwap :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openStepAtResult program
          ((Structured.Preservation.CodeSegment.startPc swapSegment).toNat)
          (.prim swapOp.toPrimOp) state)
        [] (.ok (.running swappedEVM)) :=
    OpenAssembly.Source.openStepAtResult_resolves_closed_of_prim_no_callCreate
      (program := program)
      (pc := (Structured.Preservation.CodeSegment.startPc swapSegment).toNat)
      (op := swapOp.toPrimOp) (state := state)
      (result := .running swappedEVM) hSwapNoCall hSwapStepResult
  have hSwapPc :
      swappedEVM.pc =
        Structured.Preservation.CodeSegment.startPc popSegment := by
    have hStepPc :
        swappedEVM.pc = state.pc + EvmYul.UInt256.ofNat 1 :=
      basicOp_no_callCreate_step_pc hSwapNoCall hSwapStep
    have hSwapFall :
        Structured.Preservation.CodeSegment.fallthroughPc swapSegment =
          Structured.Preservation.CodeSegment.startPc swapSegment +
            EvmYul.UInt256.ofNat 1 := by
      simpa [Structured.BasicInstr.toAssembly, Structured.BasicOp.toPrimOp,
        Assembly.Instr.byteSize] using
        codeSegment_fallthroughPc_singleton swapSegment
    have hPopStart :
        Structured.Preservation.CodeSegment.startPc popSegment =
          Structured.Preservation.CodeSegment.fallthroughPc swapSegment :=
      codeSegment_right_startPc_eq_left_fallthroughPc segment
    rw [hStepPc, hPcSwap, hPopStart, hSwapFall]
  have hAtPop :
      Assembly.Program.instrAtPc program swappedEVM.pc.toNat =
        some
          ((Structured.Preservation.CodeSegment.startPc popSegment).toNat,
            Assembly.Instr.prim Structured.BasicOp.pop.toPrimOp) := by
    simpa [hSwapPc] using codeSegment_instrAtPc_start_cons popSegment
  have hPopStep :
      Structured.BasicOp.step Structured.BasicOp.pop swappedEVM =
        .ok finalEVM := by
    simp [Structured.BasicOp.step, Structured.BasicOp.toPrimOp,
      Assembly.Target.stepInstr, Assembly.PrimOp.step,
      Assembly.PrimStep.run, Assembly.PrimOp.continuingStep?,
      EvmYul.Stack.pop, swappedEVM, finalEVM, finalStack,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, List.append_assoc]
  have hPopStepAt :
      Assembly.Source.stepAt program
          ((Structured.Preservation.CodeSegment.startPc popSegment).toNat)
          (.prim Structured.BasicOp.pop.toPrimOp) swappedEVM =
        .ok finalEVM := by
    simpa [Assembly.Source.stepAt, Structured.BasicOp.step] using
      hPopStep
  have hPopStepResult :
      Assembly.Source.stepAtResult program
          ((Structured.Preservation.CodeSegment.startPc popSegment).toNat)
          (.prim Structured.BasicOp.pop.toPrimOp) swappedEVM =
        .ok (.running finalEVM) := by
    simp [Assembly.Source.stepAtResult, hPopStepAt,
      basicOp_toPrimOp_haltKind?_none Structured.BasicOp.pop]
  have hOpenPop :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openStepAtResult program
          ((Structured.Preservation.CodeSegment.startPc popSegment).toNat)
          (.prim Structured.BasicOp.pop.toPrimOp) swappedEVM)
        [] (.ok (.running finalEVM)) :=
    OpenAssembly.Source.openStepAtResult_resolves_closed_of_prim_no_callCreate
      (program := program)
      (pc := (Structured.Preservation.CodeSegment.startPc popSegment).toNat)
      (op := Structured.BasicOp.pop.toPrimOp) (state := swappedEVM)
      (result := .running finalEVM) rfl hPopStepResult
  have hFinalPc :
      finalEVM.pc =
        Structured.Preservation.CodeSegment.fallthroughPc segment := by
    have hStepPc :
        finalEVM.pc = swappedEVM.pc + EvmYul.UInt256.ofNat 1 :=
      basicOp_no_callCreate_step_pc (op := Structured.BasicOp.pop) rfl hPopStep
    have hPopFall :
        Structured.Preservation.CodeSegment.fallthroughPc popSegment =
          Structured.Preservation.CodeSegment.startPc popSegment +
            EvmYul.UInt256.ofNat 1 := by
      simpa [Structured.BasicInstr.toAssembly, Structured.BasicOp.toPrimOp,
        Assembly.Instr.byteSize] using
        codeSegment_fallthroughPc_singleton popSegment
    have hPopFallSegment :
        Structured.Preservation.CodeSegment.fallthroughPc popSegment =
          Structured.Preservation.CodeSegment.fallthroughPc segment := by
      simp [popSegment, Structured.Preservation.CodeSegment.right,
        Structured.Preservation.CodeSegment.fallthroughPc]
    rw [hStepPc, hSwapPc, ← hPopFall, hPopFallSegment]
  refine ⟨finalEVM, ?_, hFinalPc, ?_⟩
  · refine ⟨?_, finalStack, ?_, ?_⟩
    · simpa [finalEVM, swappedEVM, Locals.Source.State.withVars,
        EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC] using hShared
    · simp [finalEVM, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC, finalStack]
    · simpa [finalStack, Locals.Source.State.withVars] using
        (Locals.SourceLowering.StackStoreRel.assign
          (layout := layout) (store := source.vars)
          (stack := baseStack) (name := name) (value := value)
          (idx := idx) hNoDup hName hStoreRel)
  · intro tailTrace result hRest
    have hPopAndRest :
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program (tailFuel + 1)
            swappedEVM)
          tailTrace result := by
      simpa using
        OpenAssembly.Source.openRunNResult_current_stepAt_running_continue
          (program := program) (fuel := tailFuel) (state := swappedEVM)
          (mid := finalEVM)
          (pc := (Structured.Preservation.CodeSegment.startPc popSegment).toNat)
          (instr := .prim Structured.BasicOp.pop.toPrimOp)
          hAtPop hOpenPop hRest
    have hSwapAndRest :
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program ((tailFuel + 1) + 1)
            state)
          tailTrace result := by
      simpa using
        OpenAssembly.Source.openRunNResult_current_stepAt_running_continue
          (program := program) (fuel := tailFuel + 1) (state := state)
          (mid := swappedEVM)
          (pc := (Structured.Preservation.CodeSegment.startPc swapSegment).toNat)
          (instr := .prim swapOp.toPrimOp)
          hAtSwap hOpenSwap hPopAndRest
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hSwapAndRest

theorem compilerOpenLocalsExpr_evalOne_assign_openRunNResult_continue_fallthrough_of_compileCode
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {expr : Locals.Expr 1}
    {ctx : Locals.Ctx} {layout : List Name}
    {compiler compilerAfter : Objects.Source.State}
    {state : EvmYul.EVM.State} {valueCode : Structured.Code}
    {name : Name} {idx : Nat} {value : Word}
    {swapOp : Structured.BasicOp}
    (hOwned : Locals.Source.Expr.SourceOwned expr)
    (hSupported : LocalsExprOpenSupported expr)
    (hAccess : Locals.SourceLowering.Expr.Accessible layout 0 expr)
    (hCompile : Locals.Expr.compileCode ctx 0 expr = some valueCode)
    (hCtxLayout : ctx.layout = layout)
    (hNoDup : layout.Nodup)
    (hName : layout[idx]? = some name)
    (hBound : idx + 1 ≤ 16)
    (hSwap : Locals.StackOp.swap? (idx + 1) = some swapOp)
    (program : Assembly.Program)
    (tailFuel : Nat)
    (segment :
      Structured.Preservation.CodeSegment program
        (valueCode ++
          [Structured.BasicInstr.op swapOp,
            Structured.BasicInstr.op Structured.BasicOp.pop]).toAssembly)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler [] state)
    {trace : OpenExternal.OpenTrace}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.evalOne
          prim expr compiler)
        trace (.ok (compilerAfter, value))) :
    ∃ evmAfter : EvmYul.EVM.State,
      Locals.SourceLowering.StackPrefixRel layout
        (compilerAfter.withVars
          (Locals.Source.Store.insert compilerAfter.vars name value))
        [] evmAfter ∧
      evmAfter.pc =
        Structured.Preservation.CodeSegment.fallthroughPc segment ∧
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program tailFuel evmAfter)
          tailTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program
            ((valueCode ++
              [Structured.BasicInstr.op swapOp,
                Structured.BasicInstr.op Structured.BasicOp.pop]).length +
              tailFuel) state)
          (trace ++ tailTrace) result := by
  let assignTail : Structured.Code :=
    [Structured.BasicInstr.op swapOp,
      Structured.BasicInstr.op Structured.BasicOp.pop]
  have hAssemblyCode :
      (valueCode ++ assignTail).toAssembly =
        valueCode.toAssembly ++ assignTail.toAssembly := by
    simp [assignTail, Structured.Code.toAssembly]
  let appendSegment :
      Structured.Preservation.CodeSegment program
        (valueCode.toAssembly ++ assignTail.toAssembly) :=
    Structured.Preservation.CodeSegment.cast_code hAssemblyCode segment
  let valueSegment :
      Structured.Preservation.CodeSegment program valueCode.toAssembly :=
    Structured.Preservation.CodeSegment.left appendSegment
  let tailSegmentRaw :
      Structured.Preservation.CodeSegment program assignTail.toAssembly :=
    Structured.Preservation.CodeSegment.right appendSegment
  have hTailAssembly :
      assignTail.toAssembly =
        [Assembly.Instr.prim swapOp.toPrimOp] ++
          [Assembly.Instr.prim Structured.BasicOp.pop.toPrimOp] := by
    simp [assignTail, Structured.Code.toAssembly,
      Structured.BasicInstr.toAssembly]
  let tailSegment :
      Structured.Preservation.CodeSegment program
        ([Assembly.Instr.prim swapOp.toPrimOp] ++
          [Assembly.Instr.prim Structured.BasicOp.pop.toPrimOp]) :=
    Structured.Preservation.CodeSegment.cast_code hTailAssembly
      tailSegmentRaw
  have hValuePc :
      state.pc =
        Structured.Preservation.CodeSegment.startPc valueSegment := by
    simpa [valueSegment, appendSegment,
      Structured.Preservation.CodeSegment.left,
      Structured.Preservation.CodeSegment.cast_code,
      Structured.Preservation.CodeSegment.startPc] using hPc
  have hValueToTail :
      Structured.Preservation.CodeSegment.fallthroughPc valueSegment =
        Structured.Preservation.CodeSegment.startPc tailSegment := by
    have hRaw :
        Structured.Preservation.CodeSegment.startPc tailSegmentRaw =
          Structured.Preservation.CodeSegment.fallthroughPc valueSegment :=
      codeSegment_right_startPc_eq_left_fallthroughPc appendSegment
    simpa [tailSegment, tailSegmentRaw,
      Structured.Preservation.CodeSegment.cast_code,
      Structured.Preservation.CodeSegment.startPc] using hRaw.symm
  have hTailFallSegment :
      Structured.Preservation.CodeSegment.fallthroughPc tailSegment =
        Structured.Preservation.CodeSegment.fallthroughPc segment := by
    simp [tailSegment, tailSegmentRaw, appendSegment,
      Structured.Preservation.CodeSegment.right,
      Structured.Preservation.CodeSegment.cast_code,
      Structured.Preservation.CodeSegment.fallthroughPc,
      hAssemblyCode, hTailAssembly, assignTail]
  have hResolveEval :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.eval
          prim expr compiler)
        trace (.ok (compilerAfter, [value])) :=
    compilerOpenLocalsExpr_evalOne_resolves_ok_inv hResolve
  rcases
      compilerOpenLocalsExpr_stackPrefix_openRunNResult_continue_fallthrough_of_compileCode
        hPrim hOwned hSupported hAccess hCompile hCtxLayout hNoDup
        [] rfl program (2 + tailFuel) valueSegment hValuePc
        hPrefixRel hResolveEval with
    ⟨evmAfterValue, hValueRel, hValuePcAfter, hValueCont⟩
  have hTailPc :
      evmAfterValue.pc =
        Structured.Preservation.CodeSegment.startPc tailSegment := by
    rw [hValuePcAfter]
    exact hValueToTail
  rcases
      compilerOpenAssignTail_stackPrefix_openRunNResult_continue_fallthrough
        (layout := layout) (source := compilerAfter)
        (state := evmAfterValue) (name := name) (idx := idx)
        (value := value) (swapOp := swapOp)
        hNoDup hName hBound hSwap (by simpa using hValueRel)
        program tailFuel tailSegment hTailPc with
    ⟨evmAfterAssign, hAssignRel, hAssignPc, hAssignCont⟩
  refine ⟨evmAfterAssign, hAssignRel, ?_, ?_⟩
  · simpa [hTailFallSegment] using hAssignPc
  · intro tailTrace result hRest
    have hTailAndRest :
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program (2 + tailFuel)
            evmAfterValue)
          tailTrace result :=
      hAssignCont hRest
    have hFull := hValueCont hTailAndRest
    have hFuel :
        valueCode.length + (2 + tailFuel) =
          (valueCode ++
            [Structured.BasicInstr.op swapOp,
              Structured.BasicInstr.op Structured.BasicOp.pop]).length +
            tailFuel := by
      simp [Nat.add_assoc]
    simpa [hFuel] using hFull

theorem compilerOpenFunctionsStmt_expr_openRunNResult_continue_fallthrough_of_compileCode
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {programSource : Functions.Program}
    {sourceCtx ctxAfter : Functions.Source.Ctx}
    {sourceFuel : Nat}
    {expr : Functions.Expr 0}
    {localsCtx : Locals.Ctx} {layout : List Name}
    {compiler compilerAfter : Objects.Source.State}
    {state : EvmYul.EVM.State} {code : Structured.Code}
    (hOwned : Locals.Source.Expr.SourceOwned expr)
    (hSupported : LocalsExprOpenSupported expr)
    (hAccess : Locals.SourceLowering.Expr.Accessible layout 0 expr)
    (hCompile : Locals.Expr.compileCode localsCtx 0 expr = some code)
    (hCtxLayout : localsCtx.layout = layout)
    (hNoDup : layout.Nodup)
    (program : Assembly.Program)
    (tailFuel : Nat)
    (segment :
      Structured.Preservation.CodeSegment program code.toAssembly)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler [] state)
    {trace : OpenExternal.OpenTrace}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Stmt.run
          prim programSource sourceCtx sourceFuel (.expr expr) compiler)
        trace (.ok (Functions.Source.Outcome.regular compilerAfter,
          ctxAfter))) :
    ctxAfter = sourceCtx ∧
      ∃ evmAfter : EvmYul.EVM.State,
        Locals.SourceLowering.StackPrefixRel layout compilerAfter []
          evmAfter ∧
        evmAfter.pc =
          Structured.Preservation.CodeSegment.fallthroughPc segment ∧
        ∀ {tailTrace : OpenExternal.OpenTrace}
          {result : Except EVMException Assembly.StepResult},
          OpenExternal.OpenResultResolves
            (OpenAssembly.Source.openRunNResult program tailFuel evmAfter)
            tailTrace result →
          OpenExternal.OpenResultResolves
            (OpenAssembly.Source.openRunNResult program
              (code.length + tailFuel) state)
            (trace ++ tailTrace) result := by
  rw [Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Stmt.run] at hResolve
  rcases OpenExternal.OpenResultResolves.bind_inv hResolve with
    hEvalError | hEvalOk
  · rcases hEvalError with ⟨err, _hEval, hResult⟩
    cases hResult
  · rcases hEvalOk with
      ⟨evalTrace, doneTrace, evalResult, hTrace, hEval, hDone⟩
    rcases evalResult with ⟨compilerAfterEval, valuesAfter⟩
    cases hDone
    subst trace
    constructor
    · rfl
    · rcases
        compilerOpenLocalsExpr_zero_stackPrefix_openRunNResult_continue_fallthrough_of_compileCode
          hPrim hOwned hSupported hAccess hCompile hCtxLayout hNoDup
          program tailFuel segment hPc hPrefixRel hEval with
        ⟨evmAfter, hRel, hAfterPc, hCont⟩
      refine ⟨evmAfter, hRel, hAfterPc, ?_⟩
      intro tailTrace result hRest
      have hFull := hCont hRest
      simpa [List.append_assoc] using hFull

theorem compilerOpenFunctionsStmt_let_openRunNResult_continue_fallthrough_of_compileCode
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {programSource : Functions.Program}
    {sourceCtx ctxAfter : Functions.Source.Ctx}
    {sourceFuel : Nat}
    {name : Name} {valueExpr : Functions.Expr 1}
    {localsCtx : Locals.Ctx} {layout : List Name}
    {compiler compilerAfter : Objects.Source.State}
    {state : EvmYul.EVM.State} {code : Structured.Code}
    (hOwned : Locals.Source.Expr.SourceOwned valueExpr)
    (hSupported : LocalsExprOpenSupported valueExpr)
    (hAccess : Locals.SourceLowering.Expr.Accessible layout 0 valueExpr)
    (hCompile : Locals.Expr.compileCode localsCtx 0 valueExpr = some code)
    (hCtxLayout : localsCtx.layout = layout)
    (hNoDup : layout.Nodup)
    (hFresh : name ∉ layout)
    (program : Assembly.Program)
    (tailFuel : Nat)
    (segment :
      Structured.Preservation.CodeSegment program code.toAssembly)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler [] state)
    {trace : OpenExternal.OpenTrace}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Stmt.run
          prim programSource sourceCtx sourceFuel (.let_ name valueExpr)
          compiler)
        trace (.ok (Functions.Source.Outcome.regular compilerAfter,
          ctxAfter))) :
    ctxAfter = { sourceCtx with scope := name :: sourceCtx.scope } ∧
      ∃ evmAfter : EvmYul.EVM.State,
        Locals.SourceLowering.StackPrefixRel (name :: layout)
          compilerAfter [] evmAfter ∧
        evmAfter.pc =
          Structured.Preservation.CodeSegment.fallthroughPc segment ∧
        ∀ {tailTrace : OpenExternal.OpenTrace}
          {result : Except EVMException Assembly.StepResult},
          OpenExternal.OpenResultResolves
            (OpenAssembly.Source.openRunNResult program tailFuel evmAfter)
            tailTrace result →
          OpenExternal.OpenResultResolves
            (OpenAssembly.Source.openRunNResult program
              (code.length + tailFuel) state)
            (trace ++ tailTrace) result := by
  rw [Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Stmt.run] at hResolve
  rcases OpenExternal.OpenResultResolves.bind_inv hResolve with
    hEvalError | hEvalOk
  · rcases hEvalError with ⟨err, _hEval, hResult⟩
    cases hResult
  · rcases hEvalOk with
      ⟨evalTrace, doneTrace, evalResult, hTrace, hEval, hDone⟩
    rcases evalResult with ⟨compilerAfterValue, value⟩
    cases hDone
    subst trace
    constructor
    · rfl
    · rcases
        compilerOpenLocalsExpr_evalOne_insert_openRunNResult_continue_fallthrough_of_compileCode
          hPrim hOwned hSupported hAccess hCompile hCtxLayout hNoDup hFresh
          program tailFuel segment hPc hPrefixRel hEval with
        ⟨evmAfter, hRel, hAfterPc, hCont⟩
      refine ⟨evmAfter, hRel, hAfterPc, ?_⟩
      intro tailTrace result hRest
      have hFull := hCont hRest
      simpa [List.append_assoc] using hFull

theorem compilerOpenFunctionsStmt_assign_openRunNResult_continue_fallthrough_of_compileCode
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {programSource : Functions.Program}
    {sourceCtx ctxAfter : Functions.Source.Ctx}
    {sourceFuel : Nat}
    {name : Name} {valueExpr : Functions.Expr 1}
    {localsCtx : Locals.Ctx} {layout : List Name}
    {compiler compilerAfter : Objects.Source.State}
    {state : EvmYul.EVM.State} {valueCode : Structured.Code}
    {idx : Nat} {swapOp : Structured.BasicOp}
    (hOwned : Locals.Source.Expr.SourceOwned valueExpr)
    (hSupported : LocalsExprOpenSupported valueExpr)
    (hAccess : Locals.SourceLowering.Expr.Accessible layout 0 valueExpr)
    (hCompile : Locals.Expr.compileCode localsCtx 0 valueExpr =
      some valueCode)
    (hCtxLayout : localsCtx.layout = layout)
    (hNoDup : layout.Nodup)
    (hName : layout[idx]? = some name)
    (hBound : idx + 1 ≤ 16)
    (hSwap : Locals.StackOp.swap? (idx + 1) = some swapOp)
    (program : Assembly.Program)
    (tailFuel : Nat)
    (segment :
      Structured.Preservation.CodeSegment program
        (valueCode ++
          [Structured.BasicInstr.op swapOp,
            Structured.BasicInstr.op Structured.BasicOp.pop]).toAssembly)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler [] state)
    {trace : OpenExternal.OpenTrace}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Stmt.run
          prim programSource sourceCtx sourceFuel (.assign name valueExpr)
          compiler)
        trace (.ok (Functions.Source.Outcome.regular compilerAfter,
          ctxAfter))) :
    ctxAfter = sourceCtx ∧
      ∃ evmAfter : EvmYul.EVM.State,
        Locals.SourceLowering.StackPrefixRel layout compilerAfter []
          evmAfter ∧
        evmAfter.pc =
          Structured.Preservation.CodeSegment.fallthroughPc segment ∧
        ∀ {tailTrace : OpenExternal.OpenTrace}
          {result : Except EVMException Assembly.StepResult},
          OpenExternal.OpenResultResolves
            (OpenAssembly.Source.openRunNResult program tailFuel evmAfter)
            tailTrace result →
          OpenExternal.OpenResultResolves
            (OpenAssembly.Source.openRunNResult program
              ((valueCode ++
                [Structured.BasicInstr.op swapOp,
                  Structured.BasicInstr.op Structured.BasicOp.pop]).length +
                tailFuel) state)
            (trace ++ tailTrace) result := by
  have hContains : compiler.vars.contains name = true := by
    rcases hPrefixRel with ⟨_hShared, baseStack, _hStack, hStoreRel⟩
    exact Locals.SourceLowering.StackStoreRel.contains_of_layout
      hStoreRel hName
  rw [Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Stmt.run] at hResolve
  simp [hContains] at hResolve
  rcases OpenExternal.OpenResultResolves.bind_inv hResolve with
    hEvalError | hEvalOk
  · rcases hEvalError with ⟨err, _hEval, hResult⟩
    cases hResult
  · rcases hEvalOk with
      ⟨evalTrace, doneTrace, evalResult, hTrace, hEval, hDone⟩
    rcases evalResult with ⟨compilerAfterValue, value⟩
    cases hDone
    subst trace
    constructor
    · rfl
    · rcases
        compilerOpenLocalsExpr_evalOne_assign_openRunNResult_continue_fallthrough_of_compileCode
          hPrim hOwned hSupported hAccess hCompile hCtxLayout hNoDup
          hName hBound hSwap program tailFuel segment hPc hPrefixRel
          hEval with
        ⟨evmAfter, hRel, hAfterPc, hCont⟩
      refine ⟨evmAfter, hRel, hAfterPc, ?_⟩
      intro tailTrace result hRest
      have hFull := hCont hRest
      simpa [List.append_assoc] using hFull

theorem compilerOpenFunctionsStmt_expr_resolves_ok_regular_inv
    {prim : Objects.Source.PrimitiveSemantics}
    {programSource : Functions.Program}
    {sourceCtx ctxAfter : Functions.Source.Ctx}
    {sourceFuel : Nat}
    {expr : Functions.Expr 0}
    {compiler : Objects.Source.State}
    {trace : OpenExternal.OpenTrace}
    {outcome : Functions.Source.Outcome}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Stmt.run
          prim programSource sourceCtx sourceFuel (.expr expr) compiler)
        trace (.ok (outcome, ctxAfter))) :
    ∃ compilerAfter : Objects.Source.State,
      outcome = Functions.Source.Outcome.regular compilerAfter ∧
        ctxAfter = sourceCtx := by
  rw [Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Stmt.run] at hResolve
  rcases OpenExternal.OpenResultResolves.bind_inv hResolve with
    hEvalError | hEvalOk
  · rcases hEvalError with ⟨err, _hEval, hResult⟩
    cases hResult
  · rcases hEvalOk with
      ⟨evalTrace, doneTrace, evalResult, hTrace, hEval, hDone⟩
    rcases evalResult with ⟨compilerAfter, valuesAfter⟩
    cases hDone
    exact ⟨compilerAfter, rfl, rfl⟩

theorem compilerOpenFunctionsStmt_let_resolves_ok_regular_inv
    {prim : Objects.Source.PrimitiveSemantics}
    {programSource : Functions.Program}
    {sourceCtx ctxAfter : Functions.Source.Ctx}
    {sourceFuel : Nat}
    {name : Name} {valueExpr : Functions.Expr 1}
    {compiler : Objects.Source.State}
    {trace : OpenExternal.OpenTrace}
    {outcome : Functions.Source.Outcome}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Stmt.run
          prim programSource sourceCtx sourceFuel (.let_ name valueExpr)
          compiler)
        trace (.ok (outcome, ctxAfter))) :
    ∃ compilerAfter : Objects.Source.State,
      outcome = Functions.Source.Outcome.regular compilerAfter ∧
        ctxAfter = { sourceCtx with scope := name :: sourceCtx.scope } := by
  rw [Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Stmt.run] at hResolve
  rcases OpenExternal.OpenResultResolves.bind_inv hResolve with
    hEvalError | hEvalOk
  · rcases hEvalError with ⟨err, _hEval, hResult⟩
    cases hResult
  · rcases hEvalOk with
      ⟨evalTrace, doneTrace, evalResult, hTrace, hEval, hDone⟩
    rcases evalResult with ⟨compilerAfterValue, value⟩
    cases hDone
    exact ⟨compilerAfterValue.insert name value, rfl, rfl⟩

theorem compilerOpenFunctionsStmt_assign_resolves_ok_regular_inv
    {prim : Objects.Source.PrimitiveSemantics}
    {programSource : Functions.Program}
    {sourceCtx ctxAfter : Functions.Source.Ctx}
    {sourceFuel : Nat}
    {name : Name} {valueExpr : Functions.Expr 1}
    {compiler : Objects.Source.State}
    {trace : OpenExternal.OpenTrace}
    {outcome : Functions.Source.Outcome}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Stmt.run
          prim programSource sourceCtx sourceFuel (.assign name valueExpr)
          compiler)
        trace (.ok (outcome, ctxAfter))) :
    ∃ compilerAfter : Objects.Source.State,
      outcome = Functions.Source.Outcome.regular compilerAfter ∧
        ctxAfter = sourceCtx := by
  rw [Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Stmt.run] at hResolve
  cases hContains : compiler.vars.contains name with
  | false =>
      simp [hContains, Reference.SourceBridgeFacts.CompilerOpen.invalid] at hResolve
      cases hResolve
  | true =>
      simp [hContains] at hResolve
      rcases OpenExternal.OpenResultResolves.bind_inv hResolve with
        hEvalError | hEvalOk
      · rcases hEvalError with ⟨err, _hEval, hResult⟩
        cases hResult
      · rcases hEvalOk with
          ⟨evalTrace, doneTrace, evalResult, hTrace, hEval, hDone⟩
        rcases evalResult with ⟨compilerAfterValue, value⟩
        cases hDone
        exact
          ⟨compilerAfterValue.withVars
              (Locals.Source.Store.insert compilerAfterValue.vars name
                value),
            rfl, rfl⟩

theorem compilerOpenFunctionsBlock_expr_cons_openRunNResult_of_tail
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {programSource : Functions.Program}
    {sourceCtx ctxFinal : Functions.Source.Ctx}
    {sourceFuel : Nat}
    {expr : Functions.Expr 0} {rest : List Functions.Stmt}
    {localsCtx : Locals.Ctx} {layout : List Name}
    {compiler : Objects.Source.State}
    {state : EvmYul.EVM.State} {code : Structured.Code}
    (hOwned : Locals.Source.Expr.SourceOwned expr)
    (hSupported : LocalsExprOpenSupported expr)
    (hAccess : Locals.SourceLowering.Expr.Accessible layout 0 expr)
    (hCompile : Locals.Expr.compileCode localsCtx 0 expr = some code)
    (hCtxLayout : localsCtx.layout = layout)
    (hNoDup : layout.Nodup)
    (program : Assembly.Program)
    (tailFuel : Nat)
    (segment :
      Structured.Preservation.CodeSegment program code.toAssembly)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler [] state)
    {ResultRel : Functions.Source.Outcome → Assembly.StepResult → Prop}
    (hTail :
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {sourceOutcome : Functions.Source.Outcome}
        {tailCtxAfter : Functions.Source.Ctx}
        {compilerAfter : Objects.Source.State}
        {evmAfter : EvmYul.EVM.State},
        Locals.SourceLowering.StackPrefixRel layout compilerAfter []
          evmAfter →
        OpenExternal.OpenResultResolves
          (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
            prim programSource sourceCtx sourceFuel { stmts := rest }
            compilerAfter)
          tailTrace (.ok (sourceOutcome, tailCtxAfter)) →
        ∃ targetResult,
          OpenExternal.OpenResultResolves
            (OpenAssembly.Source.openRunNResult program tailFuel evmAfter)
            tailTrace (.ok targetResult) ∧
          ResultRel sourceOutcome targetResult)
    {trace : OpenExternal.OpenTrace}
    {sourceOutcome : Functions.Source.Outcome}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
          prim programSource sourceCtx (sourceFuel + 1)
          { stmts := .expr expr :: rest } compiler)
        trace (.ok (sourceOutcome, ctxFinal))) :
    ∃ targetFuel targetResult,
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openRunNResult program targetFuel state)
        trace (.ok targetResult) ∧
      ResultRel sourceOutcome targetResult := by
  rw [Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen] at hResolve
  rcases OpenExternal.OpenResultResolves.bind_inv hResolve with
    hHeadError | hHeadOk
  · rcases hHeadError with ⟨err, _hHead, hResult⟩
    cases hResult
  · rcases hHeadOk with
      ⟨headTrace, tailTrace, stmtResult, hTrace, hHead, hRest⟩
    rcases stmtResult with ⟨headOutcome, ctxAfterHead⟩
    rcases
      compilerOpenFunctionsStmt_expr_resolves_ok_regular_inv hHead with
      ⟨compilerAfter, hOutcome, hCtxAfterHead⟩
    subst headOutcome
    subst ctxAfterHead
    subst trace
    simp [Functions.Source.Outcome.regular,
      Locals.Source.Outcome.regular] at hRest
    rcases
        compilerOpenFunctionsStmt_expr_openRunNResult_continue_fallthrough_of_compileCode
          hPrim hOwned hSupported hAccess hCompile hCtxLayout hNoDup
          program tailFuel segment hPc hPrefixRel hHead with
      ⟨_hCtx, evmAfter, hRel, _hAfterPc, hHeadCont⟩
    rcases hTail hRel hRest with
      ⟨targetResult, hTailRun, hOutcomeRel⟩
    refine ⟨code.length + tailFuel, targetResult, ?_, hOutcomeRel⟩
    exact hHeadCont hTailRun

theorem compilerOpenFunctionsBlock_let_cons_openRunNResult_of_tail
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {programSource : Functions.Program}
    {sourceCtx ctxFinal : Functions.Source.Ctx}
    {sourceFuel : Nat}
    {name : Name} {valueExpr : Functions.Expr 1}
    {rest : List Functions.Stmt}
    {localsCtx : Locals.Ctx} {layout : List Name}
    {compiler : Objects.Source.State}
    {state : EvmYul.EVM.State} {code : Structured.Code}
    (hOwned : Locals.Source.Expr.SourceOwned valueExpr)
    (hSupported : LocalsExprOpenSupported valueExpr)
    (hAccess : Locals.SourceLowering.Expr.Accessible layout 0 valueExpr)
    (hCompile : Locals.Expr.compileCode localsCtx 0 valueExpr = some code)
    (hCtxLayout : localsCtx.layout = layout)
    (hNoDup : layout.Nodup)
    (hFresh : name ∉ layout)
    (program : Assembly.Program)
    (tailFuel : Nat)
    (segment :
      Structured.Preservation.CodeSegment program code.toAssembly)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler [] state)
    {ResultRel : Functions.Source.Outcome → Assembly.StepResult → Prop}
    (hTail :
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {sourceOutcome : Functions.Source.Outcome}
        {tailCtxAfter : Functions.Source.Ctx}
        {compilerAfter : Objects.Source.State}
        {evmAfter : EvmYul.EVM.State},
        Locals.SourceLowering.StackPrefixRel (name :: layout)
          compilerAfter [] evmAfter →
        OpenExternal.OpenResultResolves
          (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
            prim programSource
            { sourceCtx with scope := name :: sourceCtx.scope }
            sourceFuel { stmts := rest } compilerAfter)
          tailTrace (.ok (sourceOutcome, tailCtxAfter)) →
        ∃ targetResult,
          OpenExternal.OpenResultResolves
            (OpenAssembly.Source.openRunNResult program tailFuel evmAfter)
            tailTrace (.ok targetResult) ∧
          ResultRel sourceOutcome targetResult)
    {trace : OpenExternal.OpenTrace}
    {sourceOutcome : Functions.Source.Outcome}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
          prim programSource sourceCtx (sourceFuel + 1)
          { stmts := .let_ name valueExpr :: rest } compiler)
        trace (.ok (sourceOutcome, ctxFinal))) :
    ∃ targetFuel targetResult,
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openRunNResult program targetFuel state)
        trace (.ok targetResult) ∧
      ResultRel sourceOutcome targetResult := by
  rw [Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen] at hResolve
  rcases OpenExternal.OpenResultResolves.bind_inv hResolve with
    hHeadError | hHeadOk
  · rcases hHeadError with ⟨err, _hHead, hResult⟩
    cases hResult
  · rcases hHeadOk with
      ⟨headTrace, tailTrace, stmtResult, hTrace, hHead, hRest⟩
    rcases stmtResult with ⟨headOutcome, ctxAfterHead⟩
    rcases
      compilerOpenFunctionsStmt_let_resolves_ok_regular_inv hHead with
      ⟨compilerAfter, hOutcome, hCtxAfterHead⟩
    subst headOutcome
    subst ctxAfterHead
    subst trace
    simp [Functions.Source.Outcome.regular,
      Locals.Source.Outcome.regular] at hRest
    rcases
        compilerOpenFunctionsStmt_let_openRunNResult_continue_fallthrough_of_compileCode
          hPrim hOwned hSupported hAccess hCompile hCtxLayout hNoDup
          hFresh program tailFuel segment hPc hPrefixRel hHead with
      ⟨_hCtx, evmAfter, hRel, _hAfterPc, hHeadCont⟩
    rcases hTail hRel hRest with
      ⟨targetResult, hTailRun, hOutcomeRel⟩
    refine ⟨code.length + tailFuel, targetResult, ?_, hOutcomeRel⟩
    exact hHeadCont hTailRun

theorem compilerOpenFunctionsBlock_assign_cons_openRunNResult_of_tail
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {programSource : Functions.Program}
    {sourceCtx ctxFinal : Functions.Source.Ctx}
    {sourceFuel : Nat}
    {name : Name} {valueExpr : Functions.Expr 1}
    {rest : List Functions.Stmt}
    {localsCtx : Locals.Ctx} {layout : List Name}
    {compiler : Objects.Source.State}
    {state : EvmYul.EVM.State} {valueCode : Structured.Code}
    {idx : Nat} {swapOp : Structured.BasicOp}
    (hOwned : Locals.Source.Expr.SourceOwned valueExpr)
    (hSupported : LocalsExprOpenSupported valueExpr)
    (hAccess : Locals.SourceLowering.Expr.Accessible layout 0 valueExpr)
    (hCompile : Locals.Expr.compileCode localsCtx 0 valueExpr =
      some valueCode)
    (hCtxLayout : localsCtx.layout = layout)
    (hNoDup : layout.Nodup)
    (hName : layout[idx]? = some name)
    (hBound : idx + 1 ≤ 16)
    (hSwap : Locals.StackOp.swap? (idx + 1) = some swapOp)
    (program : Assembly.Program)
    (tailFuel : Nat)
    (segment :
      Structured.Preservation.CodeSegment program
        (valueCode ++
          [Structured.BasicInstr.op swapOp,
            Structured.BasicInstr.op Structured.BasicOp.pop]).toAssembly)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler [] state)
    {ResultRel : Functions.Source.Outcome → Assembly.StepResult → Prop}
    (hTail :
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {sourceOutcome : Functions.Source.Outcome}
        {tailCtxAfter : Functions.Source.Ctx}
        {compilerAfter : Objects.Source.State}
        {evmAfter : EvmYul.EVM.State},
        Locals.SourceLowering.StackPrefixRel layout compilerAfter []
          evmAfter →
        OpenExternal.OpenResultResolves
          (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
            prim programSource sourceCtx sourceFuel { stmts := rest }
            compilerAfter)
          tailTrace (.ok (sourceOutcome, tailCtxAfter)) →
        ∃ targetResult,
          OpenExternal.OpenResultResolves
            (OpenAssembly.Source.openRunNResult program tailFuel evmAfter)
            tailTrace (.ok targetResult) ∧
          ResultRel sourceOutcome targetResult)
    {trace : OpenExternal.OpenTrace}
    {sourceOutcome : Functions.Source.Outcome}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
          prim programSource sourceCtx (sourceFuel + 1)
          { stmts := .assign name valueExpr :: rest } compiler)
        trace (.ok (sourceOutcome, ctxFinal))) :
    ∃ targetFuel targetResult,
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openRunNResult program targetFuel state)
        trace (.ok targetResult) ∧
      ResultRel sourceOutcome targetResult := by
  rw [Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen] at hResolve
  rcases OpenExternal.OpenResultResolves.bind_inv hResolve with
    hHeadError | hHeadOk
  · rcases hHeadError with ⟨err, _hHead, hResult⟩
    cases hResult
  · rcases hHeadOk with
      ⟨headTrace, tailTrace, stmtResult, hTrace, hHead, hRest⟩
    rcases stmtResult with ⟨headOutcome, ctxAfterHead⟩
    rcases
      compilerOpenFunctionsStmt_assign_resolves_ok_regular_inv hHead with
      ⟨compilerAfter, hOutcome, hCtxAfterHead⟩
    subst headOutcome
    subst ctxAfterHead
    subst trace
    simp [Functions.Source.Outcome.regular,
      Locals.Source.Outcome.regular] at hRest
    rcases
        compilerOpenFunctionsStmt_assign_openRunNResult_continue_fallthrough_of_compileCode
          hPrim hOwned hSupported hAccess hCompile hCtxLayout hNoDup
          hName hBound hSwap program tailFuel segment hPc hPrefixRel
          hHead with
      ⟨_hCtx, evmAfter, hRel, _hAfterPc, hHeadCont⟩
    rcases hTail hRel hRest with
      ⟨targetResult, hTailRun, hOutcomeRel⟩
    refine
      ⟨(valueCode ++
          [Structured.BasicInstr.op swapOp,
            Structured.BasicInstr.op Structured.BasicOp.pop]).length +
          tailFuel,
        targetResult, ?_, hOutcomeRel⟩
    exact hHeadCont hTailRun

theorem compilerOpenFunctionsBlock_expr_cons_openRunNResult_of_tail_pc
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {programSource : Functions.Program}
    {sourceCtx ctxFinal : Functions.Source.Ctx}
    {sourceFuel : Nat}
    {expr : Functions.Expr 0} {rest : List Functions.Stmt}
    {localsCtx : Locals.Ctx} {layout : List Name}
    {compiler : Objects.Source.State}
    {state : EvmYul.EVM.State} {code : Structured.Code}
    (hOwned : Locals.Source.Expr.SourceOwned expr)
    (hSupported : LocalsExprOpenSupported expr)
    (hAccess : Locals.SourceLowering.Expr.Accessible layout 0 expr)
    (hCompile : Locals.Expr.compileCode localsCtx 0 expr = some code)
    (hCtxLayout : localsCtx.layout = layout)
    (hNoDup : layout.Nodup)
    (program : Assembly.Program)
    (tailFuel : Nat)
    (segment :
      Structured.Preservation.CodeSegment program code.toAssembly)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler [] state)
    {ResultRel : Functions.Source.Outcome → Assembly.StepResult → Prop}
    (hTail :
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {sourceOutcome : Functions.Source.Outcome}
        {tailCtxAfter : Functions.Source.Ctx}
        {compilerAfter : Objects.Source.State}
        {evmAfter : EvmYul.EVM.State},
        Locals.SourceLowering.StackPrefixRel layout compilerAfter []
          evmAfter →
        evmAfter.pc =
          Structured.Preservation.CodeSegment.fallthroughPc segment →
        OpenExternal.OpenResultResolves
          (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
            prim programSource sourceCtx sourceFuel { stmts := rest }
            compilerAfter)
          tailTrace (.ok (sourceOutcome, tailCtxAfter)) →
        ∃ targetResult,
          OpenExternal.OpenResultResolves
            (OpenAssembly.Source.openRunNResult program tailFuel evmAfter)
            tailTrace (.ok targetResult) ∧
          ResultRel sourceOutcome targetResult)
    {trace : OpenExternal.OpenTrace}
    {sourceOutcome : Functions.Source.Outcome}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
          prim programSource sourceCtx (sourceFuel + 1)
          { stmts := .expr expr :: rest } compiler)
        trace (.ok (sourceOutcome, ctxFinal))) :
    ∃ targetFuel targetResult,
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openRunNResult program targetFuel state)
        trace (.ok targetResult) ∧
      ResultRel sourceOutcome targetResult := by
  rw [Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen] at hResolve
  rcases OpenExternal.OpenResultResolves.bind_inv hResolve with
    hHeadError | hHeadOk
  · rcases hHeadError with ⟨err, _hHead, hResult⟩
    cases hResult
  · rcases hHeadOk with
      ⟨headTrace, tailTrace, stmtResult, hTrace, hHead, hRest⟩
    rcases stmtResult with ⟨headOutcome, ctxAfterHead⟩
    rcases
      compilerOpenFunctionsStmt_expr_resolves_ok_regular_inv hHead with
      ⟨compilerAfter, hOutcome, hCtxAfterHead⟩
    subst headOutcome
    subst ctxAfterHead
    subst trace
    simp [Functions.Source.Outcome.regular,
      Locals.Source.Outcome.regular] at hRest
    rcases
        compilerOpenFunctionsStmt_expr_openRunNResult_continue_fallthrough_of_compileCode
          hPrim hOwned hSupported hAccess hCompile hCtxLayout hNoDup
          program tailFuel segment hPc hPrefixRel hHead with
      ⟨_hCtx, evmAfter, hRel, hAfterPc, hHeadCont⟩
    rcases hTail hRel hAfterPc hRest with
      ⟨targetResult, hTailRun, hOutcomeRel⟩
    refine ⟨code.length + tailFuel, targetResult, ?_, hOutcomeRel⟩
    exact hHeadCont hTailRun

theorem compilerOpenFunctionsBlock_let_cons_openRunNResult_of_tail_pc
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {programSource : Functions.Program}
    {sourceCtx ctxFinal : Functions.Source.Ctx}
    {sourceFuel : Nat}
    {name : Name} {valueExpr : Functions.Expr 1}
    {rest : List Functions.Stmt}
    {localsCtx : Locals.Ctx} {layout : List Name}
    {compiler : Objects.Source.State}
    {state : EvmYul.EVM.State} {code : Structured.Code}
    (hOwned : Locals.Source.Expr.SourceOwned valueExpr)
    (hSupported : LocalsExprOpenSupported valueExpr)
    (hAccess : Locals.SourceLowering.Expr.Accessible layout 0 valueExpr)
    (hCompile : Locals.Expr.compileCode localsCtx 0 valueExpr = some code)
    (hCtxLayout : localsCtx.layout = layout)
    (hNoDup : layout.Nodup)
    (hFresh : name ∉ layout)
    (program : Assembly.Program)
    (tailFuel : Nat)
    (segment :
      Structured.Preservation.CodeSegment program code.toAssembly)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler [] state)
    {ResultRel : Functions.Source.Outcome → Assembly.StepResult → Prop}
    (hTail :
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {sourceOutcome : Functions.Source.Outcome}
        {tailCtxAfter : Functions.Source.Ctx}
        {compilerAfter : Objects.Source.State}
        {evmAfter : EvmYul.EVM.State},
        Locals.SourceLowering.StackPrefixRel (name :: layout)
          compilerAfter [] evmAfter →
        evmAfter.pc =
          Structured.Preservation.CodeSegment.fallthroughPc segment →
        OpenExternal.OpenResultResolves
          (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
            prim programSource
            { sourceCtx with scope := name :: sourceCtx.scope }
            sourceFuel { stmts := rest } compilerAfter)
          tailTrace (.ok (sourceOutcome, tailCtxAfter)) →
        ∃ targetResult,
          OpenExternal.OpenResultResolves
            (OpenAssembly.Source.openRunNResult program tailFuel evmAfter)
            tailTrace (.ok targetResult) ∧
          ResultRel sourceOutcome targetResult)
    {trace : OpenExternal.OpenTrace}
    {sourceOutcome : Functions.Source.Outcome}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
          prim programSource sourceCtx (sourceFuel + 1)
          { stmts := .let_ name valueExpr :: rest } compiler)
        trace (.ok (sourceOutcome, ctxFinal))) :
    ∃ targetFuel targetResult,
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openRunNResult program targetFuel state)
        trace (.ok targetResult) ∧
      ResultRel sourceOutcome targetResult := by
  rw [Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen] at hResolve
  rcases OpenExternal.OpenResultResolves.bind_inv hResolve with
    hHeadError | hHeadOk
  · rcases hHeadError with ⟨err, _hHead, hResult⟩
    cases hResult
  · rcases hHeadOk with
      ⟨headTrace, tailTrace, stmtResult, hTrace, hHead, hRest⟩
    rcases stmtResult with ⟨headOutcome, ctxAfterHead⟩
    rcases
      compilerOpenFunctionsStmt_let_resolves_ok_regular_inv hHead with
      ⟨compilerAfter, hOutcome, hCtxAfterHead⟩
    subst headOutcome
    subst ctxAfterHead
    subst trace
    simp [Functions.Source.Outcome.regular,
      Locals.Source.Outcome.regular] at hRest
    rcases
        compilerOpenFunctionsStmt_let_openRunNResult_continue_fallthrough_of_compileCode
          hPrim hOwned hSupported hAccess hCompile hCtxLayout hNoDup
          hFresh program tailFuel segment hPc hPrefixRel hHead with
      ⟨_hCtx, evmAfter, hRel, hAfterPc, hHeadCont⟩
    rcases hTail hRel hAfterPc hRest with
      ⟨targetResult, hTailRun, hOutcomeRel⟩
    refine ⟨code.length + tailFuel, targetResult, ?_, hOutcomeRel⟩
    exact hHeadCont hTailRun

theorem compilerOpenFunctionsBlock_assign_cons_openRunNResult_of_tail_pc
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {programSource : Functions.Program}
    {sourceCtx ctxFinal : Functions.Source.Ctx}
    {sourceFuel : Nat}
    {name : Name} {valueExpr : Functions.Expr 1}
    {rest : List Functions.Stmt}
    {localsCtx : Locals.Ctx} {layout : List Name}
    {compiler : Objects.Source.State}
    {state : EvmYul.EVM.State} {valueCode : Structured.Code}
    {idx : Nat} {swapOp : Structured.BasicOp}
    (hOwned : Locals.Source.Expr.SourceOwned valueExpr)
    (hSupported : LocalsExprOpenSupported valueExpr)
    (hAccess : Locals.SourceLowering.Expr.Accessible layout 0 valueExpr)
    (hCompile : Locals.Expr.compileCode localsCtx 0 valueExpr =
      some valueCode)
    (hCtxLayout : localsCtx.layout = layout)
    (hNoDup : layout.Nodup)
    (hName : layout[idx]? = some name)
    (hBound : idx + 1 ≤ 16)
    (hSwap : Locals.StackOp.swap? (idx + 1) = some swapOp)
    (program : Assembly.Program)
    (tailFuel : Nat)
    (segment :
      Structured.Preservation.CodeSegment program
        (valueCode ++
          [Structured.BasicInstr.op swapOp,
            Structured.BasicInstr.op Structured.BasicOp.pop]).toAssembly)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler [] state)
    {ResultRel : Functions.Source.Outcome → Assembly.StepResult → Prop}
    (hTail :
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {sourceOutcome : Functions.Source.Outcome}
        {tailCtxAfter : Functions.Source.Ctx}
        {compilerAfter : Objects.Source.State}
        {evmAfter : EvmYul.EVM.State},
        Locals.SourceLowering.StackPrefixRel layout compilerAfter []
          evmAfter →
        evmAfter.pc =
          Structured.Preservation.CodeSegment.fallthroughPc segment →
        OpenExternal.OpenResultResolves
          (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
            prim programSource sourceCtx sourceFuel { stmts := rest }
            compilerAfter)
          tailTrace (.ok (sourceOutcome, tailCtxAfter)) →
        ∃ targetResult,
          OpenExternal.OpenResultResolves
            (OpenAssembly.Source.openRunNResult program tailFuel evmAfter)
            tailTrace (.ok targetResult) ∧
          ResultRel sourceOutcome targetResult)
    {trace : OpenExternal.OpenTrace}
    {sourceOutcome : Functions.Source.Outcome}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
          prim programSource sourceCtx (sourceFuel + 1)
          { stmts := .assign name valueExpr :: rest } compiler)
        trace (.ok (sourceOutcome, ctxFinal))) :
    ∃ targetFuel targetResult,
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openRunNResult program targetFuel state)
        trace (.ok targetResult) ∧
      ResultRel sourceOutcome targetResult := by
  rw [Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen] at hResolve
  rcases OpenExternal.OpenResultResolves.bind_inv hResolve with
    hHeadError | hHeadOk
  · rcases hHeadError with ⟨err, _hHead, hResult⟩
    cases hResult
  · rcases hHeadOk with
      ⟨headTrace, tailTrace, stmtResult, hTrace, hHead, hRest⟩
    rcases stmtResult with ⟨headOutcome, ctxAfterHead⟩
    rcases
      compilerOpenFunctionsStmt_assign_resolves_ok_regular_inv hHead with
      ⟨compilerAfter, hOutcome, hCtxAfterHead⟩
    subst headOutcome
    subst ctxAfterHead
    subst trace
    simp [Functions.Source.Outcome.regular,
      Locals.Source.Outcome.regular] at hRest
    rcases
        compilerOpenFunctionsStmt_assign_openRunNResult_continue_fallthrough_of_compileCode
          hPrim hOwned hSupported hAccess hCompile hCtxLayout hNoDup
          hName hBound hSwap program tailFuel segment hPc hPrefixRel
          hHead with
      ⟨_hCtx, evmAfter, hRel, hAfterPc, hHeadCont⟩
    rcases hTail hRel hAfterPc hRest with
      ⟨targetResult, hTailRun, hOutcomeRel⟩
    refine
      ⟨(valueCode ++
          [Structured.BasicInstr.op swapOp,
            Structured.BasicInstr.op Structured.BasicOp.pop]).length +
          tailFuel,
        targetResult, ?_, hOutcomeRel⟩
    exact hHeadCont hTailRun

theorem compilerOpenFunctionsBlock_expr_cons_openRunNResult_of_compileOpen_tail_pc
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {programSource : Functions.Program}
    {sourceCtx ctxFinal : Functions.Source.Ctx}
    {sourceFuel : Nat}
    {returns : List Name}
    {expr : Functions.Expr 0} {rest : List Functions.Stmt}
    {localsCtx finalLocalsCtx : Locals.Ctx} {layout : List Name}
    {compiledStmts : List Expressions.Stmt}
    {compiler : Objects.Source.State}
    {state : EvmYul.EVM.State}
    {structuredCtx : Structured.CompileContext}
    {supply : Structured.LabelSupply}
    (hOwned : Locals.Source.Expr.SourceOwned expr)
    (hSupported : LocalsExprOpenSupported expr)
    (hAccess : Locals.SourceLowering.Expr.Accessible layout 0 expr)
    (hCompileBlock :
      Locals.Block.compileOpen localsCtx
          (Functions.Block.toLocals returns
            { stmts := .expr expr :: rest }) =
        some (compiledStmts, finalLocalsCtx))
    (hCtxLayout : localsCtx.layout = layout)
    (hNoDup : layout.Nodup)
    (program : Assembly.Program)
    (tailFuel : Nat)
    (segment :
      Structured.Preservation.CodeSegment program
        (Structured.Block.compileFromCtx
          { stmts := Expressions.StmtList.toStructured compiledStmts }
          structuredCtx supply).code)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler [] state)
    {ResultRel : Functions.Source.Outcome → Assembly.StepResult → Prop}
    (hTail :
      ∀ {tailStmts : List Expressions.Stmt}
        {tailFinalCtx : Locals.Ctx}
        {tailTrace : OpenExternal.OpenTrace}
        {sourceOutcome : Functions.Source.Outcome}
        {tailCtxAfter : Functions.Source.Ctx}
        {compilerAfter : Objects.Source.State}
        {evmAfter : EvmYul.EVM.State},
        (tailSegment :
          Structured.Preservation.CodeSegment program
            (Structured.Block.compileFromCtx
              { stmts := Expressions.StmtList.toStructured tailStmts }
              structuredCtx supply).code) →
        Locals.Block.compileOpen localsCtx
          (Functions.Block.toLocals returns { stmts := rest }) =
          some (tailStmts, tailFinalCtx) →
        Locals.SourceLowering.StackPrefixRel layout compilerAfter []
          evmAfter →
        evmAfter.pc =
          Structured.Preservation.CodeSegment.startPc tailSegment →
        OpenExternal.OpenResultResolves
          (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
            prim programSource sourceCtx sourceFuel { stmts := rest }
            compilerAfter)
          tailTrace (.ok (sourceOutcome, tailCtxAfter)) →
        ∃ targetResult,
          OpenExternal.OpenResultResolves
            (OpenAssembly.Source.openRunNResult program tailFuel evmAfter)
            tailTrace (.ok targetResult) ∧
          ResultRel sourceOutcome targetResult)
    {trace : OpenExternal.OpenTrace}
    {sourceOutcome : Functions.Source.Outcome}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
          prim programSource sourceCtx (sourceFuel + 1)
          { stmts := .expr expr :: rest } compiler)
        trace (.ok (sourceOutcome, ctxFinal))) :
    ∃ targetFuel targetResult,
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openRunNResult program targetFuel state)
        trace (.ok targetResult) ∧
      ResultRel sourceOutcome targetResult := by
  rcases
      functionsBlock_toLocals_compileOpen_expr_cons_inv hCompileBlock with
    ⟨code, restStmts, hCode, hRestCompile, hCompiledStmts⟩
  have hSegmentCode :
      (Structured.Block.compileFromCtx
          { stmts := Expressions.StmtList.toStructured compiledStmts }
          structuredCtx supply).code =
        (Structured.Block.compileFromCtx
          { stmts :=
              Expressions.StmtList.toStructured
                (Locals.codeStmt code ++ restStmts) }
          structuredCtx supply).code := by
    simp [hCompiledStmts]
  let segment' :
      Structured.Preservation.CodeSegment program
        (Structured.Block.compileFromCtx
          { stmts :=
              Expressions.StmtList.toStructured
                (Locals.codeStmt code ++ restStmts) }
          structuredCtx supply).code :=
    Structured.Preservation.CodeSegment.cast_code hSegmentCode segment
  rcases codeSegment_expressions_codeStmt_cons_split segment' with
    ⟨headSegment, tailSegment, hHeadStart, hTailStart, _hTailFall⟩
  have hSegmentStart :
      Structured.Preservation.CodeSegment.startPc segment' =
        Structured.Preservation.CodeSegment.startPc segment := by
    simp [segment', Structured.Preservation.CodeSegment.cast_code,
      Structured.Preservation.CodeSegment.startPc]
  have hHeadPc :
      state.pc =
        Structured.Preservation.CodeSegment.startPc headSegment := by
    rw [hPc, ← hSegmentStart, ← hHeadStart]
  have hTailForHead :
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {sourceOutcome : Functions.Source.Outcome}
        {tailCtxAfter : Functions.Source.Ctx}
        {compilerAfter : Objects.Source.State}
        {evmAfter : EvmYul.EVM.State},
        Locals.SourceLowering.StackPrefixRel layout compilerAfter []
          evmAfter →
        evmAfter.pc =
          Structured.Preservation.CodeSegment.fallthroughPc headSegment →
        OpenExternal.OpenResultResolves
          (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
            prim programSource sourceCtx sourceFuel { stmts := rest }
            compilerAfter)
          tailTrace (.ok (sourceOutcome, tailCtxAfter)) →
        ∃ targetResult,
          OpenExternal.OpenResultResolves
            (OpenAssembly.Source.openRunNResult program tailFuel evmAfter)
            tailTrace (.ok targetResult) ∧
          ResultRel sourceOutcome targetResult := by
    intro tailTrace sourceOutcome tailCtxAfter compilerAfter evmAfter
      hRel hAfterPc hRest
    have hTailPc :
        evmAfter.pc =
          Structured.Preservation.CodeSegment.startPc tailSegment := by
      rw [hAfterPc]
      exact hTailStart.symm
    exact hTail tailSegment hRestCompile hRel hTailPc hRest
  exact
    compilerOpenFunctionsBlock_expr_cons_openRunNResult_of_tail_pc
      hPrim hOwned hSupported hAccess hCode hCtxLayout hNoDup program
      tailFuel headSegment hHeadPc hPrefixRel hTailForHead hResolve

theorem compilerOpenFunctionsBlock_let_cons_openRunNResult_of_compileOpen_tail_pc
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {programSource : Functions.Program}
    {sourceCtx ctxFinal : Functions.Source.Ctx}
    {sourceFuel : Nat}
    {returns : List Name}
    {name : Name} {valueExpr : Functions.Expr 1}
    {rest : List Functions.Stmt}
    {localsCtx finalLocalsCtx : Locals.Ctx} {layout : List Name}
    {compiledStmts : List Expressions.Stmt}
    {compiler : Objects.Source.State}
    {state : EvmYul.EVM.State}
    {structuredCtx : Structured.CompileContext}
    {supply : Structured.LabelSupply}
    (hOwned : Locals.Source.Expr.SourceOwned valueExpr)
    (hSupported : LocalsExprOpenSupported valueExpr)
    (hAccess : Locals.SourceLowering.Expr.Accessible layout 0 valueExpr)
    (hCompileBlock :
      Locals.Block.compileOpen localsCtx
          (Functions.Block.toLocals returns
            { stmts := .let_ name valueExpr :: rest }) =
        some (compiledStmts, finalLocalsCtx))
    (hCtxLayout : localsCtx.layout = layout)
    (hNoDup : layout.Nodup)
    (hFresh : name ∉ layout)
    (program : Assembly.Program)
    (tailFuel : Nat)
    (segment :
      Structured.Preservation.CodeSegment program
        (Structured.Block.compileFromCtx
          { stmts := Expressions.StmtList.toStructured compiledStmts }
          structuredCtx supply).code)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler [] state)
    {ResultRel : Functions.Source.Outcome → Assembly.StepResult → Prop}
    (hTail :
      ∀ {tailStmts : List Expressions.Stmt}
        {tailFinalCtx : Locals.Ctx}
        {tailTrace : OpenExternal.OpenTrace}
        {sourceOutcome : Functions.Source.Outcome}
        {tailCtxAfter : Functions.Source.Ctx}
        {compilerAfter : Objects.Source.State}
        {evmAfter : EvmYul.EVM.State},
        (tailSegment :
          Structured.Preservation.CodeSegment program
            (Structured.Block.compileFromCtx
              { stmts := Expressions.StmtList.toStructured tailStmts }
              structuredCtx supply).code) →
        Locals.Block.compileOpen
          (localsCtx.withLayout (name :: localsCtx.layout))
          (Functions.Block.toLocals returns { stmts := rest }) =
          some (tailStmts, tailFinalCtx) →
        Locals.SourceLowering.StackPrefixRel (name :: layout) compilerAfter []
          evmAfter →
        evmAfter.pc =
          Structured.Preservation.CodeSegment.startPc tailSegment →
        OpenExternal.OpenResultResolves
          (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
            prim programSource
            { sourceCtx with scope := name :: sourceCtx.scope }
            sourceFuel { stmts := rest } compilerAfter)
          tailTrace (.ok (sourceOutcome, tailCtxAfter)) →
        ∃ targetResult,
          OpenExternal.OpenResultResolves
            (OpenAssembly.Source.openRunNResult program tailFuel evmAfter)
            tailTrace (.ok targetResult) ∧
          ResultRel sourceOutcome targetResult)
    {trace : OpenExternal.OpenTrace}
    {sourceOutcome : Functions.Source.Outcome}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
          prim programSource sourceCtx (sourceFuel + 1)
          { stmts := .let_ name valueExpr :: rest } compiler)
        trace (.ok (sourceOutcome, ctxFinal))) :
    ∃ targetFuel targetResult,
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openRunNResult program targetFuel state)
        trace (.ok targetResult) ∧
      ResultRel sourceOutcome targetResult := by
  rcases
      functionsBlock_toLocals_compileOpen_let_cons_inv hCompileBlock with
    ⟨code, restStmts, hCode, hRestCompile, hCompiledStmts⟩
  have hSegmentCode :
      (Structured.Block.compileFromCtx
          { stmts := Expressions.StmtList.toStructured compiledStmts }
          structuredCtx supply).code =
        (Structured.Block.compileFromCtx
          { stmts :=
              Expressions.StmtList.toStructured
                (Locals.codeStmt code ++ restStmts) }
          structuredCtx supply).code := by
    simp [hCompiledStmts]
  let segment' :
      Structured.Preservation.CodeSegment program
        (Structured.Block.compileFromCtx
          { stmts :=
              Expressions.StmtList.toStructured
                (Locals.codeStmt code ++ restStmts) }
          structuredCtx supply).code :=
    Structured.Preservation.CodeSegment.cast_code hSegmentCode segment
  rcases codeSegment_expressions_codeStmt_cons_split segment' with
    ⟨headSegment, tailSegment, hHeadStart, hTailStart, _hTailFall⟩
  have hSegmentStart :
      Structured.Preservation.CodeSegment.startPc segment' =
        Structured.Preservation.CodeSegment.startPc segment := by
    simp [segment', Structured.Preservation.CodeSegment.cast_code,
      Structured.Preservation.CodeSegment.startPc]
  have hHeadPc :
      state.pc =
        Structured.Preservation.CodeSegment.startPc headSegment := by
    rw [hPc, ← hSegmentStart, ← hHeadStart]
  have hTailForHead :
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {sourceOutcome : Functions.Source.Outcome}
        {tailCtxAfter : Functions.Source.Ctx}
        {compilerAfter : Objects.Source.State}
        {evmAfter : EvmYul.EVM.State},
        Locals.SourceLowering.StackPrefixRel (name :: layout) compilerAfter []
          evmAfter →
        evmAfter.pc =
          Structured.Preservation.CodeSegment.fallthroughPc headSegment →
        OpenExternal.OpenResultResolves
          (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
            prim programSource
            { sourceCtx with scope := name :: sourceCtx.scope }
            sourceFuel { stmts := rest } compilerAfter)
          tailTrace (.ok (sourceOutcome, tailCtxAfter)) →
        ∃ targetResult,
          OpenExternal.OpenResultResolves
            (OpenAssembly.Source.openRunNResult program tailFuel evmAfter)
            tailTrace (.ok targetResult) ∧
          ResultRel sourceOutcome targetResult := by
    intro tailTrace sourceOutcome tailCtxAfter compilerAfter evmAfter
      hRel hAfterPc hRest
    have hTailPc :
        evmAfter.pc =
          Structured.Preservation.CodeSegment.startPc tailSegment := by
      rw [hAfterPc]
      exact hTailStart.symm
    exact hTail tailSegment hRestCompile hRel hTailPc hRest
  exact
    compilerOpenFunctionsBlock_let_cons_openRunNResult_of_tail_pc
      hPrim hOwned hSupported hAccess hCode hCtxLayout hNoDup hFresh
      program tailFuel headSegment hHeadPc hPrefixRel hTailForHead hResolve

theorem compilerOpenFunctionsBlock_assign_cons_openRunNResult_of_compileOpen_tail_pc
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {programSource : Functions.Program}
    {sourceCtx ctxFinal : Functions.Source.Ctx}
    {sourceFuel : Nat}
    {returns : List Name}
    {name : Name} {valueExpr : Functions.Expr 1}
    {rest : List Functions.Stmt}
    {localsCtx finalLocalsCtx : Locals.Ctx} {layout : List Name}
    {compiledStmts : List Expressions.Stmt}
    {compiler : Objects.Source.State}
    {state : EvmYul.EVM.State}
    {structuredCtx : Structured.CompileContext}
    {supply : Structured.LabelSupply}
    {idx : Nat}
    (hOwned : Locals.Source.Expr.SourceOwned valueExpr)
    (hSupported : LocalsExprOpenSupported valueExpr)
    (hAccess : Locals.SourceLowering.Expr.Accessible layout 0 valueExpr)
    (hCompileBlock :
      Locals.Block.compileOpen localsCtx
          (Functions.Block.toLocals returns
            { stmts := .assign name valueExpr :: rest }) =
        some (compiledStmts, finalLocalsCtx))
    (hCtxLayout : localsCtx.layout = layout)
    (hNoDup : layout.Nodup)
    (hName : layout[idx]? = some name)
    (hBound : idx + 1 ≤ 16)
    (program : Assembly.Program)
    (tailFuel : Nat)
    (segment :
      Structured.Preservation.CodeSegment program
        (Structured.Block.compileFromCtx
          { stmts := Expressions.StmtList.toStructured compiledStmts }
          structuredCtx supply).code)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler [] state)
    {ResultRel : Functions.Source.Outcome → Assembly.StepResult → Prop}
    (hTail :
      ∀ {tailStmts : List Expressions.Stmt}
        {tailFinalCtx : Locals.Ctx}
        {tailTrace : OpenExternal.OpenTrace}
        {sourceOutcome : Functions.Source.Outcome}
        {tailCtxAfter : Functions.Source.Ctx}
        {compilerAfter : Objects.Source.State}
        {evmAfter : EvmYul.EVM.State},
        (tailSegment :
          Structured.Preservation.CodeSegment program
            (Structured.Block.compileFromCtx
              { stmts := Expressions.StmtList.toStructured tailStmts }
              structuredCtx supply).code) →
        Locals.Block.compileOpen localsCtx
          (Functions.Block.toLocals returns { stmts := rest }) =
          some (tailStmts, tailFinalCtx) →
        Locals.SourceLowering.StackPrefixRel layout compilerAfter []
          evmAfter →
        evmAfter.pc =
          Structured.Preservation.CodeSegment.startPc tailSegment →
        OpenExternal.OpenResultResolves
          (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
            prim programSource sourceCtx sourceFuel { stmts := rest }
            compilerAfter)
          tailTrace (.ok (sourceOutcome, tailCtxAfter)) →
        ∃ targetResult,
          OpenExternal.OpenResultResolves
            (OpenAssembly.Source.openRunNResult program tailFuel evmAfter)
            tailTrace (.ok targetResult) ∧
          ResultRel sourceOutcome targetResult)
    {trace : OpenExternal.OpenTrace}
    {sourceOutcome : Functions.Source.Outcome}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
          prim programSource sourceCtx (sourceFuel + 1)
          { stmts := .assign name valueExpr :: rest } compiler)
        trace (.ok (sourceOutcome, ctxFinal))) :
    ∃ targetFuel targetResult,
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openRunNResult program targetFuel state)
        trace (.ok targetResult) ∧
      ResultRel sourceOutcome targetResult := by
  rcases
      functionsBlock_toLocals_compileOpen_assign_cons_inv hCompileBlock with
    ⟨depth, valueCode, swapOp, restStmts, hDepth, hValue, hSwap,
      hRestCompile, hCompiledStmts⟩
  have hDepthExpected :
      Locals.Layout.lookupDepth? name localsCtx.layout =
        some (idx + 1) := by
    simpa [hCtxLayout] using
      (Locals.Layout.lookupDepth?_of_get?_nodup hName hNoDup)
  have hDepthEq : depth = idx + 1 := by
    rw [hDepthExpected] at hDepth
    cases hDepth
    rfl
  subst depth
  have hSegmentCode :
      (Structured.Block.compileFromCtx
          { stmts := Expressions.StmtList.toStructured compiledStmts }
          structuredCtx supply).code =
        (Structured.Block.compileFromCtx
          { stmts :=
              Expressions.StmtList.toStructured
                (Locals.codeStmt
                  (valueCode ++
                    [Structured.BasicInstr.op swapOp,
                      Structured.BasicInstr.op Structured.BasicOp.pop]) ++
                  restStmts) }
          structuredCtx supply).code := by
    simp [hCompiledStmts]
  let segment' :
      Structured.Preservation.CodeSegment program
        (Structured.Block.compileFromCtx
          { stmts :=
              Expressions.StmtList.toStructured
                (Locals.codeStmt
                  (valueCode ++
                    [Structured.BasicInstr.op swapOp,
                      Structured.BasicInstr.op Structured.BasicOp.pop]) ++
                  restStmts) }
          structuredCtx supply).code :=
    Structured.Preservation.CodeSegment.cast_code hSegmentCode segment
  rcases codeSegment_expressions_codeStmt_cons_split segment' with
    ⟨headSegment, tailSegment, hHeadStart, hTailStart, _hTailFall⟩
  have hSegmentStart :
      Structured.Preservation.CodeSegment.startPc segment' =
        Structured.Preservation.CodeSegment.startPc segment := by
    simp [segment', Structured.Preservation.CodeSegment.cast_code,
      Structured.Preservation.CodeSegment.startPc]
  have hHeadPc :
      state.pc =
        Structured.Preservation.CodeSegment.startPc headSegment := by
    rw [hPc, ← hSegmentStart, ← hHeadStart]
  have hTailForHead :
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {sourceOutcome : Functions.Source.Outcome}
        {tailCtxAfter : Functions.Source.Ctx}
        {compilerAfter : Objects.Source.State}
        {evmAfter : EvmYul.EVM.State},
        Locals.SourceLowering.StackPrefixRel layout compilerAfter []
          evmAfter →
        evmAfter.pc =
          Structured.Preservation.CodeSegment.fallthroughPc headSegment →
        OpenExternal.OpenResultResolves
          (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
            prim programSource sourceCtx sourceFuel { stmts := rest }
            compilerAfter)
          tailTrace (.ok (sourceOutcome, tailCtxAfter)) →
        ∃ targetResult,
          OpenExternal.OpenResultResolves
            (OpenAssembly.Source.openRunNResult program tailFuel evmAfter)
            tailTrace (.ok targetResult) ∧
          ResultRel sourceOutcome targetResult := by
    intro tailTrace sourceOutcome tailCtxAfter compilerAfter evmAfter
      hRel hAfterPc hRest
    have hTailPc :
        evmAfter.pc =
          Structured.Preservation.CodeSegment.startPc tailSegment := by
      rw [hAfterPc]
      exact hTailStart.symm
    exact hTail tailSegment hRestCompile hRel hTailPc hRest
  exact
    compilerOpenFunctionsBlock_assign_cons_openRunNResult_of_tail_pc
      hPrim hOwned hSupported hAccess hValue hCtxLayout hNoDup hName
      hBound hSwap program tailFuel headSegment hHeadPc hPrefixRel
      hTailForHead hResolve

def FunctionsBlockCompiledOutcomeRel
    (asm : Assembly.Program) (ctx : Structured.CompileContext)
    (fallthroughPc : Word) (returns layout : List Name)
    (hiddenReturns : List Structured.ReturnDest) (tokens : List Word)
    (source : Functions.Source.Outcome)
    (target : Assembly.StepResult) : Prop :=
  ∃ direct : Locals.Outcome,
    Functions.SourceDirect.BlockScopedOutcomeRel returns layout hiddenReturns
      source direct ∧
    Structured.Preservation.CompiledOutcomeRel asm ctx fallthroughPc direct
      target tokens

namespace FunctionsBlockCompiledOutcomeRel

theorem regular_nil
    {asm : Assembly.Program} {ctx : Structured.CompileContext}
    {fallthroughPc : Word} {returns layout : List Name}
    {source : Objects.Source.State} {target : EvmYul.EVM.State}
    (hRel :
      Locals.SourceLowering.StackPrefixRel layout source [] target)
    (hPc : target.pc = fallthroughPc) :
    FunctionsBlockCompiledOutcomeRel asm ctx fallthroughPc returns layout
      [] [] (Functions.Source.Outcome.regular source)
      (.running target) := by
  let directState : Structured.RunState := Structured.RunState.initial target
  have hLocal :
      Locals.SourceLowering.StateRel layout source directState := by
    exact
      Locals.SourceLowering.StackPrefixRel.to_stateRel_nil
        (target := directState)
        (by simpa [directState, Structured.RunState.initial] using hRel)
  have hDirectState :
      Functions.SourceDirect.StateRel layout [] source directState := by
    exact ⟨hLocal, rfl⟩
  refine
    ⟨Locals.Outcome.regular directState,
      Functions.SourceDirect.BlockScopedOutcomeRel.regular hDirectState,
      ?_⟩
  exact
    Structured.Preservation.CompiledOutcomeRel.regular
      (Structured.Preservation.Frame.stateRel_initial target) hPc

end FunctionsBlockCompiledOutcomeRel

theorem functionsBlock_toLocals_compileOpen_nil_inv
    {returns : List Name} {ctx finalCtx : Locals.Ctx}
    {compiledStmts : List Expressions.Stmt}
    (hCompile :
      Locals.Block.compileOpen ctx
          (Functions.Block.toLocals returns { stmts := [] }) =
        some (compiledStmts, finalCtx)) :
    compiledStmts = [] ∧ finalCtx = ctx := by
  have h :
      compiledStmts = [] ∧ ctx = finalCtx := by
    simpa [Functions.Block.toLocals, Functions.StmtList.toLocals,
      Locals.Block.compileOpen] using hCompile
  exact ⟨h.1, h.2.symm⟩

theorem compilerOpenFunctionsBlock_nil_openRunNResult_of_compileOpen
    {prim : Objects.Source.PrimitiveSemantics}
    {programSource : Functions.Program}
    {sourceCtx ctxAfter : Functions.Source.Ctx}
    {sourceFuel : Nat}
    {returns : List Name}
    {localsCtx finalLocalsCtx : Locals.Ctx} {layout : List Name}
    {compiledStmts : List Expressions.Stmt}
    {compiler : Objects.Source.State}
    {state : EvmYul.EVM.State}
    {structuredCtx : Structured.CompileContext}
    {supply : Structured.LabelSupply}
    (hCompileBlock :
      Locals.Block.compileOpen localsCtx
          (Functions.Block.toLocals returns { stmts := [] }) =
        some (compiledStmts, finalLocalsCtx))
    (program : Assembly.Program)
    (segment :
      Structured.Preservation.CodeSegment program
        (Structured.Block.compileFromCtx
          { stmts := Expressions.StmtList.toStructured compiledStmts }
          structuredCtx supply).code)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler [] state)
    {trace : OpenExternal.OpenTrace}
    {sourceOutcome : Functions.Source.Outcome}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
          prim programSource sourceCtx sourceFuel { stmts := [] } compiler)
        trace (.ok (sourceOutcome, ctxAfter))) :
    ∃ targetFuel targetResult,
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openRunNResult program targetFuel state)
        trace (.ok targetResult) ∧
      FunctionsBlockCompiledOutcomeRel program structuredCtx
        (Structured.Preservation.CodeSegment.fallthroughPc segment)
        returns layout [] [] sourceOutcome targetResult := by
  rcases functionsBlock_toLocals_compileOpen_nil_inv hCompileBlock with
    ⟨hCompiledStmts, _hFinalCtx⟩
  cases sourceFuel with
  | zero =>
      rw [Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen]
        at hResolve
      cases hResolve
  | succ sourceFuel' =>
      rw [Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen]
        at hResolve
      cases hResolve
      have hFallthrough :
          state.pc =
            Structured.Preservation.CodeSegment.fallthroughPc segment := by
        have hSegmentCode :
            (Structured.Block.compileFromCtx
              { stmts := Expressions.StmtList.toStructured compiledStmts }
              structuredCtx supply).code = [] := by
          simp [hCompiledStmts, Expressions.StmtList.toStructured,
            Structured.Block.compileFromCtx]
        let emptySegment :
            Structured.Preservation.CodeSegment program [] :=
          Structured.Preservation.CodeSegment.cast_code hSegmentCode segment
        have hEmpty :
            Structured.Preservation.CodeSegment.fallthroughPc emptySegment =
              Structured.Preservation.CodeSegment.startPc emptySegment :=
          codeSegment_fallthroughPc_empty emptySegment
        have hStart :
            Structured.Preservation.CodeSegment.startPc emptySegment =
              Structured.Preservation.CodeSegment.startPc segment := by
          simp [emptySegment, Structured.Preservation.CodeSegment.cast_code,
            Structured.Preservation.CodeSegment.startPc]
        have hFall :
            Structured.Preservation.CodeSegment.fallthroughPc emptySegment =
              Structured.Preservation.CodeSegment.fallthroughPc segment := by
          cases segment with
          | mk pre post hAsm hFits =>
              simp [emptySegment,
                Structured.Preservation.CodeSegment.cast_code,
                Structured.Preservation.CodeSegment.fallthroughPc,
                hSegmentCode]
        calc
          state.pc = Structured.Preservation.CodeSegment.startPc segment := hPc
          _ = Structured.Preservation.CodeSegment.startPc emptySegment :=
            hStart.symm
          _ = Structured.Preservation.CodeSegment.fallthroughPc emptySegment :=
            hEmpty.symm
          _ = Structured.Preservation.CodeSegment.fallthroughPc segment :=
            hFall
      refine ⟨0, .running state, ?_, ?_⟩
      · exact OpenExternal.OpenResultResolves.done
      · exact
          FunctionsBlockCompiledOutcomeRel.regular_nil
            (asm := program) (ctx := structuredCtx) (returns := returns)
            (layout := layout) hPrefixRel hFallthrough

def FunctionsBlockToAssemblySourceOpenSoundAt
    (prim : Objects.Source.PrimitiveSemantics)
    (program : Functions.Program) (asm : Assembly.Program)
    (ctx : Functions.Source.Ctx) (sourceFuel : Nat)
    (block : Functions.Block) (sourceInitial : Objects.Source.State)
    (evmInitial : EvmYul.EVM.State) : Prop :=
  ∀ {trace : OpenExternal.OpenTrace}
    {sourceOutcome : Functions.Source.Outcome}
    {ctxAfter : Functions.Source.Ctx},
    OpenExternal.OpenResultResolves
      (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
        prim program ctx sourceFuel block sourceInitial)
      trace (.ok (sourceOutcome, ctxAfter)) →
      ∃ targetFuel targetResult,
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult asm targetFuel evmInitial)
          trace (.ok targetResult) ∧
        Functions.Source.WholeProgramOutcomeRel sourceOutcome targetResult

def FunctionsBlockToCompiledOpenSoundAt
    (prim : Objects.Source.PrimitiveSemantics)
    (program : Functions.Program) (asm : Assembly.Program)
    (ctx : Functions.Source.Ctx) (sourceFuel : Nat)
    (block : Functions.Block) (sourceInitial : Objects.Source.State)
    (evmInitial : EvmYul.EVM.State) : Prop :=
  ∀ {trace : OpenExternal.OpenTrace}
    {sourceOutcome : Functions.Source.Outcome}
    {ctxAfter : Functions.Source.Ctx},
    OpenExternal.OpenResultResolves
      (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
        prim program ctx sourceFuel block sourceInitial)
      trace (.ok (sourceOutcome, ctxAfter)) →
      ∃ targetFuel targetResult,
        OpenExternal.OpenResultResolves
          (OpenAssembly.Compiled.openRunNResult asm targetFuel evmInitial)
          trace (.ok targetResult) ∧
        Functions.Source.WholeProgramOutcomeRel sourceOutcome targetResult

namespace FunctionsBlockToAssemblySourceOpenSoundAt

theorem to_compiled
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    {ctx : Functions.Source.Ctx} {sourceFuel : Nat}
    {block : Functions.Block} {sourceInitial : Objects.Source.State}
    {evmInitial : EvmYul.EVM.State}
    (hCompile : Assembly.compile? asm = some target)
    (hSound :
      FunctionsBlockToAssemblySourceOpenSoundAt prim program asm ctx
        sourceFuel block sourceInitial evmInitial) :
    FunctionsBlockToCompiledOpenSoundAt prim program asm ctx sourceFuel
      block sourceInitial evmInitial := by
  intro trace sourceOutcome ctxAfter hSource
  rcases hSound hSource with
    ⟨targetFuel, targetResult, hAssembly, hOutcome⟩
  rcases
      OpenAssembly.compile_openRunN_result_compiled_sound
        (target := target) hCompile hAssembly with
    ⟨_hAccepted, hCompiled⟩
  exact ⟨targetFuel, targetResult, hCompiled, hOutcome⟩

end FunctionsBlockToAssemblySourceOpenSoundAt

def FunctionsProgramToAssemblySourceOpenSoundAt
    (prim : Objects.Source.PrimitiveSemantics)
    (program : Functions.Program) (asm : Assembly.Program)
    (sourceFuel : Nat) (initial : EvmYul.EVM.State) : Prop :=
  FunctionsBlockToAssemblySourceOpenSoundAt prim program asm
    Functions.Source.Ctx.initial sourceFuel program.body
    (Functions.Source.Program.initialState initial.toSharedState) initial

def FunctionsProgramToCompiledOpenSoundAt
    (prim : Objects.Source.PrimitiveSemantics)
    (program : Functions.Program) (asm : Assembly.Program)
    (sourceFuel : Nat) (initial : EvmYul.EVM.State) : Prop :=
  FunctionsBlockToCompiledOpenSoundAt prim program asm
    Functions.Source.Ctx.initial sourceFuel program.body
    (Functions.Source.Program.initialState initial.toSharedState) initial

theorem FunctionsProgramToAssemblySourceOpenSoundAt.to_compiled
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    {sourceFuel : Nat} {initial : EvmYul.EVM.State}
    (hCompile : Assembly.compile? asm = some target)
    (hSound :
      FunctionsProgramToAssemblySourceOpenSoundAt prim program asm
        sourceFuel initial) :
    FunctionsProgramToCompiledOpenSoundAt prim program asm sourceFuel
      initial :=
  FunctionsBlockToAssemblySourceOpenSoundAt.to_compiled hCompile hSound

end OpenLowering
end Yul
end EvmCompiler
