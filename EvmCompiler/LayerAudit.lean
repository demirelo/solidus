import EvmCompiler.Yul.RecursiveBridgeSupport
import EvmCompiler.Yul.NoCallCreate
import EvmCompiler.Yul.NoCallRuntime
import EvmCompiler.Functions.SourceLowering
import EvmCompiler.Objects.Layout
import EvmCompiler.Solidity.Frontend

namespace EvmCompiler
namespace LayerAudit

/-
Checked theorem spine for the currently implemented layers.

This file is intentionally small: each definition below is just a typechecked
alias to the public theorem that connects one layer's source interpreter to the
next lower layer. It is an audit tripwire, not another compiler pass.
-/
namespace Interpreters

/-- Labeled assembly source semantics over symbolic labels and gasless EVM state. -/
abbrev assemblySourceRun :=
  @Assembly.Source.runNResult

/-- Resolved assembly/bytecode-level target semantics. -/
abbrev assemblyTargetRun :=
  @Assembly.Target.runNResult

/-- Structured control source semantics. -/
abbrev structuredRun :=
  @Structured.Program.run

/-- Expression-aware source semantics. -/
abbrev expressionsRun :=
  @Expressions.Program.run

/-- Local-variable/scoped source semantics. -/
abbrev localsRun :=
  @Locals.Program.run

/-- Stack-free local-variable source semantics for higher-layer bridges. -/
abbrev localsSourceRunState :=
  @Locals.Source.Program.runState

/-- Stack-free local-variable source semantics from an EVM shared state. -/
abbrev localsSourceRun :=
  @Locals.Source.Program.run

abbrev localsSourceExprEvalVarsEq :=
  @Locals.Source.Expr.eval_vars_eq

abbrev localsSourceExprSeqEvalVarsEq :=
  @Locals.Source.Expr.evalSeq_vars_eq

abbrev localsSourceExprEvalOneVarsEq :=
  @Locals.Source.Expr.evalOne_vars_eq

/-- The direct scoped-stack interpreter used by the public locals layer. -/
abbrev localsDirectRun :=
  @Locals.Direct.Program.run

/-- Function-call source semantics. -/
abbrev functionsRun :=
  @Functions.Program.run

/-- Stack-free function-call source semantics for higher-layer bridges. -/
abbrev functionsSourceRunState :=
  @Functions.Source.Program.runState

/-- The direct function interpreter used by the public function layer. -/
abbrev functionsDirectRun :=
  @Functions.Direct.Program.run

/-- Object source semantics over the root object wrapper. -/
abbrev objectsRun :=
  @Objects.Program.run

/-- Object source semantics over the stack-free function source interpreter. -/
abbrev objectsSourceRunState :=
  @Objects.Source.Program.runState

/-- Imported Nethermind Yul source semantics. -/
abbrev importedYulRun :=
  @Yul.Program.run

/--
Compiler-facing Yul lowering semantics. This is intentionally quarantined:
it is useful for composing the existing compiler path, but it is not the
independent imported source interpreter.
-/
noncomputable abbrev yulLoweredRun :=
  @Yul.Lowered.run

/--
Compiler-facing Yul lowering into the repaired source tower. This is the
intended target for the imported-reference bridge as lower source-to-direct
preservation theorems are filled in.
-/
noncomputable abbrev yulSourceLoweredRunState :=
  @Yul.SourceLowered.runState

end Interpreters

namespace Adjacent

abbrev assemblyToBytecode :=
  @Assembly.compile_whole_program_result_sound

abbrev structuredToAssembly :=
  @Structured.Preservation.compile_preserves

abbrev expressionsToStructured :=
  @Expressions.Program.compile_preserves_of_compileChecked

abbrev expressionsToStructuredRawCompile :=
  @Expressions.Program.compile_preserves

abbrev localsToExpressions :=
  @Locals.Program.compile_preserves_checked

abbrev localsToExpressionsRawCompile :=
  @Locals.Program.compile_preserves

noncomputable abbrev localsSourceCompileChecked :=
  @Locals.Source.Program.compileChecked?

abbrev localsSourceCompileCheckedEqSome :=
  @Locals.Source.Program.compileChecked?_eq_some

/--
Source-facing locals compiler theorem. This is the boundary higher layers
should target: the direct scoped-stack outcome is hidden behind
`Locals.Source.WholeProgramOutcomeRel`.
-/
abbrev localsSourceToAssembly :=
  @Locals.Source.Program.compile_preserves_checked_of_compileAccepted

abbrev functionsToLocals :=
  @Functions.Program.compile_preserves_checked

abbrev functionsToLocalsRawCompile :=
  @Functions.Program.compile_preserves

/--
Source-facing function compiler theorem. This is the boundary higher layers
should target: the direct procedure outcome is hidden behind
`Functions.Source.WholeProgramOutcomeRel`.
-/
abbrev functionsSourceToAssembly :=
  @Functions.Source.Program.compile_preserves_checked_of_compileAccepted

/--
Raw function/source helper that still exposes source scopedness and frame-bound
resource premises. Keep it named as a lower proof helper, not as the public
source-facing compiler spine.
-/
abbrev functionsSourceToAssemblyRawFrameBound :=
  @Functions.Source.Program.compile_preserves

abbrev functionsSourceToAssemblyOfCompileAccepted :=
  @Functions.Source.Program.compile_preserves_of_compileAccepted

abbrev objectsToFunctions :=
  @Objects.Program.compile_preserves_checked

abbrev objectsToFunctionsRawCompile :=
  @Objects.Program.compile_preserves

/--
Source-facing object compiler theorem. Objects are still a transparent root
wrapper, but this path composes through `Functions.Source.Program` rather than
the direct procedure backend.
-/
abbrev objectsSourceToAssembly :=
  @Objects.Source.Program.compile_preserves_checked_of_compileAccepted

/--
Raw object/source helper that still exposes the function frame-bound resource
premise.  Keep it named as a lower proof helper, not as the public source-facing
compiler spine.
-/
abbrev objectsSourceToAssemblyRawFrameBound :=
  @Objects.Source.Program.compile_preserves

abbrev objectsSourceToAssemblyOfCompileAccepted :=
  @Objects.Source.Program.compile_preserves_of_compileAccepted

/--
Compiler-facing Yul preservation is checked only for the quarantined lowered
semantics. The active imported-source path should connect Nethermind runs to
`Yul.SourceLowered.run` with per-construct source-tower facts and then use the
source-run preservation theorems below. The legacy `Reference.SourceBridge` and
`Reference.LoweredBridge` compatibility paths are backend-only / audit-visible
and must not be treated as the independent imported-source proof.
-/
abbrev yulLoweredToObjects :=
  @Yul.Program.compile_preserves_checked

/--
Compiler-facing Yul preservation through the repaired source tower. This is the
right theorem for higher-layer bridge work: the target semantics is
`Yul.SourceLowered.run`, not the backend-only `Yul.Lowered.run`.
-/
abbrev yulSourceLoweredToAssembly :=
  @Yul.Program.compile_source_preserves_checked_of_compileAccepted

/--
Raw Yul/source-lowered helper that still exposes generated object frame bounds.
The public source-facing route should use `Yul.Program.SourceCompileAccepted`.
-/
abbrev yulSourceLoweredToAssemblyRawFrameBound :=
  @Yul.Program.compile_source_preserves_checked

abbrev yulSourceLoweredToAssemblyOfCompileAccepted :=
  @Yul.Program.compile_source_preserves_of_compileAccepted

abbrev yulSourceLoweredToAssemblyCheckedOfCompileAccepted :=
  @Yul.Program.compile_source_preserves_checked_of_compileAccepted

end Adjacent

namespace InterpreterConnections

abbrev expressionsRunToStructured :=
  @Expressions.Program.run_toStructured

abbrev localsRunToExpressions :=
  @Locals.Program.run_toExpressions_exists

abbrev localsSourceRunToDirect :=
  @Locals.Source.Program.run_toDirect_exists

abbrev localsSourceRunStateToDirect :=
  @Locals.Source.Program.runState_toDirect_exists

abbrev functionsRunToLocals :=
  @Functions.Direct.Program.run_toLocals_exists

abbrev functionsSourceRunStateToDirectOfCompileAccepted :=
  @Functions.Source.Program.runState_toDirect_exists_of_compileAccepted

abbrev functionsSourceRunToDirectOfCompileAccepted :=
  @Functions.Source.Program.run_toDirect_exists_of_compileAccepted

/--
Objects currently introduce no executable object-level behavior beyond choosing
the root object's code, so this is an explicit transparent-adapter theorem.
-/
abbrev objectsRunToFunctions :=
  @Objects.Program.run_toFunctions

abbrev objectsEvalToFunctions :=
  @Objects.Program.eval_toFunctions

abbrev objectsSourceObjectRunStateToFunctions :=
  @Objects.Source.Object.runState_toFunctions

abbrev objectsSourceObjectEvalToFunctions :=
  @Objects.Source.Object.eval_toFunctions

abbrev objectsSourceProgramRunStateToFunctions :=
  @Objects.Source.Program.runState_toFunctions

abbrev objectsSourceProgramEvalToFunctions :=
  @Objects.Source.Program.eval_toFunctions

abbrev yulSourceLoweredRunStateOfToObjects :=
  @Yul.SourceLowered.runState_of_toObjects?

abbrev yulSourceLoweredRunOfToObjects :=
  @Yul.SourceLowered.run_of_toObjects?

/-- Public locals are a thin wrapper around the direct locals interpreter. -/
theorem localsRunToDirect :
    @Locals.Program.run = @Locals.Direct.Program.run :=
  rfl

/--
Backend compatibility: the legacy executable `Functions.Program.run` is still
the direct function interpreter. Higher layers should target
`Functions.Source.Program.runState` / `Functions.Source.Program.run` and the
source-facing compiler theorem above.
-/
theorem functionsRunToDirect :
    @Functions.Program.run = @Functions.Direct.Program.run :=
  rfl

end InterpreterConnections

namespace Acceptance

abbrev expressionsAccepted :=
  @Expressions.Program.Accepted

abbrev expressionsSourceAccepted :=
  @Expressions.Program.SourceAccepted

abbrev localsAccepted :=
  @Locals.Program.Accepted

abbrev localsSourceAccepted :=
  @Locals.Program.SourceAccepted

abbrev localsSourceCompileAccepted :=
  @Locals.Source.Program.CompileAccepted

abbrev localsScoped :=
  @Locals.Program.Scoped

abbrev localsLexicalScoped :=
  @Locals.Lexical.ProgramScoped

abbrev localsSourceWF :=
  @Locals.Source.Program.SourceWF

abbrev localsSourceOwnedOfSourceWF :=
  @Locals.Source.Program.sourceOwned_of_sourceWF

abbrev localsLexicalScopedOfSourceWF :=
  @Locals.Source.Program.lexicalScoped_of_sourceWF

abbrev localsSourceWFExprScoped :=
  @Locals.SourceLowering.SourceWF.expr_scoped

abbrev localsSourceWFExprSeqScoped :=
  @Locals.SourceLowering.SourceWF.exprSeq_scoped

abbrev localsSourceWFBlockScoped :=
  @Locals.SourceLowering.SourceWF.block_scoped

abbrev localsSourceWFStmtScoped :=
  @Locals.SourceLowering.SourceWF.stmt_scoped

abbrev localsSourceWFProgramScoped :=
  @Locals.SourceLowering.SourceWF.program_scoped_of_sourceWF

abbrev localsSourceAcceptedProgramScoped :=
  @Locals.SourceLowering.SourceWF.program_scoped_of_sourceAccepted

abbrev localsScopeBlockScoped :=
  @Locals.Scope.Block.Scoped

abbrev localsScopeStmtScoped :=
  @Locals.Scope.Stmt.Scoped

abbrev localsScopeBlockOutEnvNodup :=
  @Locals.Block.scoped_outEnv_nodup

abbrev functionsAccepted :=
  @Functions.Program.Accepted

abbrev functionsSourceAccepted :=
  @Functions.Program.SourceAccepted

abbrev functionsSourceCompileAccepted :=
  @Functions.Source.Program.CompileAccepted

abbrev functionsSourceAcceptedOfAccepted :=
  @Functions.Program.sourceAccepted_of_accepted

abbrev objectsAccepted :=
  @Objects.Program.Accepted

abbrev objectsSourceAccepted :=
  @Objects.Program.SourceAccepted

abbrev objectsSourceCompileAccepted :=
  @Objects.Source.Program.CompileAccepted

abbrev objectsSourceAcceptedOfAccepted :=
  @Objects.Program.sourceAccepted_of_accepted

namespace ObjectData

abbrev dataSectionPayloadBytes :=
  @Objects.DataSection.Sections.payloadBytes

abbrev frontendDataSectionPayloadBytes :=
  @Solidity.Frontend.DataSection.List.payloadBytes

abbrev frontendDataToBackendPayloadBytes :=
  @Solidity.Frontend.DataSection.List.toObjects_payloadBytes

abbrev frontendDataToBackendNamedSizeEntries :=
  @Solidity.Frontend.DataSection.List.toObjects_namedSizeEntries

abbrev frontendDataToBackendNamedOffsetEntries :=
  @Solidity.Frontend.DataSection.List.toObjects_namedOffsetEntriesFromNat

noncomputable abbrev objectImageBytes :=
  @Objects.Object.imageBytes?

noncomputable abbrev objectPayloadLayout :=
  @Objects.Object.payloadLayout?

noncomputable abbrev programBytecodeImage :=
  @Objects.Program.bytecodeImage?

abbrev frontendResolveDatasizeToYul :=
  @Solidity.Frontend.Expr.toYul_after_resolveObjectBuiltins_datasize_namedData

abbrev frontendResolveDataoffsetToYul :=
  @Solidity.Frontend.Expr.toYul_after_resolveObjectBuiltins_dataoffset_namedDataBase

abbrev frontendResolveDatacopyToYulCodecopy :=
  @Solidity.Frontend.Expr.toYul_after_resolveObjectBuiltins_datacopy_codecopy

noncomputable abbrev frontendCompileCheckedWithLayout :=
  @Solidity.Frontend.Program.compileCheckedWithLayout?

abbrev frontendCompileCheckedWithLayoutEqSome :=
  @Solidity.Frontend.Program.compileCheckedWithLayout?_eq_some

abbrev frontendCompileCheckedWithLayoutSomeLower :=
  @Solidity.Frontend.Program.compileCheckedWithLayout?_some_lower

noncomputable abbrev frontendCompileCheckedWithLocalDataBase :=
  @Solidity.Frontend.Program.compileCheckedWithLocalDataBase?

abbrev frontendCompileCheckedWithLocalDataBaseEqSome :=
  @Solidity.Frontend.Program.compileCheckedWithLocalDataBase?_eq_some

abbrev frontendCompileCheckedWithLocalDataBaseSomeLower :=
  @Solidity.Frontend.Program.compileCheckedWithLocalDataBase?_some_lower

end ObjectData

abbrev yulAccepted :=
  @Yul.Program.Accepted

abbrev yulFullSafePrimitive :=
  @Yul.Reference.Safe.Full.primitive

abbrev yulFullSafeExpr :=
  @Yul.Reference.Safe.Full.expr

abbrev yulFullSafeStmt :=
  @Yul.Reference.Safe.Full.stmt

abbrev yulFullSafeProgram :=
  @Yul.Reference.Safe.Full.program

abbrev yulReferenceFullAccepted :=
  @Yul.Reference.FullAccepted

abbrev yulReferenceFullAcceptedOfAccepted :=
  @Yul.Reference.fullAccepted_of_accepted

abbrev yulFeatureCoverageProgram :=
  @Yul.Reference.Safe.FeatureCoverage.program

abbrev yulBridgeCoveredAccepted :=
  @Yul.Reference.BridgeCoveredAccepted

abbrev yulBridgeCoveredAcceptedIffAccepted :=
  @Yul.Reference.bridgeCoveredAccepted_iff_accepted

abbrev yulSourceAccepted :=
  @Yul.Program.SourceAccepted

abbrev yulSourceCompileAccepted :=
  @Yul.Program.SourceCompileAccepted

abbrev yulSourceAcceptedOfAccepted :=
  @Yul.Program.sourceAccepted_of_accepted

end Acceptance

namespace SourceTowerRepair

abbrev functionsCtxToLocals :=
  @Functions.SourceLowering.Ctx.toLocals

abbrev functionsLowerAssignReturnedTopsRev :=
  @Functions.Lower.assignReturnedTopsRev

abbrev functionsDirectAssignTopWithOffset :=
  @Functions.Direct.assignTopWithOffset

abbrev functionsAtomicSourceOwned :=
  @Functions.SourceLowering.SourceToLocals.Stmt.AtomicSourceOwned

abbrev functionsAtomicListSourceOwned :=
  @Functions.SourceLowering.SourceToLocals.StmtList.AtomicSourceOwned

abbrev functionsAtomicBlockSourceOwned :=
  @Functions.SourceLowering.SourceToLocals.Block.AtomicSourceOwned

abbrev functionsSourceOwnedBlock :=
  @Functions.SourceLowering.SourceToLocals.Block.SourceOwned

abbrev functionsSourceOwnedStmt :=
  @Functions.SourceLowering.SourceToLocals.Stmt.SourceOwned

abbrev functionsSourceOwnedStmtList :=
  @Functions.SourceLowering.SourceToLocals.StmtList.SourceOwned

abbrev localsSourceBlockRegularEqRestrict :=
  @Locals.Source.Block.runScoped_regular_eq_restrict

abbrev localsSourceStmtRegularScope :=
  @Locals.Source.Stmt.run_regular_scope

abbrev localsSourceBlockOpenRegularScope :=
  @Locals.Source.Block.runOpen_regular_scope

abbrev localsSourceBlockRegularDropsNotMem :=
  @Locals.Source.Block.runScoped_regular_drops_not_mem

abbrev localsSourcePrimitiveSemanticsStructured :=
  Locals.Source.PrimitiveSemantics.structured

abbrev localsSourceLoweringPrimitiveSound :=
  @Locals.SourceLowering.PrimitiveSound

abbrev localsSourcePrimitiveSemanticsStructuredEvalStep :=
  @Locals.SourceLowering.PrimitiveSemantics.structured_eval_step

abbrev localsSourcePrimitiveSemanticsStructuredEvalStepExists :=
  @Locals.SourceLowering.PrimitiveSemantics.structured_eval_step_exists

abbrev localsSourcePrimitiveSemanticsStructuredEvalLength :=
  @Locals.SourceLowering.PrimitiveSemantics.structured_eval_length

abbrev localsSourcePrimitiveSemanticsStructuredPrimitiveSound :=
  @Locals.SourceLowering.PrimitiveSemantics.structured_primitiveSound

abbrev localsSourceLoweringPrimitiveSoundTerminalStep :=
  @Locals.SourceLowering.PrimitiveSound.terminal_step

abbrev localsSourceLoweringPrimitiveSoundTerminalStepExists :=
  @Locals.SourceLowering.PrimitiveSound.terminal_step_exists

abbrev localsSourcePrimitiveSemanticsStructuredTerminalStopStep :=
  @Locals.SourceLowering.PrimitiveSemantics.structured_terminal_stop_step

abbrev localsSourcePrimitiveSemanticsStructuredTerminalStopStepExists :=
  @Locals.SourceLowering.PrimitiveSemantics.structured_terminal_stop_step_exists

abbrev localsSourcePrimitiveSemanticsStructuredTerminalReturnStep :=
  @Locals.SourceLowering.PrimitiveSemantics.structured_terminal_return_step

abbrev localsSourcePrimitiveSemanticsStructuredTerminalReturnStepExists :=
  @Locals.SourceLowering.PrimitiveSemantics.structured_terminal_return_step_exists

abbrev localsSourcePrimitiveSemanticsStructuredTerminalRevertStep :=
  @Locals.SourceLowering.PrimitiveSemantics.structured_terminal_revert_step

abbrev localsSourcePrimitiveSemanticsStructuredTerminalRevertStepExists :=
  @Locals.SourceLowering.PrimitiveSemantics.structured_terminal_revert_step_exists

abbrev localsSourcePrimitiveSemanticsStructuredTerminalSelfdestructStep :=
  @Locals.SourceLowering.PrimitiveSemantics.structured_terminal_selfdestruct_step

abbrev localsSourcePrimitiveSemanticsStructuredTerminalSelfdestructStepExists :=
  @Locals.SourceLowering.PrimitiveSemantics.structured_terminal_selfdestruct_step_exists

abbrev localsSourcePrimitiveSemanticsStructuredTerminalStep :=
  @Locals.SourceLowering.PrimitiveSemantics.structured_terminal_step

abbrev localsSourcePrimitiveSemanticsStructuredTerminalStepExists :=
  @Locals.SourceLowering.PrimitiveSemantics.structured_terminal_step_exists

abbrev localsSourceLoweringExprAccessible :=
  @Locals.SourceLowering.Expr.Accessible

abbrev localsSourceLoweringExprSeqAccessible :=
  @Locals.SourceLowering.ExprSeq.Accessible

abbrev localsSourceLoweringAccessExprWidth :=
  @Locals.SourceLowering.Access.exprWidth

abbrev localsSourceLoweringAccessExprSeqWidth :=
  @Locals.SourceLowering.Access.exprSeqWidth

abbrev localsSourceLoweringAccessExprBound :=
  @Locals.SourceLowering.Access.ExprBound

abbrev localsSourceLoweringAccessExprSeqBound :=
  @Locals.SourceLowering.Access.ExprSeqBound

abbrev localsSourceLoweringAtomicStmtHolds :=
  @Locals.SourceLowering.AtomicStmt.Holds

abbrev localsSourceLoweringAtomicStmtAccessBound :=
  @Locals.SourceLowering.AtomicStmt.AccessBound

abbrev localsSourceLoweringAtomicStmtSourceAccessBound :=
  @Locals.SourceLowering.AtomicStmt.SourceAccessBound

abbrev localsSourceLoweringAtomicStmtAccessBoundOfSourceAccessBound :=
  @Locals.SourceLowering.AtomicStmt.accessBound_of_sourceAccessBound

abbrev localsSourceLoweringStructuralAtomicLowerable :=
  @Locals.SourceLowering.Structural.AtomicLowerable

abbrev localsSourceLoweringStructuralBlockLowerable :=
  @Locals.SourceLowering.Structural.BlockLowerable

abbrev localsSourceLoweringStructuralStmtLowerable :=
  @Locals.SourceLowering.Structural.StmtLowerable

abbrev localsSourceLoweringStructuralStmtListLowerable :=
  @Locals.SourceLowering.Structural.StmtListLowerable

abbrev localsSourceLoweringStructuralCaseListLowerable :=
  @Locals.SourceLowering.Structural.CaseListLowerable

abbrev localsSourceLoweringStructuralDefaultLowerable :=
  @Locals.SourceLowering.Structural.DefaultLowerable

abbrev localsSourceLoweringStructuralAtomicLowerableScoped :=
  @Locals.SourceLowering.Structural.atomicLowerable_scoped

abbrev localsSourceLoweringStructuralAtomicLowerableSourceAccessBound :=
  @Locals.SourceLowering.Structural.atomicLowerable_sourceAccessBound

abbrev localsSourceLoweringStructuralAtomicLowerableHolds :=
  @Locals.SourceLowering.Structural.atomicLowerable_holds

abbrev localsSourceLoweringStructuralBlockLowerableScoped :=
  @Locals.SourceLowering.Structural.blockLowerable_scoped

abbrev localsSourceLoweringStructuralStmtLowerableScoped :=
  @Locals.SourceLowering.Structural.stmtLowerable_scoped

abbrev localsSourceLoweringStructuralStmtListLowerableScoped :=
  @Locals.SourceLowering.Structural.stmtListLowerable_scoped

abbrev localsSourceLoweringStructuralCaseListLowerableScoped :=
  @Locals.SourceLowering.Structural.caseListLowerable_scoped

abbrev localsSourceLoweringStructuralDefaultLowerableScoped :=
  @Locals.SourceLowering.Structural.defaultLowerable_scoped

abbrev localsSourceLoweringStructuralBlockMeasure :=
  Locals.SourceLowering.Structural.BlockMeasure

abbrev localsSourceLoweringStructuralStmtMeasure :=
  Locals.SourceLowering.Structural.StmtMeasure

abbrev localsSourceLoweringStructuralStmtListMeasure :=
  Locals.SourceLowering.Structural.StmtListMeasure

abbrev localsSourceLoweringStructuralSelectLowerable :=
  @Locals.SourceLowering.Structural.select_lowerable

abbrev localsSourceLoweringScopeExprSourceOwnedOfScoped :=
  @Locals.SourceLowering.Scope.expr_sourceOwned_of_scoped

abbrev localsSourceLoweringScopeExprSeqSourceOwnedOfScoped :=
  @Locals.SourceLowering.Scope.exprSeq_sourceOwned_of_scoped

abbrev localsSourceLoweringCtxRelExprAccessibleOfScoped :=
  @Locals.SourceLowering.CtxRel.expr_accessible_of_scoped

abbrev localsSourceLoweringCtxRelExprSeqAccessibleOfScoped :=
  @Locals.SourceLowering.CtxRel.exprSeq_accessible_of_scoped

abbrev localsSourceLoweringCtxRelExprAccessibleOfScopedBound :=
  @Locals.SourceLowering.CtxRel.expr_accessible_of_scoped_bound

abbrev localsSourceLoweringCtxRelExprSeqAccessibleOfScopedBound :=
  @Locals.SourceLowering.CtxRel.exprSeq_accessible_of_scoped_bound

abbrev localsSourceLoweringExprEvalLengthOfSourceOwned :=
  @Locals.SourceLowering.Expr.eval_length_of_sourceOwned

abbrev localsSourceLoweringExprSeqEvalLengthOfSourceOwned :=
  @Locals.SourceLowering.Expr.evalSeq_length_of_sourceOwned

abbrev localsSourceLoweringStackPrefixRel :=
  @Locals.SourceLowering.StackPrefixRel

abbrev localsSourceLoweringStackPrefixRelOfStateRel :=
  @Locals.SourceLowering.StackPrefixRel.of_stateRel

abbrev localsSourceLoweringStackPrefixRelToStateRelNil :=
  @Locals.SourceLowering.StackPrefixRel.to_stateRel_nil

abbrev localsSourceLoweringCleanupScopeRel :=
  @Locals.SourceLowering.CleanupScopeRel

abbrev localsSourceLoweringCleanupScopeRelRefl :=
  @Locals.SourceLowering.CleanupScopeRel.refl

abbrev localsSourceLoweringCleanupScopeRelCons :=
  @Locals.SourceLowering.CleanupScopeRel.cons

abbrev localsSourceLoweringCleanupScopeRelTrans :=
  @Locals.SourceLowering.CleanupScopeRel.trans

abbrev localsSourceLoweringScopeStmtOutEnvCleanupScopeRel :=
  @Locals.SourceLowering.Scope.stmt_outEnv_cleanupScopeRel

abbrev localsSourceLoweringScopeStmtListOutEnvCleanupScopeRel :=
  @Locals.SourceLowering.Scope.stmtList_outEnv_cleanupScopeRel

abbrev localsSourceLoweringScopeBlockOutEnvCleanupScopeRel :=
  @Locals.SourceLowering.Scope.block_outEnv_cleanupScopeRel

abbrev localsSourceLoweringCtxHandlersRel :=
  @Locals.SourceLowering.CtxHandlersRel

abbrev localsSourceLoweringCtxHandlersRelInitial :=
  @Locals.SourceLowering.CtxHandlersRel.initial

abbrev localsSourceLoweringCtxHandlersRelWithoutLoopControl :=
  @Locals.SourceLowering.CtxHandlersRel.withoutLoopControl

abbrev localsSourceLoweringCtxHandlersRelWithLoopControlSelf :=
  @Locals.SourceLowering.CtxHandlersRel.withLoopControl_self

abbrev localsSourceLoweringCtxHandlersRelWithScopeCons :=
  @Locals.SourceLowering.CtxHandlersRel.withScopeCons

abbrev localsSourceLoweringCtxInv :=
  @Locals.SourceLowering.CtxInv

abbrev localsSourceLoweringLoweringStateRel :=
  @Locals.SourceLowering.LoweringStateRel

abbrev localsSourceLoweringStateRelInitial :=
  @Locals.SourceLowering.StateRel.initial

abbrev localsSourceLoweringStackStoreRelRestrictToSelf :=
  @Locals.SourceLowering.StackStoreRel.restrictTo_self

abbrev localsSourceLoweringStateRelRestrictToSelf :=
  @Locals.SourceLowering.StateRel.restrictTo_self

abbrev localsSourceLoweringStateRelCleanupAllExists :=
  @Locals.SourceLowering.StateRel.cleanupAll_exists

abbrev localsSourceLoweringStateRelCleanupToScopeExists :=
  @Locals.SourceLowering.StateRel.cleanupTo_scope_exists

abbrev localsSourceLoweringOutcomeRelHaltShared :=
  @Locals.SourceLowering.OutcomeRel.halt_shared

abbrev localsSourceLoweringExprRunCodeOfEvalSourceOwned :=
  @Locals.SourceLowering.Expr.runCode_of_eval_sourceOwned

abbrev localsSourceLoweringExprSeqRunCodeOfEvalSourceOwned :=
  @Locals.SourceLowering.Expr.runSeqCode_of_eval_sourceOwned

abbrev localsSourceLoweringExprEvalOneBridgeSourceOwned :=
  @Locals.SourceLowering.Expr.evalOne_bridge_sourceOwned

abbrev localsSourceLoweringExprEvalConditionBridgeSourceOwned :=
  @Locals.SourceLowering.Expr.evalCondition_bridge_sourceOwned

abbrev localsSourceLoweringExprEvalOnePopBridgeSourceOwned :=
  @Locals.SourceLowering.Expr.evalOne_pop_bridge_sourceOwned

abbrev localsSourceLoweringSwitchSourceSelectEq :=
  @Locals.SourceLowering.Switch.source_select_eq

abbrev localsSourceLoweringStmtExprBridge :=
  @Locals.SourceLowering.Stmt.expr_bridge

abbrev localsSourceLoweringStmtLetExprBridge :=
  @Locals.SourceLowering.Stmt.let_expr_bridge

abbrev localsSourceLoweringStmtAssignExprBridge :=
  @Locals.SourceLowering.Stmt.assign_expr_bridge

abbrev localsSourceLoweringStmtBreakBridge :=
  @Locals.SourceLowering.Stmt.brk_bridge

abbrev localsSourceLoweringStmtContinueBridge :=
  @Locals.SourceLowering.Stmt.cont_bridge

abbrev localsSourceLoweringStmtTerminalBridge :=
  @Locals.SourceLowering.Stmt.terminal_bridge

abbrev localsSourceLoweringStmtTerminalArgsBridge :=
  @Locals.SourceLowering.Stmt.terminalArgs_bridge

abbrev localsSourceLoweringRunResultRel :=
  @Locals.SourceLowering.RunResultRel

abbrev localsSourceLoweringRunResultRelAt :=
  @Locals.SourceLowering.RunResultRelAt

abbrev localsSourceLoweringHandlerScopesEq :=
  @Locals.SourceLowering.HandlerScopesEq

abbrev localsSourceLoweringHandlerScopesEqRefl :=
  @Locals.SourceLowering.HandlerScopesEq.refl

abbrev localsSourceLoweringHandlerScopesEqSymm :=
  @Locals.SourceLowering.HandlerScopesEq.symm

abbrev localsSourceLoweringHandlerScopesEqTrans :=
  @Locals.SourceLowering.HandlerScopesEq.trans

abbrev localsSourceLoweringStructuralStmtLowerableRegularHandlerScopesEq :=
  @Locals.SourceLowering.Structural.stmtLowerable_regular_handlerScopesEq

abbrev localsSourceLoweringStructuralBlockLowerableRegularHandlerScopesEq :=
  @Locals.SourceLowering.Structural.blockLowerable_regular_handlerScopesEq

abbrev localsSourceLoweringStructuralStmtListLowerableRegularHandlerScopesEq :=
  @Locals.SourceLowering.Structural.stmtListLowerable_regular_handlerScopesEq

abbrev localsSourceLoweringRunResultRelAtRebase :=
  @Locals.SourceLowering.RunResultRelAt.rebase

abbrev localsSourceLoweringRunResultRelAtToRunResultRel :=
  @Locals.SourceLowering.RunResultRelAt.toRunResultRel

abbrev localsSourceLoweringRunResultRelRegular :=
  @Locals.SourceLowering.RunResultRel.regular

abbrev localsSourceLoweringScopedOutcomeRel :=
  @Locals.SourceLowering.ScopedOutcomeRel

abbrev localsSourceLoweringScopedOutcomeRelAt :=
  @Locals.SourceLowering.ScopedOutcomeRelAt

abbrev localsSourceLoweringScopedOutcomeRelAtToScopedOutcomeRel :=
  @Locals.SourceLowering.ScopedOutcomeRelAt.toScopedOutcomeRel

abbrev localsSourceLoweringScopedOutcomeRelAtToRunResultRelAt :=
  @Locals.SourceLowering.ScopedOutcomeRelAt.toRunResultRelAt

abbrev localsSourceLoweringStmtRunBridge :=
  @Locals.SourceLowering.StmtRunBridge

abbrev localsSourceLoweringStmtRunBridgeAt :=
  @Locals.SourceLowering.StmtRunBridgeAt

abbrev localsSourceLoweringStmtRunBridgeAtToStmtRunBridge :=
  @Locals.SourceLowering.StmtRunBridgeAt.toStmtRunBridge

abbrev localsSourceLoweringStmtRunBridgeAtRebase :=
  @Locals.SourceLowering.StmtRunBridgeAt.rebase

abbrev localsSourceLoweringStmtRunBridgeAtExpr :=
  @Locals.SourceLowering.StmtRunBridgeAt.expr

abbrev localsSourceLoweringStmtRunBridgeAtLetExpr :=
  @Locals.SourceLowering.StmtRunBridgeAt.letExpr

abbrev localsSourceLoweringStmtRunBridgeAtAssignExpr :=
  @Locals.SourceLowering.StmtRunBridgeAt.assign_expr

abbrev localsSourceLoweringStmtRunBridgeAtBreak :=
  @Locals.SourceLowering.StmtRunBridgeAt.brk

abbrev localsSourceLoweringStmtRunBridgeAtContinue :=
  @Locals.SourceLowering.StmtRunBridgeAt.cont

abbrev localsSourceLoweringStmtRunBridgeAtTerminal :=
  @Locals.SourceLowering.StmtRunBridgeAt.terminal

abbrev localsSourceLoweringStmtRunBridgeAtTerminalArgs :=
  @Locals.SourceLowering.StmtRunBridgeAt.terminalArgs

abbrev localsSourceLoweringStmtRunBridgeAtExprFromScopedSourceRun :=
  @Locals.SourceLowering.StmtRunBridgeAt.expr_from_scoped_source_run

abbrev localsSourceLoweringStmtRunBridgeAtLetExprFromScopedSourceRun :=
  @Locals.SourceLowering.StmtRunBridgeAt.letExpr_from_scoped_source_run

abbrev localsSourceLoweringStmtRunBridgeAtAssignExprFromScopedSourceRun :=
  @Locals.SourceLowering.StmtRunBridgeAt.assign_expr_from_scoped_source_run

abbrev localsSourceLoweringStmtRunBridgeAtBreakFromSourceRun :=
  @Locals.SourceLowering.StmtRunBridgeAt.brk_from_source_run

abbrev localsSourceLoweringStmtRunBridgeAtContinueFromSourceRun :=
  @Locals.SourceLowering.StmtRunBridgeAt.cont_from_source_run

abbrev localsSourceLoweringStmtRunBridgeAtTerminalFromSourceRun :=
  @Locals.SourceLowering.StmtRunBridgeAt.terminal_from_source_run

abbrev localsSourceLoweringStmtRunBridgeAtTerminalArgsFromScopedSourceRun :=
  @Locals.SourceLowering.StmtRunBridgeAt.terminalArgs_from_scoped_source_run

abbrev localsSourceLoweringStmtRunBridgeAtAtomicFromScopedSourceRun :=
  @Locals.SourceLowering.StmtRunBridgeAt.atomic_from_scoped_source_run

abbrev localsSourceLoweringStmtRunBridgeAtAtomicFromScopedSourceRunSourceBound :=
  @Locals.SourceLowering.StmtRunBridgeAt.atomic_from_scoped_source_run_source_bound

abbrev localsSourceLoweringStmtRunBridgeAtAtomicRegularHandlerScopesEq :=
  @Locals.SourceLowering.StmtRunBridgeAt.atomic_regular_handlerScopesEq

abbrev localsSourceLoweringStmtRunBridgeAtBlockFromOpenBridgeSourceRun :=
  @Locals.SourceLowering.StmtRunBridgeAt.block_from_open_bridge_source_run

abbrev localsSourceLoweringStmtRunBridgeAtIfFromScopedSourceRun :=
  @Locals.SourceLowering.StmtRunBridgeAt.if_from_scoped_source_run

abbrev localsSourceLoweringStmtRunBridgeAtIfFromScopedSourceRunSourceBound :=
  @Locals.SourceLowering.StmtRunBridgeAt.if_from_scoped_source_run_source_bound

abbrev localsSourceLoweringStmtRunBridgeAtSwitchFromScopedSourceRun :=
  @Locals.SourceLowering.StmtRunBridgeAt.switch_from_scoped_source_run

abbrev localsSourceLoweringStmtRunBridgeAtSwitchFromScopedSourceRunSourceBound :=
  @Locals.SourceLowering.StmtRunBridgeAt.switch_from_scoped_source_run_source_bound

abbrev localsSourceLoweringStmtRunBridgeTargetResultOfSource :=
  @Locals.SourceLowering.StmtRunBridge.target_result_of_source

abbrev localsSourceLoweringStmtRunBridgeExpr :=
  @Locals.SourceLowering.StmtRunBridge.expr

abbrev localsSourceLoweringStmtRunBridgeLetExpr :=
  @Locals.SourceLowering.StmtRunBridge.letExpr

abbrev localsSourceLoweringStmtRunBridgeAssignExpr :=
  @Locals.SourceLowering.StmtRunBridge.assign_expr

abbrev localsSourceLoweringStmtRunBridgeBreak :=
  @Locals.SourceLowering.StmtRunBridge.brk

abbrev localsSourceLoweringStmtRunBridgeContinue :=
  @Locals.SourceLowering.StmtRunBridge.cont

abbrev localsSourceLoweringStmtRunBridgeTerminal :=
  @Locals.SourceLowering.StmtRunBridge.terminal

abbrev localsSourceLoweringStmtRunBridgeTerminalArgs :=
  @Locals.SourceLowering.StmtRunBridge.terminalArgs

abbrev localsSourceLoweringStmtRunBridgeExprFromScoped :=
  @Locals.SourceLowering.StmtRunBridge.expr_from_scoped

abbrev localsSourceLoweringStmtRunBridgeLetExprFromScoped :=
  @Locals.SourceLowering.StmtRunBridge.letExpr_from_scoped

abbrev localsSourceLoweringStmtRunBridgeAssignExprFromScoped :=
  @Locals.SourceLowering.StmtRunBridge.assign_expr_from_scoped

abbrev localsSourceLoweringStmtRunBridgeTerminalArgsFromScoped :=
  @Locals.SourceLowering.StmtRunBridge.terminalArgs_from_scoped

abbrev localsSourceLoweringStmtRunBridgeExprFromScopedSourceRun :=
  @Locals.SourceLowering.StmtRunBridge.expr_from_scoped_source_run

abbrev localsSourceLoweringStmtRunBridgeLetExprFromScopedSourceRun :=
  @Locals.SourceLowering.StmtRunBridge.letExpr_from_scoped_source_run

abbrev localsSourceLoweringStmtRunBridgeAssignExprFromScopedSourceRun :=
  @Locals.SourceLowering.StmtRunBridge.assign_expr_from_scoped_source_run

abbrev localsSourceLoweringStmtRunBridgeBreakFromSourceRun :=
  @Locals.SourceLowering.StmtRunBridge.brk_from_source_run

abbrev localsSourceLoweringStmtRunBridgeContinueFromSourceRun :=
  @Locals.SourceLowering.StmtRunBridge.cont_from_source_run

abbrev localsSourceLoweringStmtRunBridgeTerminalFromSourceRun :=
  @Locals.SourceLowering.StmtRunBridge.terminal_from_source_run

abbrev localsSourceLoweringStmtRunBridgeTerminalArgsFromScopedSourceRun :=
  @Locals.SourceLowering.StmtRunBridge.terminalArgs_from_scoped_source_run

abbrev localsSourceLoweringStmtRunBridgeAtomicFromScopedSourceRun :=
  @Locals.SourceLowering.StmtRunBridge.atomic_from_scoped_source_run

abbrev localsSourceLoweringStmtRunBridgeAtomicFromScopedSourceRunSourceBound :=
  @Locals.SourceLowering.StmtRunBridge.atomic_from_scoped_source_run_source_bound

abbrev localsSourceLoweringStmtRunBridgeBlockFromOpenBridgeSourceRun :=
  @Locals.SourceLowering.StmtRunBridge.block_from_open_bridge_source_run

abbrev localsSourceLoweringStmtRunBridgeIfFromScopedSourceRun :=
  @Locals.SourceLowering.StmtRunBridge.if_from_scoped_source_run

abbrev localsSourceLoweringStmtRunBridgeIfFromScopedSourceRunSourceBound :=
  @Locals.SourceLowering.StmtRunBridge.if_from_scoped_source_run_source_bound

abbrev localsSourceLoweringStmtRunBridgeSwitchFromScopedSourceRun :=
  @Locals.SourceLowering.StmtRunBridge.switch_from_scoped_source_run

abbrev localsSourceLoweringStmtRunBridgeSwitchFromScopedSourceRunSourceBound :=
  @Locals.SourceLowering.StmtRunBridge.switch_from_scoped_source_run_source_bound

abbrev localsSourceLoweringBlockOpenRunBridge :=
  @Locals.SourceLowering.BlockOpenRunBridge

abbrev localsSourceLoweringBlockOpenRunBridgeAt :=
  @Locals.SourceLowering.BlockOpenRunBridgeAt

abbrev localsSourceLoweringBlockOpenRunBridgeAtToBlockOpenRunBridge :=
  @Locals.SourceLowering.BlockOpenRunBridgeAt.toBlockOpenRunBridge

abbrev localsSourceLoweringBlockOpenRunBridgeAtRebase :=
  @Locals.SourceLowering.BlockOpenRunBridgeAt.rebase

abbrev localsSourceLoweringBlockOpenRunBridgeAtTargetResultOfSource :=
  @Locals.SourceLowering.BlockOpenRunBridgeAt.target_result_of_source

abbrev localsSourceLoweringBlockOpenRunBridgeAtRunScopedFromOpenBridge :=
  @Locals.SourceLowering.BlockOpenRunBridgeAt.runScoped_from_open_bridge

abbrev localsSourceLoweringBlockOpenRunBridgeAtNil :=
  @Locals.SourceLowering.BlockOpenRunBridgeAt.nil

abbrev localsSourceLoweringBlockOpenRunBridgeAtConsFromStmtBridge :=
  @Locals.SourceLowering.BlockOpenRunBridgeAt.cons_from_stmt_bridge

abbrev localsSourceLoweringBlockOpenRunBridgeAtConsFromStmtSourceRun :=
  @Locals.SourceLowering.BlockOpenRunBridgeAt.cons_from_stmt_source_run

abbrev localsSourceLoweringBlockOpenRunBridgeAtConsFromAtomicSourceRun :=
  @Locals.SourceLowering.BlockOpenRunBridgeAt.cons_from_atomic_source_run

abbrev localsSourceLoweringBlockOpenRunBridgeAtConsFromAtomicSourceRunWithHandlers :=
  @Locals.SourceLowering.BlockOpenRunBridgeAt.cons_from_atomic_source_run_with_handlers

abbrev localsSourceLoweringBlockOpenRunBridgeAtConsFromAtomicSourceRunWithHandlersSourceBound :=
  @Locals.SourceLowering.BlockOpenRunBridgeAt.cons_from_atomic_source_run_with_handlers_source_bound

abbrev localsSourceLoweringStructuralBlockOpenRunBridgeAtOfSourceRun :=
  @Locals.SourceLowering.Structural.blockOpenRunBridgeAt_of_source_run

abbrev localsSourceLoweringStructuralStmtListOpenRunBridgeAtOfSourceRun :=
  @Locals.SourceLowering.Structural.stmtListOpenRunBridgeAt_of_source_run

abbrev localsSourceLoweringStructuralStmtRunBridgeAtOfSourceRun :=
  @Locals.SourceLowering.Structural.stmtRunBridgeAt_of_source_run

abbrev localsSourceLoweringStructuralRunForLoopBridgeAtOfSourceRun :=
  @Locals.SourceLowering.Structural.runForLoopBridgeAt_of_source_run

abbrev localsSourceLoweringStructuralRunForLoopBridgeAtOfSourceRunAux :=
  @Locals.SourceLowering.Structural.runForLoopBridgeAt_of_source_run_aux

abbrev localsSourceLoweringStructuralRunForLoopBridgeAtOfSourceRunFixedAux :=
  @Locals.SourceLowering.Structural.runForLoopBridgeAt_of_source_run_fixed_aux

abbrev localsSourceLoweringStructuralForStmtRunBridgeAtOfSourceRun :=
  @Locals.SourceLowering.Structural.forStmtRunBridgeAt_of_source_run

abbrev localsSourceLoweringBlockOpenRunBridgeTargetResultOfSource :=
  @Locals.SourceLowering.BlockOpenRunBridge.target_result_of_source

abbrev localsSourceLoweringBlockOpenRunBridgeRunScopedFromOpenBridge :=
  @Locals.SourceLowering.BlockOpenRunBridge.runScoped_from_open_bridge

abbrev localsSourceLoweringBlockOpenRunBridgeNil :=
  @Locals.SourceLowering.BlockOpenRunBridge.nil

abbrev localsSourceLoweringBlockOpenRunBridgeConsFromStmtBridge :=
  @Locals.SourceLowering.BlockOpenRunBridge.cons_from_stmt_bridge

abbrev localsSourceLoweringBlockOpenRunBridgeConsFromStmtSourceRun :=
  @Locals.SourceLowering.BlockOpenRunBridge.cons_from_stmt_source_run

abbrev localsSourceLoweringBlockOpenRunBridgeConsFromAtomicSourceRun :=
  @Locals.SourceLowering.BlockOpenRunBridge.cons_from_atomic_source_run

abbrev functionsSourceBlockRegularEqRestrict :=
  @Functions.Source.Block.runScoped_regular_eq_restrict

abbrev functionsSourceBlockRegularDropsNotMem :=
  @Functions.Source.Block.runScoped_regular_drops_not_mem

abbrev functionsSourceBlockRunOpenMono :=
  @Functions.Source.Block.runOpen_mono

abbrev functionsSourceBlockRunScopedMono :=
  @Functions.Source.Block.runScoped_mono

abbrev functionsSourceFunDefRunBodyMono :=
  @Functions.Source.FunDef.runBody_mono

abbrev functionsSourceStmtRunForLoopMono :=
  @Functions.Source.Stmt.runForLoop_mono

abbrev functionsSourceStmtRunMono :=
  @Functions.Source.Stmt.run_mono

abbrev functionsSourceBlockRunOpenAppendRegularExists :=
  @Functions.Source.Block.runOpen_append_regular_exists

abbrev functionsSourceBlockRunOpenAppendNonregularExists :=
  @Functions.Source.Block.runOpen_append_nonregular_exists

abbrev functionsScopeExprScopedCodeFalse :=
  @Functions.Scope.exprScoped_code_false

abbrev functionsSourceOwnedCaseList :=
  @Functions.SourceLowering.SourceToLocals.CaseList.SourceOwned

abbrev functionsSourceOwnedDefault :=
  @Functions.SourceLowering.SourceToLocals.Default.SourceOwned

abbrev functionsAtomicToLocalsSourceOwned :=
  @Functions.SourceLowering.SourceToLocals.atomic_toLocals_sourceOwned

abbrev functionsAtomicListToLocalsSourceOwned :=
  @Functions.SourceLowering.SourceToLocals.atomicList_toLocals_sourceOwned

abbrev functionsAtomicBlockToLocalsSourceOwned :=
  @Functions.SourceLowering.SourceToLocals.atomicBlock_toLocals_sourceOwned

abbrev functionsBlockStmtToLocalsSourceOwned :=
  @Functions.SourceLowering.SourceToLocals.blockStmt_toLocals_sourceOwned

abbrev functionsIfStmtToLocalsSourceOwned :=
  @Functions.SourceLowering.SourceToLocals.ifStmt_toLocals_sourceOwned

abbrev functionsCaseListToLocalsSourceOwned :=
  @Functions.SourceLowering.SourceToLocals.caseList_toLocals_sourceOwned

abbrev functionsDefaultToLocalsSourceOwned :=
  @Functions.SourceLowering.SourceToLocals.default_toLocals_sourceOwned

abbrev functionsSwitchStmtToLocalsSourceOwned :=
  @Functions.SourceLowering.SourceToLocals.switchStmt_toLocals_sourceOwned

abbrev functionsSwitchSelectToLocals :=
  @Functions.SourceLowering.SourceToLocals.switch_select_toLocals

abbrev functionsSwitchSelectSourceOwned :=
  @Functions.SourceLowering.SourceToLocals.switch_select_sourceOwned

abbrev functionsForStmtToLocalsSourceOwned :=
  @Functions.SourceLowering.SourceToLocals.forStmt_toLocals_sourceOwned

abbrev functionsSourceAfterStmtRun :=
  @Functions.SourceLowering.SourceToLocals.afterStmtRun

abbrev functionsSourceRunOpenSingleton :=
  @Functions.SourceLowering.SourceToLocals.runOpen_singleton_of_stmt_run

abbrev functionsAtomicRunOpenToLocals :=
  @Functions.SourceLowering.SourceToLocals.atomic_runOpen_toLocals_of_run

abbrev functionsAtomicListRunOpenToLocals :=
  @Functions.SourceLowering.SourceToLocals.atomicList_runOpen_toLocals_of_run

abbrev functionsAtomicBlockRunOpenToLocals :=
  @Functions.SourceLowering.SourceToLocals.atomicBlock_runOpen_toLocals_of_run

abbrev functionsAtomicBlockRunScopedToLocals :=
  @Functions.SourceLowering.SourceToLocals.atomicBlock_runScoped_toLocals_of_run

abbrev functionsBlockStmtToLocals :=
  @Functions.SourceLowering.SourceToLocals.blockStmt_toLocals_of_run

abbrev functionsIfStmtToLocals :=
  @Functions.SourceLowering.SourceToLocals.ifStmt_toLocals_of_run

abbrev functionsRunForLoopToLocals :=
  @Functions.SourceLowering.SourceToLocals.runForLoop_toLocals_of_run

abbrev functionsForStmtToLocals :=
  @Functions.SourceLowering.SourceToLocals.forStmt_toLocals_of_run

abbrev functionsSwitchStmtToLocals :=
  @Functions.SourceLowering.SourceToLocals.switchStmt_toLocals_of_run

abbrev functionsSourceExprStmtToLocals :=
  @Functions.SourceLowering.Stmt.expr_toLocals_of_run

abbrev functionsSourceLetToLocals :=
  @Functions.SourceLowering.Stmt.let_toLocals_of_run

abbrev functionsSourceAssignToLocals :=
  @Functions.SourceLowering.Stmt.assign_toLocals_of_run

abbrev functionsSourceBreakToLocals :=
  @Functions.SourceLowering.Stmt.brk_toLocals_of_run

abbrev functionsSourceContinueToLocals :=
  @Functions.SourceLowering.Stmt.cont_toLocals_of_run

abbrev functionsSourceLeaveToLocals :=
  @Functions.SourceLowering.Stmt.leave_toLocals_of_run

abbrev functionsSourceTerminalToLocals :=
  @Functions.SourceLowering.Stmt.terminal_toLocals_of_run

abbrev functionsSourceTerminalArgsToLocals :=
  @Functions.SourceLowering.Stmt.terminalArgs_toLocals_of_run

abbrev functionsSourceArgListEvalLength :=
  @Functions.Source.ArgList.eval_length

abbrev functionsSourceStoreInsertManyLength :=
  @Functions.Source.Store.insertMany_length

abbrev functionsSourceStoreLookupManyLength :=
  @Functions.Source.Store.lookupMany_length

abbrev functionsSourceStoreLookupManyRestrictToOfMem :=
  @Functions.Source.Store.lookupMany_restrictTo_of_mem

abbrev functionsSourceStoreAssignManyLength :=
  @Functions.Source.Store.assignMany_length

abbrev functionsSourceStoreAssignManyAppend :=
  @Functions.Source.Store.assignMany_append

abbrev functionsSourceStoreAssignManyPreservesContainsOfNotMem :=
  @Functions.Source.Store.assignMany_preserves_contains_of_not_mem

abbrev functionsSourceStoreAssignManySnocOfRun :=
  @Functions.Source.Store.assignMany_snoc_of_run

abbrev functionsSourceStoreInsertCommOfNe :=
  @Functions.Source.Store.insert_comm_of_ne

abbrev functionsSourceStoreAssignManyCommuteInsertOfNotMem :=
  @Functions.Source.Store.assignMany_commute_insert_of_not_mem

abbrev functionsSourceStoreAssignManyRemoveInsertOfNotMem :=
  @Functions.Source.Store.assignMany_remove_insert_of_not_mem

abbrev functionsSourceStoreAssignManyReverseOfRun :=
  @Functions.Source.Store.assignMany_reverse_of_run

abbrev functionsFunDefSignatureNodup :=
  @Functions.FunDef.signatureNodup

abbrev functionsFunDefBodyScoped :=
  @Functions.FunDef.bodyScoped

abbrev functionsSourceFunDefBodyCtx :=
  @Functions.Source.FunDef.bodyCtx

abbrev functionsSourceFunDefRunBodyReturnedParts :=
  @Functions.Source.FunDef.runBody_returned_parts

abbrev functionsSourceFunDefRunBodyHaltedParts :=
  @Functions.Source.FunDef.runBody_halted_parts

abbrev functionsSourceFunDefRunBodyArgsLength :=
  @Functions.Source.FunDef.runBody_args_length

abbrev functionsSourceFunDefRunBodyReturnedLength :=
  @Functions.Source.FunDef.runBody_returned_length

abbrev functionsSourceStmtCallRegularTargetsNodup :=
  @Functions.Source.Stmt.call_regular_targets_nodup

abbrev functionsSourceStmtCallRegularArgsLength :=
  @Functions.Source.Stmt.call_regular_args_length

abbrev functionsSourceStmtCallRegularTargetsLength :=
  @Functions.Source.Stmt.call_regular_targets_length

abbrev functionsSourceStmtCallRegularArities :=
  @Functions.Source.Stmt.call_regular_arities

abbrev functionsSourceStmtCallHaltTargetsNodup :=
  @Functions.Source.Stmt.call_halt_targets_nodup

abbrev functionsSourceStmtCallHaltArgsLength :=
  @Functions.Source.Stmt.call_halt_args_length

abbrev functionsSourceDirectExprSeqEvalMpr :=
  @Functions.SourceDirect.ExprSeq.eval_mpr

abbrev functionsSourceDirectExprSeqVarSlotValuesAtMpr :=
  @Functions.SourceDirect.ExprSeq.varSlotValuesAt_mpr

abbrev functionsSourceDirectExprSeqVarSlotValuesAtMp :=
  @Functions.SourceDirect.ExprSeq.varSlotValuesAt_mp

abbrev functionsSourceDirectExprEvalOfEvalOne :=
  @Functions.SourceDirect.Expr.eval_of_evalOne

abbrev functionsSourceDirectSourceScopeExprScopedSourceOwned :=
  @Functions.SourceDirect.SourceScope.exprScoped_sourceOwned

abbrev functionsSourceDirectSourceScopeExprSeqScopedSourceOwned :=
  @Functions.SourceDirect.SourceScope.exprSeqScoped_sourceOwned

abbrev functionsSourceDirectSourceScopeStmtOutEnvNodup :=
  @Functions.SourceDirect.SourceScope.stmt_outEnv_nodup

abbrev functionsSourceDirectSourceScopeBlockOutEnvNodup :=
  @Functions.SourceDirect.SourceScope.block_outEnv_nodup

abbrev functionsSourceDirectSourceScopeStmtListOutEnvNodup :=
  @Functions.SourceDirect.SourceScope.stmtList_outEnv_nodup

abbrev functionsSourceDirectSourceScopeStmtOutEnvContainsOfContains :=
  @Functions.SourceDirect.SourceScope.stmt_outEnv_contains_of_contains

abbrev functionsSourceDirectSourceScopeBlockOutEnvContainsOfContains :=
  @Functions.SourceDirect.SourceScope.block_outEnv_contains_of_contains

abbrev functionsSourceDirectSourceScopeStmtListOutEnvContainsOfContains :=
  @Functions.SourceDirect.SourceScope.stmtList_outEnv_contains_of_contains

abbrev functionsSourceDirectSourceScopeSwitchSelectBlockScoped :=
  @Functions.SourceDirect.SourceScope.switch_select_block_scoped

abbrev functionsSourceDirectArgListEvalArgExprs :=
  @Functions.SourceDirect.ArgList.eval_argExprs

abbrev functionsSourceDirectArgListArgExprsSourceOwned :=
  @Functions.SourceDirect.ArgList.argExprs_sourceOwned

abbrev functionsSourceDirectArgListArgExprsSourceOwnedOfScoped :=
  @Functions.SourceDirect.ArgList.argExprs_sourceOwned_of_scoped

abbrev functionsSourceDirectArgListArgExprsScopedOfScoped :=
  @Functions.SourceDirect.ArgList.argExprs_scoped_of_scoped

abbrev functionsSourceDirectArgListEvalArgsOfEvalSourceOwned :=
  @Functions.SourceDirect.ArgList.evalArgs_of_eval_sourceOwned

abbrev functionsSourceDirectArgListEvalArgsCallerStateRelOfEvalSourceOwned :=
  @Functions.SourceDirect.ArgList.evalArgs_callerStateRel_of_eval_sourceOwned

abbrev functionsSourceDirectCallPrelude :=
  @Functions.SourceDirect.CallPrelude

abbrev functionsSourceDirectCallPreludeExistsOfEvalSourceOwned :=
  @Functions.SourceDirect.CallPrelude.exists_of_eval_sourceOwned

abbrev functionsSourceDirectCallPreludeExistsOfEvalScoped :=
  @Functions.SourceDirect.CallPrelude.exists_of_eval_scoped

abbrev functionsSourceDirectCallPreludeExistsOfEvalStmtScoped :=
  @Functions.SourceDirect.CallPrelude.exists_of_eval_stmt_scoped

abbrev functionsSourceDirectCallPreludePrepareCallFrame :=
  @Functions.SourceDirect.CallPrelude.prepareCallFrame

abbrev functionsSourceDirectFunListSourceFindEq :=
  @Functions.SourceDirect.FunList.source_find?_eq

abbrev functionsSourceDirectFunListScopedOfFind :=
  @Functions.SourceDirect.FunList.scoped_of_find?

abbrev functionsSourceDirectFunListSourceScopedOfFind :=
  @Functions.SourceDirect.FunList.source_scoped_of_find?

abbrev functionsSourceDirectFunListSourceOwnedOfFind :=
  @Functions.SourceDirect.FunList.sourceOwned_of_find?

abbrev functionsSourceDirectFunListSourceSourceOwnedOfFind :=
  @Functions.SourceDirect.FunList.source_sourceOwned_of_find?

abbrev functionsSourceDirectSourceRunStmtRegularScope :=
  @Functions.SourceDirect.SourceRun.stmt_regular_scope

abbrev functionsSourceDirectSourceRunForStmtNotBreakContinue :=
  @Functions.SourceDirect.SourceRun.for_stmt_not_break_continue

abbrev functionsSourceDirectSourceRunCallStmtNotBreakContinue :=
  @Functions.SourceDirect.SourceRun.call_stmt_not_break_continue

abbrev functionsSourceDirectSourceRunStmtRegularLeaveScope :=
  @Functions.SourceDirect.SourceRun.stmt_regular_leaveScope

abbrev functionsSourceDirectSourceRunStmtRegularBreakScope :=
  @Functions.SourceDirect.SourceRun.stmt_regular_breakScope

abbrev functionsSourceDirectSourceRunStmtRegularContinueScope :=
  @Functions.SourceDirect.SourceRun.stmt_regular_continueScope

abbrev functionsSourceDirectSourceRunStmtRegularScopeNodup :=
  @Functions.SourceDirect.SourceRun.stmt_regular_scope_nodup

abbrev functionsSourceDirectSourceRunStmtRegularReturnScope :=
  @Functions.SourceDirect.SourceRun.stmt_regular_returnScope

abbrev functionsSourceDirectSourceRunStmtRegularReturnsInScope :=
  @Functions.SourceDirect.SourceRun.stmt_regular_returns_in_scope

abbrev functionsSourceDirectSourceRunBlockRunOpenRegularScope :=
  @Functions.SourceDirect.SourceRun.block_runOpen_regular_scope

abbrev functionsSourceDirectSourceRunBlockRunOpenRegularLeaveScope :=
  @Functions.SourceDirect.SourceRun.block_runOpen_regular_leaveScope

abbrev functionsSourceDirectSourceRunBlockRunOpenRegularBreakScope :=
  @Functions.SourceDirect.SourceRun.block_runOpen_regular_breakScope

abbrev functionsSourceDirectSourceRunBlockRunOpenRegularContinueScope :=
  @Functions.SourceDirect.SourceRun.block_runOpen_regular_continueScope

abbrev functionsSourceDirectSourceRunBlockRunOpenRegularReturnScope :=
  @Functions.SourceDirect.SourceRun.block_runOpen_regular_returnScope

abbrev functionsSourceDirectSourceRunBlockRunOpenRegularReturnsInScope :=
  @Functions.SourceDirect.SourceRun.block_runOpen_regular_returns_in_scope

abbrev functionsSourceDirectSourceRunBlockRunOpenNotBreakContinueOfNoLoopControl :=
  @Functions.SourceDirect.SourceRun.block_runOpen_not_break_continue_of_no_loop_control

abbrev functionsSourceDirectSourceRunBlockRunScopedNotBreakContinueOfNoLoopControl :=
  @Functions.SourceDirect.SourceRun.block_runScoped_not_break_continue_of_no_loop_control

abbrev functionsSourceDirectSourceRunBlockRunScopedOpenExists :=
  @Functions.SourceDirect.SourceRun.block_runScoped_open_exists

abbrev functionsSourceDirectSameScope :=
  @Functions.SourceDirect.SameScope

abbrev functionsSourceDirectSameScopeSymm :=
  @Functions.SourceDirect.SameScope.symm

abbrev functionsSourceDirectSameScopeNodupLeft :=
  @Functions.SourceDirect.SameScope.nodup_left

abbrev functionsSourceDirectSameScopeNodupRight :=
  @Functions.SourceDirect.SameScope.nodup_right

abbrev functionsSourceDirectCleanupScopeRel :=
  @Functions.SourceDirect.CleanupScopeRel

abbrev functionsSourceDirectCleanupLayoutRel :=
  @Functions.SourceDirect.CleanupLayoutRel

abbrev functionsSourceDirectCleanupLayoutRelRefl :=
  @Functions.SourceDirect.CleanupLayoutRel.refl

abbrev functionsSourceDirectCleanupLayoutRelCons :=
  @Functions.SourceDirect.CleanupLayoutRel.cons

abbrev functionsSourceDirectCleanupLayoutRelTrans :=
  @Functions.SourceDirect.CleanupLayoutRel.trans

abbrev functionsSourceDirectCleanupLayoutRelToCleanupScope :=
  @Functions.SourceDirect.CleanupLayoutRel.to_cleanupScope

abbrev functionsSourceDirectStackStoreRelInsertManyReversePrefix :=
  @Functions.SourceDirect.StackStoreRel.insertMany_reverse_prefix

abbrev functionsSourceDirectStackStoreRelInsertManyReverseEmpty :=
  @Functions.SourceDirect.StackStoreRel.insertMany_reverse_empty

abbrev functionsSourceDirectCtxRel :=
  @Functions.SourceDirect.CtxRel

abbrev functionsSourceDirectCtxRelAssignmentTargets :=
  @Functions.SourceDirect.CtxRel.assignmentTargets

abbrev functionsSourceDirectCtxRelLookupOfSourceMem :=
  @Functions.SourceDirect.CtxRel.lookup_of_source_mem

abbrev functionsSourceDirectCtxRelLayoutNodup :=
  @Functions.SourceDirect.CtxRel.layout_nodup

abbrev functionsSourceDirectAccessExprWidth :=
  @Functions.SourceDirect.Access.exprWidth

abbrev functionsSourceDirectAccessExprSeqWidth :=
  @Functions.SourceDirect.Access.exprSeqWidth

abbrev functionsSourceDirectFrameBoundBlock :=
  @Functions.SourceDirect.FrameBound.Block

abbrev functionsSourceDirectFrameBoundStmt :=
  @Functions.SourceDirect.FrameBound.Stmt

abbrev functionsSourceDirectFrameBoundStmtList :=
  @Functions.SourceDirect.FrameBound.StmtList

abbrev functionsSourceDirectFrameBoundCaseList :=
  @Functions.SourceDirect.FrameBound.CaseList

abbrev functionsSourceDirectFrameBoundDefault :=
  @Functions.SourceDirect.FrameBound.Default

abbrev functionsSourceDirectFrameBoundFunDef :=
  @Functions.SourceDirect.FrameBound.FunDef

abbrev functionsSourceDirectFrameBoundFunList :=
  @Functions.SourceDirect.FrameBound.FunList

abbrev functionsSourceDirectFrameBoundProgram :=
  @Functions.SourceDirect.FrameBound.Program

abbrev functionsSourceDirectFrameBoundFunDefBody :=
  @Functions.SourceDirect.FrameBound.funDef_body

abbrev functionsSourceDirectFrameBoundFunDefRegularReturnBound :=
  @Functions.SourceDirect.FrameBound.funDef_regularReturnBound

abbrev functionsSourceDirectFrameBoundStmtListHead :=
  @Functions.SourceDirect.FrameBound.stmtList_head

abbrev functionsSourceDirectFrameBoundStmtListTail :=
  @Functions.SourceDirect.FrameBound.stmtList_tail

abbrev functionsSourceDirectFrameBoundSwitchSelectBlock :=
  @Functions.SourceDirect.FrameBound.switch_select_block

abbrev functionsSourceDirectFrameBoundFunDefOfFind :=
  @Functions.SourceDirect.FrameBound.funDef_of_find?

abbrev functionsSourceDirectFrameBoundSourceFunDefOfFind :=
  @Functions.SourceDirect.FrameBound.source_funDef_of_find?

abbrev functionsSourceDirectFrameBoundAccessOfCtxRel :=
  @Functions.SourceDirect.FrameBound.access_of_ctxRel

abbrev functionsSourceDirectFrameBoundCallArgAccessOfCtxRel :=
  @Functions.SourceDirect.FrameBound.call_argAccess_of_ctxRel

abbrev functionsSourceDirectFrameBoundCallAssignBoundOfCtxRel :=
  @Functions.SourceDirect.FrameBound.call_assignBound_of_ctxRel

abbrev functionsSourceDirectCtxRelExprAccessibleOfScoped :=
  @Functions.SourceDirect.CtxRel.expr_accessible_of_scoped

abbrev functionsSourceDirectCtxRelExprSeqAccessibleOfScoped :=
  @Functions.SourceDirect.CtxRel.exprSeq_accessible_of_scoped

abbrev functionsSourceDirectFunctionBodyCtxRel :=
  @Functions.SourceDirect.FunDef.bodyCtxRel

abbrev functionsSourceDirectFunctionTargetBodyCtxLayoutNodup :=
  @Functions.SourceDirect.FunDef.targetBodyCtx_layout_nodup

abbrev functionsSourceDirectStateRel :=
  @Functions.SourceDirect.StateRel

abbrev functionsSourceDirectStateRelCleanupToLayout :=
  @Functions.SourceDirect.StateRel.cleanupTo_layout

abbrev functionsSourceDirectStateRelRestrictToSameScope :=
  @Functions.SourceDirect.StateRel.restrictTo_sameScope

abbrev functionsSourceDirectStateRelWithShared :=
  @Functions.SourceDirect.StateRel.withShared

abbrev functionsSourceDirectPrefixedStateRel :=
  @Functions.SourceDirect.PrefixedStateRel

abbrev functionsSourceDirectPrefixedStateRelOfStateRelStackPrefix :=
  @Functions.SourceDirect.PrefixedStateRel.of_stateRel_stack_prefix

abbrev functionsSourceDirectPrefixedCallerStateRelWithShared :=
  @Functions.SourceDirect.PrefixedStateRel.callerStateRel_withShared

abbrev functionsSourceDirectInitialStateRel :=
  @Functions.SourceDirect.StateRel.initial

abbrev functionsSourceDirectOutcomeRel :=
  @Functions.SourceDirect.OutcomeRel

abbrev functionsSourceDirectStmtOutcomeRel :=
  @Functions.SourceDirect.StmtOutcomeRel

abbrev functionsSourceDirectStmtOutcomeRelLeaveOfReturnValuesRelRestrict :=
  @Functions.SourceDirect.StmtOutcomeRel.leave_of_returnValuesRel_restrict

abbrev functionsSourceDirectStmtOutcomeRelStateRelOfRegularOrCont :=
  @Functions.SourceDirect.StmtOutcomeRel.stateRel_of_regular_or_cont

abbrev functionsSourceDirectBlockSourceOwned :=
  @Functions.SourceDirect.Block.SourceOwned

abbrev functionsSourceDirectStmtSourceOwned :=
  @Functions.SourceDirect.Stmt.SourceOwned

abbrev functionsSourceDirectFunDefSourceOwned :=
  @Functions.SourceDirect.FunDef.SourceOwned

abbrev functionsSourceDirectProgramSourceOwned :=
  @Functions.SourceDirect.Program.SourceOwned

abbrev functionsSourceDirectSourceOwnedProgramOfScoped :=
  @Functions.SourceDirect.SourceOwned.program_of_scoped

abbrev functionsSourceDirectStmtRunResultRel :=
  @Functions.SourceDirect.StmtRunResultRel

abbrev functionsSourceDirectStmtRunResultRelRegular :=
  @Functions.SourceDirect.StmtRunResultRel.regular

abbrev functionsSourceDirectStmtRunResultRelToBlockOpenResultRel :=
  @Functions.SourceDirect.StmtRunResultRel.to_blockOpenResultRel

abbrev functionsSourceDirectStmtRunResultRelRegularStateRel :=
  @Functions.SourceDirect.StmtRunResultRel.regular_stateRel

abbrev functionsSourceDirectStmtRunResultRelOutcomeRelOfNonregular :=
  @Functions.SourceDirect.StmtRunResultRel.outcomeRel_of_nonregular

abbrev functionsSourceDirectBlockOpenResultRel :=
  @Functions.SourceDirect.BlockOpenResultRel

abbrev functionsSourceDirectBlockOpenResultRelRegular :=
  @Functions.SourceDirect.BlockOpenResultRel.regular

abbrev functionsSourceDirectBlockOpenResultRelOutcomeRelOfNonregular :=
  @Functions.SourceDirect.BlockOpenResultRel.outcomeRel_of_nonregular

abbrev functionsSourceDirectStmtRunBridge :=
  @Functions.SourceDirect.StmtRunBridge

abbrev functionsSourceDirectStmtRunBridgeOfParts :=
  @Functions.SourceDirect.StmtRunBridge.of_parts

abbrev functionsSourceDirectStmtRunBridgeWithLayout :=
  @Functions.SourceDirect.StmtRunBridgeWithLayout

abbrev functionsSourceDirectStmtRunBridgeWithLayoutToBridge :=
  @Functions.SourceDirect.StmtRunBridgeWithLayout.to_bridge

abbrev functionsSourceDirectStmtRunBridgeWithLayoutRegularLayout :=
  @Functions.SourceDirect.StmtRunBridgeWithLayout.regular_layout

abbrev functionsSourceDirectStmtRunBridgeWithLayoutTargetResultOfSource :=
  @Functions.SourceDirect.StmtRunBridgeWithLayout.target_result_of_source

abbrev functionsSourceDirectStmtRunBridgeWithLayoutOfBridgeAndLayout :=
  @Functions.SourceDirect.StmtRunBridgeWithLayout.of_bridge_and_layout

abbrev functionsSourceDirectStmtRunBridgeWithLayoutOfBridgeAndRegularTargetLayout :=
  @Functions.SourceDirect.StmtRunBridgeWithLayout.of_bridge_and_regular_target_layout

abbrev functionsSourceDirectStmtRunBridgeWithLayoutOfBridgeAndNeverRegularSource :=
  @Functions.SourceDirect.StmtRunBridgeWithLayout.of_bridge_and_never_regular_source

abbrev functionsSourceDirectStmtRunBridgeWithLayoutOfPartsRegularTargetCleanup :=
  @Functions.SourceDirect.StmtRunBridgeWithLayout.of_parts_regular_target_cleanup

abbrev functionsSourceDirectStmtRunBridgeWithLayoutOfPartsNeverRegularSource :=
  @Functions.SourceDirect.StmtRunBridgeWithLayout.of_parts_never_regular_source

abbrev functionsSourceDirectBlockOpenRunBridge :=
  @Functions.SourceDirect.BlockOpenRunBridge

abbrev functionsSourceDirectBlockOpenRunBridgeOfParts :=
  @Functions.SourceDirect.BlockOpenRunBridge.of_parts

abbrev functionsSourceDirectBlockOpenRunBridgeNilFromRel :=
  @Functions.SourceDirect.BlockOpenRunBridge.nil_from_rel

abbrev functionsSourceDirectBlockOpenRunBridgeWithLayout :=
  @Functions.SourceDirect.BlockOpenRunBridgeWithLayout

abbrev functionsSourceDirectBlockOpenRunBridgeWithLayoutToBridge :=
  @Functions.SourceDirect.BlockOpenRunBridgeWithLayout.to_bridge

abbrev functionsSourceDirectBlockOpenRunBridgeWithLayoutRegularLayout :=
  @Functions.SourceDirect.BlockOpenRunBridgeWithLayout.regular_layout

abbrev functionsSourceDirectBlockOpenRunBridgeWithLayoutTargetResultOfSource :=
  @Functions.SourceDirect.BlockOpenRunBridgeWithLayout.target_result_of_source

abbrev functionsSourceDirectBlockOpenRunBridgeWithLayoutOfBridgeAndLayout :=
  @Functions.SourceDirect.BlockOpenRunBridgeWithLayout.of_bridge_and_layout

abbrev functionsSourceDirectBlockOpenRunBridgeWithLayoutNilFromRel :=
  @Functions.SourceDirect.BlockOpenRunBridgeWithLayout.nil_from_rel

abbrev functionsSourceDirectExprLitBridge :=
  @Functions.SourceDirect.Expr.lit_bridge

abbrev functionsSourceDirectExprVarBridge :=
  @Functions.SourceDirect.Expr.var_bridge

abbrev functionsSourceDirectExprEvalBridgeSourceOwned :=
  @Functions.SourceDirect.Expr.eval_bridge_sourceOwned

abbrev functionsSourceDirectExprEvalOneBridgeSourceOwned :=
  @Functions.SourceDirect.Expr.evalOne_bridge_sourceOwned

abbrev functionsSourceDirectExprResultRelOfStateRelStackPrefix :=
  @Functions.SourceDirect.ExprResultRel.of_stateRel_stack_prefix

abbrev functionsSourceDirectExprResultRelToStateRelNil :=
  @Functions.SourceDirect.ExprResultRel.to_stateRel_nil

abbrev functionsSourceDirectReturnValuesRel :=
  @Functions.SourceDirect.ReturnValuesRel

abbrev functionsSourceDirectReturnValuesAccessible :=
  @Functions.SourceDirect.ReturnValuesRel.Accessible

abbrev functionsSourceDirectReturnValuesAccessibleOfCtxRel :=
  @Functions.SourceDirect.ReturnValuesRel.accessible_of_ctxRel

abbrev functionsSourceDirectReturnValuesSafeOfCtxRel :=
  @Functions.SourceDirect.ReturnValuesRel.safe_of_ctxRel

abbrev functionsSourceDirectReturnValuesLookupManyExistsOfAccessible :=
  @Functions.SourceDirect.ReturnValuesRel.lookupMany_exists_of_accessible

abbrev functionsSourceDirectFrameBoundLeaveAccessible :=
  @Functions.SourceDirect.FrameBound.leave_accessible

abbrev functionsSourceDirectFrameBoundFunDefRegularReturnSafe :=
  @Functions.SourceDirect.FrameBound.funDef_regular_return_safe

abbrev functionsSourceDirectSourceInvariantStmt :=
  @Functions.SourceDirect.SourceInvariant.Stmt

abbrev functionsSourceDirectSourceInvariantBlock :=
  @Functions.SourceDirect.SourceInvariant.Block

abbrev functionsSourceDirectSourceInvariantStmtTargetLayoutNodup :=
  @Functions.SourceDirect.SourceInvariant.Stmt.targetLayoutNodup

abbrev functionsSourceDirectSourceInvariantStmtForPostOfRegularInit :=
  @Functions.SourceDirect.SourceInvariant.Stmt.for_post_of_regular_init

abbrev functionsSourceDirectSourceInvariantStmtForBodyOfRegularInit :=
  @Functions.SourceDirect.SourceInvariant.Stmt.for_body_of_regular_init

abbrev functionsSourceDirectSourceInvariantBlockHead :=
  @Functions.SourceDirect.SourceInvariant.Block.head

abbrev functionsSourceDirectSourceInvariantBlockTailOfRegular :=
  @Functions.SourceDirect.SourceInvariant.Block.tail_of_regular

abbrev functionsSourceDirectSourceInvariantFunDefBody :=
  @Functions.SourceDirect.SourceInvariant.FunDef.body

abbrev functionsSourceDirectSourceInvariantFunDefBodyOfFind :=
  @Functions.SourceDirect.SourceInvariant.FunDef.body_of_find?

abbrev functionsSourceDirectSourceInvariantProgramBody :=
  @Functions.SourceDirect.SourceInvariant.Program.body

abbrev functionsSourceDirectReturnValuesVarSlotValuesAtReturnExprsOfLookupManyAccessible :=
  @Functions.SourceDirect.ReturnValuesRel.varSlotValuesAt_returnExprs_of_lookupMany_accessible

abbrev functionsSourceDirectReturnValuesOfStateRelLookupManyAccessible :=
  @Functions.SourceDirect.ReturnValuesRel.of_stateRel_lookupMany_accessible

abbrev functionsSourceDirectReturnValuesExistsOfStateRelAccessible :=
  @Functions.SourceDirect.ReturnValuesRel.exists_of_stateRel_accessible

abbrev functionsSourceDirectReturnValuesPush :=
  @Functions.SourceDirect.ReturnValuesRel.pushReturns

abbrev functionsSourceDirectReturnValuesPushCleanupReturnedStack :=
  @Functions.SourceDirect.ReturnValuesRel.pushCleanup_returnedStack

abbrev functionsSourceDirectReturnedStackRel :=
  @Functions.SourceDirect.ReturnedStackRel

abbrev functionsSourceDirectReturnedStackRelPopReturnAttach :=
  @Functions.SourceDirect.ReturnedStackRel.popReturn_attach

abbrev functionsSourceDirectCleanupManyPreservingExists :=
  @Functions.SourceDirect.Cleanup.cleanupManyPreserving_exists

abbrev functionsSourceDirectRunCleanupToPreservingExists :=
  @Functions.SourceDirect.Cleanup.runCleanupToPreserving_exists

abbrev functionsSourceDirectRunCleanupAllExists :=
  @Functions.SourceDirect.Cleanup.runCleanupAll_exists

abbrev functionsSourceDirectStmtLetLitBridge :=
  @Functions.SourceDirect.Stmt.let_lit_bridge

abbrev functionsSourceDirectStmtExprBridge :=
  @Functions.SourceDirect.Stmt.expr_bridge

abbrev functionsSourceDirectStmtExprStmtOutcomeBridge :=
  @Functions.SourceDirect.Stmt.expr_stmtOutcome_bridge

abbrev functionsSourceDirectStmtLetVarBridge :=
  @Functions.SourceDirect.Stmt.let_var_bridge

abbrev functionsSourceDirectStmtLetExprBridge :=
  @Functions.SourceDirect.Stmt.let_expr_bridge

abbrev functionsSourceDirectStmtLetExprStmtOutcomeBridge :=
  @Functions.SourceDirect.Stmt.let_expr_stmtOutcome_bridge

abbrev functionsSourceDirectStmtAssignLitBridge :=
  @Functions.SourceDirect.Stmt.assign_lit_bridge

abbrev functionsSourceDirectStmtAssignVarBridge :=
  @Functions.SourceDirect.Stmt.assign_var_bridge

abbrev functionsSourceDirectStmtAssignExprBridge :=
  @Functions.SourceDirect.Stmt.assign_expr_bridge

abbrev functionsSourceDirectStmtAssignExprStmtOutcomeBridge :=
  @Functions.SourceDirect.Stmt.assign_expr_stmtOutcome_bridge

abbrev functionsSourceDirectAssignTopStateRelOfStackPrefix :=
  @Functions.SourceDirect.Assignment.assignTop_stateRel_of_stack_prefix

abbrev functionsSourceDirectAssignTopWithOffsetPrefixed :=
  @Functions.SourceDirect.Assignment.assignTopWithOffset_prefixed

abbrev functionsSourceDirectAssignReturnedTopsDirectOrder :=
  @Functions.SourceDirect.Assignment.assignReturnedTops_direct_order

abbrev functionsSourceDirectAssignReturnedTopsSourceOrder :=
  @Functions.SourceDirect.Assignment.assignReturnedTops_source_order

abbrev functionsSourceDirectAssignReturnedTopsSourceOrderOfStateRelStackPrefix :=
  @Functions.SourceDirect.Assignment.assignReturnedTops_source_order_of_stateRel_stack_prefix

abbrev functionsSourceDirectAssignReturnedTopsSourceOrderOfCtxRelStackPrefix :=
  @Functions.SourceDirect.Assignment.assignReturnedTops_source_order_of_ctxRel_stack_prefix

abbrev functionsSourceDirectFinishReturnedCallStateRel :=
  @Functions.SourceDirect.Assignment.finishReturnedCall_stateRel

abbrev functionsSourceDirectInitReturnsStateRel :=
  @Functions.SourceDirect.InitReturns.stateRel

abbrev functionsSourceDirectFunDefInitCallFrameStateRel :=
  @Functions.SourceDirect.FunDef.initCallFrame_stateRel

abbrev functionsSourceDirectFunDefPrepareCallFrameStateRel :=
  @Functions.SourceDirect.FunDef.prepareCallFrame_stateRel

abbrev functionsSourceDirectFunDefRunBodyRegularFromBody :=
  @Functions.SourceDirect.FunDef.runBody_regular_from_body

abbrev functionsSourceDirectFunDefRunBodyLeaveFromBody :=
  @Functions.SourceDirect.FunDef.runBody_leave_from_body

abbrev functionsSourceDirectFunDefRunBodyHaltFromBody :=
  @Functions.SourceDirect.FunDef.runBody_halt_from_body

abbrev functionsSourceDirectFunDefRunBodyReturnedFromOpenBridgeWithLayout :=
  @Functions.SourceDirect.FunDef.runBody_returned_from_open_bridge_with_layout

abbrev functionsSourceDirectFunDefRunBodyHaltedFromOpenBridgeWithLayout :=
  @Functions.SourceDirect.FunDef.runBody_halted_from_open_bridge_with_layout

abbrev functionsSourceDirectFunDefReturnedRunBodyFromBodyBridgeWithLayout :=
  @Functions.SourceDirect.FunDef.returned_runBody_from_body_bridge_with_layout

abbrev functionsSourceDirectFunDefHaltedRunBodyFromBodyBridgeWithLayout :=
  @Functions.SourceDirect.FunDef.halted_runBody_from_body_bridge_with_layout

abbrev functionsSourceDirectFunDefReturnedRunBodyFromProgramBodyBridgeWithLayout :=
  @Functions.SourceDirect.FunDef.returned_runBody_from_program_body_bridge_with_layout

abbrev functionsSourceDirectFunDefHaltedRunBodyFromProgramBodyBridgeWithLayout :=
  @Functions.SourceDirect.FunDef.halted_runBody_from_program_body_bridge_with_layout

abbrev functionsSourceDirectStmtBreakBridge :=
  @Functions.SourceDirect.Stmt.brk_bridge

abbrev functionsSourceDirectStmtBreakStmtOutcomeBridge :=
  @Functions.SourceDirect.Stmt.brk_stmtOutcome_bridge

abbrev functionsSourceDirectStmtBreakStmtOutcomeBridgeCurrentScope :=
  @Functions.SourceDirect.Stmt.brk_stmtOutcome_bridge_current_scope

abbrev functionsSourceDirectStmtBreakStmtRunResultBridgeCurrentScope :=
  @Functions.SourceDirect.Stmt.brk_stmtRunResult_bridge_current_scope

abbrev functionsSourceDirectStmtContinueBridge :=
  @Functions.SourceDirect.Stmt.cont_bridge

abbrev functionsSourceDirectStmtContinueStmtOutcomeBridge :=
  @Functions.SourceDirect.Stmt.cont_stmtOutcome_bridge

abbrev functionsSourceDirectStmtContinueStmtOutcomeBridgeCurrentScope :=
  @Functions.SourceDirect.Stmt.cont_stmtOutcome_bridge_current_scope

abbrev functionsSourceDirectStmtContinueStmtRunResultBridgeCurrentScope :=
  @Functions.SourceDirect.Stmt.cont_stmtRunResult_bridge_current_scope

abbrev functionsSourceDirectStmtLeaveBridge :=
  @Functions.SourceDirect.Stmt.leave_bridge

abbrev functionsSourceDirectStmtLeaveStmtOutcomeBridge :=
  @Functions.SourceDirect.Stmt.leave_stmtOutcome_bridge

abbrev functionsSourceDirectStmtCallReturnedFromParts :=
  @Functions.SourceDirect.Stmt.call_returned_from_parts

abbrev functionsSourceDirectStmtCallHaltedFromParts :=
  @Functions.SourceDirect.Stmt.call_halted_from_parts

abbrev functionsSourceDirectStmtCallReturnedStmtOutcomeFromParts :=
  @Functions.SourceDirect.Stmt.call_returned_stmtOutcome_from_parts

abbrev functionsSourceDirectStmtCallHaltedStmtOutcomeFromParts :=
  @Functions.SourceDirect.Stmt.call_halted_stmtOutcome_from_parts

abbrev functionsSourceDirectStmtCallReturnedStmtRunResultFromParts :=
  @Functions.SourceDirect.Stmt.call_returned_stmtRunResult_from_parts

abbrev functionsSourceDirectStmtCallHaltedStmtRunResultFromParts :=
  @Functions.SourceDirect.Stmt.call_halted_stmtRunResult_from_parts

abbrev functionsSourceDirectStmtCallReturnedStmtRunBridgeFromParts :=
  @Functions.SourceDirect.Stmt.call_returned_stmtRunBridge_from_parts

abbrev functionsSourceDirectStmtCallHaltedStmtRunBridgeFromParts :=
  @Functions.SourceDirect.Stmt.call_halted_stmtRunBridge_from_parts

abbrev functionsSourceDirectStmtCallReturnedStmtRunBridgeWithLayoutFromParts :=
  @Functions.SourceDirect.Stmt.call_returned_stmtRunBridge_with_layout_from_parts

abbrev functionsSourceDirectStmtCallHaltedStmtRunBridgeWithLayoutFromParts :=
  @Functions.SourceDirect.Stmt.call_halted_stmtRunBridge_with_layout_from_parts

abbrev functionsSourceDirectStmtCallStmtRunBridgeFromSourceRunWithLayout :=
  @Functions.SourceDirect.Stmt.call_stmtRunBridge_from_source_run_with_layout

abbrev functionsSourceDirectStmtCallStmtRunBridgeFromSourceRunProgramWithLayout :=
  @Functions.SourceDirect.Stmt.call_stmtRunBridge_from_source_run_program_with_layout

abbrev functionsSourceDirectStmtTerminalStmtOutcomeBridge :=
  @Functions.SourceDirect.Stmt.terminal_stmtOutcome_bridge

abbrev functionsSourceDirectStmtTerminalArgsStmtOutcomeBridge :=
  @Functions.SourceDirect.Stmt.terminalArgs_stmtOutcome_bridge

abbrev functionsSourceDirectStmtExprStmtRunResultBridge :=
  @Functions.SourceDirect.Stmt.expr_stmtRunResult_bridge

abbrev functionsSourceDirectStmtExprStmtRunBridge :=
  @Functions.SourceDirect.Stmt.expr_stmtRunBridge

abbrev functionsSourceDirectStmtExprStmtRunBridgeFromScoped :=
  @Functions.SourceDirect.Stmt.expr_stmtRunBridge_from_scoped

abbrev functionsSourceDirectStmtExprStmtRunBridgeWithLayout :=
  @Functions.SourceDirect.Stmt.expr_stmtRunBridge_with_layout

abbrev functionsSourceDirectStmtExprStmtRunBridgeFromScopedWithLayout :=
  @Functions.SourceDirect.Stmt.expr_stmtRunBridge_from_scoped_with_layout

abbrev functionsSourceDirectStmtExprStmtRunBridgeFromSourceRunWithLayout :=
  @Functions.SourceDirect.Stmt.expr_stmtRunBridge_from_source_run_with_layout

abbrev functionsSourceDirectStmtLetExprStmtRunResultBridge :=
  @Functions.SourceDirect.Stmt.let_expr_stmtRunResult_bridge

abbrev functionsSourceDirectStmtLetExprStmtRunBridge :=
  @Functions.SourceDirect.Stmt.let_expr_stmtRunBridge

abbrev functionsSourceDirectStmtLetExprStmtRunBridgeFromScoped :=
  @Functions.SourceDirect.Stmt.let_expr_stmtRunBridge_from_scoped

abbrev functionsSourceDirectStmtLetExprStmtRunBridgeWithLayout :=
  @Functions.SourceDirect.Stmt.let_expr_stmtRunBridge_with_layout

abbrev functionsSourceDirectStmtLetExprStmtRunBridgeFromScopedWithLayout :=
  @Functions.SourceDirect.Stmt.let_expr_stmtRunBridge_from_scoped_with_layout

abbrev functionsSourceDirectStmtLetExprStmtRunBridgeFromSourceRunWithLayout :=
  @Functions.SourceDirect.Stmt.let_expr_stmtRunBridge_from_source_run_with_layout

abbrev functionsSourceDirectStmtAssignExprStmtRunResultBridge :=
  @Functions.SourceDirect.Stmt.assign_expr_stmtRunResult_bridge

abbrev functionsSourceDirectStmtAssignExprStmtRunBridge :=
  @Functions.SourceDirect.Stmt.assign_expr_stmtRunBridge

abbrev functionsSourceDirectStmtAssignExprStmtRunBridgeFromScoped :=
  @Functions.SourceDirect.Stmt.assign_expr_stmtRunBridge_from_scoped

abbrev functionsSourceDirectStmtAssignExprStmtRunBridgeWithLayout :=
  @Functions.SourceDirect.Stmt.assign_expr_stmtRunBridge_with_layout

abbrev functionsSourceDirectStmtAssignExprStmtRunBridgeFromScopedWithLayout :=
  @Functions.SourceDirect.Stmt.assign_expr_stmtRunBridge_from_scoped_with_layout

abbrev functionsSourceDirectStmtAssignExprStmtRunBridgeFromSourceRunWithLayout :=
  @Functions.SourceDirect.Stmt.assign_expr_stmtRunBridge_from_source_run_with_layout

abbrev functionsSourceDirectStmtBreakStmtRunResultBridge :=
  @Functions.SourceDirect.Stmt.brk_stmtRunResult_bridge

abbrev functionsSourceDirectStmtBreakStmtRunBridge :=
  @Functions.SourceDirect.Stmt.brk_stmtRunBridge

abbrev functionsSourceDirectStmtBreakStmtRunBridgeWithLayout :=
  @Functions.SourceDirect.Stmt.brk_stmtRunBridge_with_layout

abbrev functionsSourceDirectStmtBreakStmtRunBridgeWithLayoutCurrentScope :=
  @Functions.SourceDirect.Stmt.brk_stmtRunBridge_with_layout_current_scope

abbrev functionsSourceDirectStmtBreakStmtRunBridgeFromSourceRunWithLayout :=
  @Functions.SourceDirect.Stmt.brk_stmtRunBridge_from_source_run_with_layout

abbrev functionsSourceDirectStmtBreakStmtRunBridgeFromSourceRunWithLayoutCurrentScope :=
  @Functions.SourceDirect.Stmt.brk_stmtRunBridge_from_source_run_with_layout_current_scope

abbrev functionsSourceDirectStmtBreakLoopStmtRunBridgeFromSourceRunCurrentScope :=
  @Functions.SourceDirect.Stmt.brk_loopStmtRunBridge_from_source_run_current_scope

abbrev functionsSourceDirectStmtBreakLoopStmtRunBridgeFromSourceRunCleanupLayout :=
  @Functions.SourceDirect.Stmt.brk_loopStmtRunBridge_from_source_run_cleanup_layout

abbrev functionsSourceDirectStmtContinueStmtRunResultBridge :=
  @Functions.SourceDirect.Stmt.cont_stmtRunResult_bridge

abbrev functionsSourceDirectStmtContinueStmtRunBridge :=
  @Functions.SourceDirect.Stmt.cont_stmtRunBridge

abbrev functionsSourceDirectStmtContinueStmtRunBridgeWithLayout :=
  @Functions.SourceDirect.Stmt.cont_stmtRunBridge_with_layout

abbrev functionsSourceDirectStmtContinueStmtRunBridgeWithLayoutCurrentScope :=
  @Functions.SourceDirect.Stmt.cont_stmtRunBridge_with_layout_current_scope

abbrev functionsSourceDirectStmtContinueStmtRunBridgeFromSourceRunWithLayout :=
  @Functions.SourceDirect.Stmt.cont_stmtRunBridge_from_source_run_with_layout

abbrev functionsSourceDirectStmtContinueStmtRunBridgeFromSourceRunWithLayoutCurrentScope :=
  @Functions.SourceDirect.Stmt.cont_stmtRunBridge_from_source_run_with_layout_current_scope

abbrev functionsSourceDirectStmtContinueLoopStmtRunBridgeFromSourceRunCurrentScope :=
  @Functions.SourceDirect.Stmt.cont_loopStmtRunBridge_from_source_run_current_scope

abbrev functionsSourceDirectStmtContinueLoopStmtRunBridgeFromSourceRunCleanupLayout :=
  @Functions.SourceDirect.Stmt.cont_loopStmtRunBridge_from_source_run_cleanup_layout

abbrev functionsSourceDirectStmtLeaveStmtRunResultBridge :=
  @Functions.SourceDirect.Stmt.leave_stmtRunResult_bridge

abbrev functionsSourceDirectStmtLeaveStmtRunBridge :=
  @Functions.SourceDirect.Stmt.leave_stmtRunBridge

abbrev functionsSourceDirectStmtLeaveStmtRunBridgeWithLayout :=
  @Functions.SourceDirect.Stmt.leave_stmtRunBridge_with_layout

abbrev functionsSourceDirectStmtLeaveStmtRunBridgeFromSourceRunWithLayout :=
  @Functions.SourceDirect.Stmt.leave_stmtRunBridge_from_source_run_with_layout

abbrev functionsSourceDirectStmtLeaveStmtRunBridgeFromSourceRunFrameBound :=
  @Functions.SourceDirect.Stmt.leave_stmtRunBridge_from_source_run_frameBound

abbrev functionsSourceDirectStmtTerminalStmtRunResultBridge :=
  @Functions.SourceDirect.Stmt.terminal_stmtRunResult_bridge

abbrev functionsSourceDirectStmtTerminalStmtRunBridge :=
  @Functions.SourceDirect.Stmt.terminal_stmtRunBridge

abbrev functionsSourceDirectStmtTerminalStmtRunBridgeWithLayout :=
  @Functions.SourceDirect.Stmt.terminal_stmtRunBridge_with_layout

abbrev functionsSourceDirectStmtTerminalStmtRunBridgeFromSourceRunWithLayout :=
  @Functions.SourceDirect.Stmt.terminal_stmtRunBridge_from_source_run_with_layout

abbrev functionsSourceDirectStmtTerminalArgsStmtRunResultBridge :=
  @Functions.SourceDirect.Stmt.terminalArgs_stmtRunResult_bridge

abbrev functionsSourceDirectStmtTerminalArgsStmtRunBridge :=
  @Functions.SourceDirect.Stmt.terminalArgs_stmtRunBridge

abbrev functionsSourceDirectStmtTerminalArgsStmtRunBridgeFromScoped :=
  @Functions.SourceDirect.Stmt.terminalArgs_stmtRunBridge_from_scoped

abbrev functionsSourceDirectStmtTerminalArgsStmtRunBridgeWithLayout :=
  @Functions.SourceDirect.Stmt.terminalArgs_stmtRunBridge_with_layout

abbrev functionsSourceDirectStmtTerminalArgsStmtRunBridgeFromScopedWithLayout :=
  @Functions.SourceDirect.Stmt.terminalArgs_stmtRunBridge_from_scoped_with_layout

abbrev functionsSourceDirectStmtTerminalArgsStmtRunBridgeFromSourceRunWithLayout :=
  @Functions.SourceDirect.Stmt.terminalArgs_stmtRunBridge_from_source_run_with_layout

abbrev functionsSourceDirectExprEvalConditionBridgeSourceOwned :=
  @Functions.SourceDirect.Expr.evalCondition_bridge_sourceOwned

abbrev functionsSourceDirectExprEvalOnePopBridgeSourceOwned :=
  @Functions.SourceDirect.Expr.evalOne_pop_bridge_sourceOwned

abbrev functionsSourceDirectSwitchSourceSelectEq :=
  @Functions.SourceDirect.Switch.source_select_eq

abbrev functionsSourceDirectStmtIfFalseStmtRunResultFromCondition :=
  @Functions.SourceDirect.Stmt.if_false_stmtRunResult_from_condition

abbrev functionsSourceDirectStmtIfFalseStmtRunBridgeFromCondition :=
  @Functions.SourceDirect.Stmt.if_false_stmtRunBridge_from_condition

abbrev functionsSourceDirectStmtIfFalseStmtRunBridgeFromScopedCondition :=
  @Functions.SourceDirect.Stmt.if_false_stmtRunBridge_from_scoped_condition

abbrev functionsSourceDirectStmtIfFalseStmtRunBridgeFromConditionWithLayout :=
  @Functions.SourceDirect.Stmt.if_false_stmtRunBridge_from_condition_with_layout

abbrev functionsSourceDirectStmtIfFalseStmtRunBridgeFromScopedConditionWithLayout :=
  @Functions.SourceDirect.Stmt.if_false_stmtRunBridge_from_scoped_condition_with_layout

abbrev functionsSourceDirectStmtIfTrueRegularStmtRunResultFromOpen :=
  @Functions.SourceDirect.Stmt.if_true_regular_stmtRunResult_from_open

abbrev functionsSourceDirectStmtIfTrueRegularStmtRunBridgeFromOpen :=
  @Functions.SourceDirect.Stmt.if_true_regular_stmtRunBridge_from_open

abbrev functionsSourceDirectStmtIfTrueRegularStmtRunBridgeFromScopedBody :=
  @Functions.SourceDirect.Stmt.if_true_regular_stmtRunBridge_from_scoped_body

abbrev functionsSourceDirectStmtIfTrueRegularStmtRunBridgeFromOpenWithLayout :=
  @Functions.SourceDirect.Stmt.if_true_regular_stmtRunBridge_from_open_with_layout

abbrev functionsSourceDirectStmtIfTrueRegularStmtRunBridgeFromScopedBodyWithLayout :=
  @Functions.SourceDirect.Stmt.if_true_regular_stmtRunBridge_from_scoped_body_with_layout

abbrev functionsSourceDirectStmtIfTrueNonregularStmtRunResultFromOpen :=
  @Functions.SourceDirect.Stmt.if_true_nonregular_stmtRunResult_from_open

abbrev functionsSourceDirectStmtIfTrueNonregularStmtRunBridgeFromOpen :=
  @Functions.SourceDirect.Stmt.if_true_nonregular_stmtRunBridge_from_open

abbrev functionsSourceDirectStmtIfTrueNonregularStmtRunBridgeFromScopedBody :=
  @Functions.SourceDirect.Stmt.if_true_nonregular_stmtRunBridge_from_scoped_body

abbrev functionsSourceDirectStmtIfTrueNonregularStmtRunBridgeFromOpenWithLayout :=
  @Functions.SourceDirect.Stmt.if_true_nonregular_stmtRunBridge_from_open_with_layout

abbrev functionsSourceDirectStmtIfTrueNonregularStmtRunBridgeFromScopedBodyWithLayout :=
  @Functions.SourceDirect.Stmt.if_true_nonregular_stmtRunBridge_from_scoped_body_with_layout

abbrev functionsSourceDirectStmtIfTrueStmtRunBridgeFromOpenBridgeWithLayout :=
  @Functions.SourceDirect.Stmt.if_true_stmtRunBridge_from_open_bridge_with_layout

abbrev functionsSourceDirectStmtIfStmtRunBridgeFromSourceRunWithLayout :=
  @Functions.SourceDirect.Stmt.if_stmtRunBridge_from_source_run_with_layout

abbrev functionsSourceDirectStmtIfStmtRunBridgeFromExactSourceRunWithLayout :=
  @Functions.SourceDirect.Stmt.if_stmtRunBridge_from_exact_source_run_with_layout

abbrev functionsSourceDirectStmtSwitchNoneStmtRunResultFromScrutinee :=
  @Functions.SourceDirect.Stmt.switch_none_stmtRunResult_from_scrutinee

abbrev functionsSourceDirectStmtSwitchNoneStmtRunBridgeFromScrutinee :=
  @Functions.SourceDirect.Stmt.switch_none_stmtRunBridge_from_scrutinee

abbrev functionsSourceDirectStmtSwitchNoneStmtRunBridgeFromScopedScrutinee :=
  @Functions.SourceDirect.Stmt.switch_none_stmtRunBridge_from_scoped_scrutinee

abbrev functionsSourceDirectStmtSwitchNoneStmtRunBridgeFromScrutineeWithLayout :=
  @Functions.SourceDirect.Stmt.switch_none_stmtRunBridge_from_scrutinee_with_layout

abbrev functionsSourceDirectStmtSwitchNoneStmtRunBridgeFromScopedScrutineeWithLayout :=
  @Functions.SourceDirect.Stmt.switch_none_stmtRunBridge_from_scoped_scrutinee_with_layout

abbrev functionsSourceDirectStmtSwitchSomeRegularStmtRunResultFromOpen :=
  @Functions.SourceDirect.Stmt.switch_some_regular_stmtRunResult_from_open

abbrev functionsSourceDirectStmtSwitchSomeRegularStmtRunBridgeFromOpen :=
  @Functions.SourceDirect.Stmt.switch_some_regular_stmtRunBridge_from_open

abbrev functionsSourceDirectStmtSwitchSomeRegularStmtRunBridgeFromScopedBody :=
  @Functions.SourceDirect.Stmt.switch_some_regular_stmtRunBridge_from_scoped_body

abbrev functionsSourceDirectStmtSwitchSomeRegularStmtRunBridgeFromOpenWithLayout :=
  @Functions.SourceDirect.Stmt.switch_some_regular_stmtRunBridge_from_open_with_layout

abbrev functionsSourceDirectStmtSwitchSomeRegularStmtRunBridgeFromScopedBodyWithLayout :=
  @Functions.SourceDirect.Stmt.switch_some_regular_stmtRunBridge_from_scoped_body_with_layout

abbrev functionsSourceDirectStmtSwitchSomeNonregularStmtRunResultFromOpen :=
  @Functions.SourceDirect.Stmt.switch_some_nonregular_stmtRunResult_from_open

abbrev functionsSourceDirectStmtSwitchSomeNonregularStmtRunBridgeFromOpen :=
  @Functions.SourceDirect.Stmt.switch_some_nonregular_stmtRunBridge_from_open

abbrev functionsSourceDirectStmtSwitchSomeNonregularStmtRunBridgeFromScopedBody :=
  @Functions.SourceDirect.Stmt.switch_some_nonregular_stmtRunBridge_from_scoped_body

abbrev functionsSourceDirectStmtSwitchSomeNonregularStmtRunBridgeFromOpenWithLayout :=
  @Functions.SourceDirect.Stmt.switch_some_nonregular_stmtRunBridge_from_open_with_layout

abbrev functionsSourceDirectStmtSwitchSomeNonregularStmtRunBridgeFromScopedBodyWithLayout :=
  @Functions.SourceDirect.Stmt.switch_some_nonregular_stmtRunBridge_from_scoped_body_with_layout

abbrev functionsSourceDirectStmtSwitchSomeStmtRunBridgeFromOpenBridgeWithLayout :=
  @Functions.SourceDirect.Stmt.switch_some_stmtRunBridge_from_open_bridge_with_layout

abbrev functionsSourceDirectStmtSwitchStmtRunBridgeFromSourceRunWithLayout :=
  @Functions.SourceDirect.Stmt.switch_stmtRunBridge_from_source_run_with_layout

abbrev functionsSourceDirectStmtSwitchStmtRunBridgeFromExactSourceRunWithLayout :=
  @Functions.SourceDirect.Stmt.switch_stmtRunBridge_from_exact_source_run_with_layout

abbrev functionsSourceDirectStmtRunForLoopFalseFromCondition :=
  @Functions.SourceDirect.Stmt.runForLoop_false_from_condition

abbrev functionsSourceDirectStmtRunForLoopConditionBridgeFromScoped :=
  @Functions.SourceDirect.Stmt.runForLoop_condition_bridge_from_scoped

abbrev functionsSourceDirectStmtRunForLoopFalseFromScopedCondition :=
  @Functions.SourceDirect.Stmt.runForLoop_false_from_scoped_condition

abbrev functionsSourceDirectStmtRunForLoopBodyBreakFromScoped :=
  @Functions.SourceDirect.Stmt.runForLoop_body_break_from_scoped

abbrev functionsSourceDirectStmtRunForLoopBodyBreakFromScopedCondition :=
  @Functions.SourceDirect.Stmt.runForLoop_body_break_from_scoped_condition

abbrev functionsSourceDirectStmtRunForLoopBodyLeaveFromScoped :=
  @Functions.SourceDirect.Stmt.runForLoop_body_leave_from_scoped

abbrev functionsSourceDirectStmtRunForLoopBodyLeaveFromScopedCondition :=
  @Functions.SourceDirect.Stmt.runForLoop_body_leave_from_scoped_condition

abbrev functionsSourceDirectStmtRunForLoopBodyHaltFromScoped :=
  @Functions.SourceDirect.Stmt.runForLoop_body_halt_from_scoped

abbrev functionsSourceDirectStmtRunForLoopBodyHaltFromScopedCondition :=
  @Functions.SourceDirect.Stmt.runForLoop_body_halt_from_scoped_condition

abbrev functionsSourceDirectStmtRunForLoopBodyNextPostLeaveOrHaltFromScoped :=
  @Functions.SourceDirect.Stmt.runForLoop_body_next_post_leave_or_halt_from_scoped

abbrev functionsSourceDirectStmtRunForLoopBodyNextPostLeaveOrHaltFromScopedCondition :=
  @Functions.SourceDirect.Stmt.runForLoop_body_next_post_leave_or_halt_from_scoped_condition

abbrev functionsSourceDirectStmtRunForLoopBodyNextPostRegularFromScoped :=
  @Functions.SourceDirect.Stmt.runForLoop_body_next_post_regular_from_scoped

abbrev functionsSourceDirectStmtRunForLoopBodyNextPostRegularFromScopedCondition :=
  @Functions.SourceDirect.Stmt.runForLoop_body_next_post_regular_from_scoped_condition

abbrev functionsSourceDirectStmtRunForLoopFromExactSourceRunWithLayout :=
  @Functions.SourceDirect.Stmt.runForLoop_from_exact_source_run_with_layout

abbrev functionsSourceDirectStmtRunForLoopFromExactSourceRunWithBodyDispatcher :=
  @Functions.SourceDirect.Stmt.runForLoop_from_exact_source_run_with_body_dispatcher

abbrev functionsSourceDirectStmtRunForLoopFromExactSourceRunWithBodyPostDispatchers :=
  @Functions.SourceDirect.Stmt.runForLoop_from_exact_source_run_with_body_post_dispatchers

abbrev functionsSourceDirectStmtRunForLoopFromExactSourceRunWithBodyPostDispatchersInduction :=
  @Functions.SourceDirect.Stmt.runForLoop_from_exact_source_run_with_body_post_dispatchers_induction

abbrev functionsSourceDirectStmtRunForLoopFromExactSourceRunWithBodyDispatcherForCallback :=
  @Functions.SourceDirect.Stmt.runForLoop_from_exact_source_run_with_body_dispatcher_for_callback

abbrev functionsSourceDirectStmtRunForLoopFromExactSourceRunWithBodyDispatcherForCallbackBounded :=
  @Functions.SourceDirect.Stmt.runForLoop_from_exact_source_run_with_body_dispatcher_for_callback_bounded

abbrev functionsSourceDirectStmtRunForLoopFromExactSourceRunWithBodyPostDispatchersForCallback :=
  @Functions.SourceDirect.Stmt.runForLoop_from_exact_source_run_with_body_post_dispatchers_for_callback

abbrev functionsSourceDirectStmtRunForLoopFromExactSourceRunWithBodyPostDispatchersForCallbackBounded :=
  @Functions.SourceDirect.Stmt.runForLoop_from_exact_source_run_with_body_post_dispatchers_for_callback_bounded

abbrev functionsSourceDirectStmtRunForLoopFromExactSourceRunWithBodyPostDispatchersInductionForCallback :=
  @Functions.SourceDirect.Stmt.runForLoop_from_exact_source_run_with_body_post_dispatchers_induction_for_callback

abbrev functionsSourceDirectStmtRunForLoopFromExactSourceRunWithBodyPostDispatchersInductionForCallbackBounded :=
  @Functions.SourceDirect.Stmt.runForLoop_from_exact_source_run_with_body_post_dispatchers_induction_for_callback_bounded

abbrev functionsSourceDirectStmtIfLoopStmtRunBridgeFromExactSourceRunWithLayout :=
  @Functions.SourceDirect.Stmt.if_loopStmtRunBridge_from_exact_source_run_with_layout

abbrev functionsSourceDirectStmtSwitchLoopStmtRunBridgeFromExactSourceRunWithLayout :=
  @Functions.SourceDirect.Stmt.switch_loopStmtRunBridge_from_exact_source_run_with_layout

abbrev functionsSourceDirectStmtForLeaveOrHaltStmtRunResultFromInitOpen :=
  @Functions.SourceDirect.Stmt.for_leave_or_halt_stmtRunResult_from_init_open

abbrev functionsSourceDirectStmtForLeaveOrHaltStmtRunBridgeFromInitOpen :=
  @Functions.SourceDirect.Stmt.for_leave_or_halt_stmtRunBridge_from_init_open

abbrev functionsSourceDirectStmtForLeaveOrHaltStmtRunBridgeWithLayoutFromInitOpen :=
  @Functions.SourceDirect.Stmt.for_leave_or_halt_stmtRunBridge_with_layout_from_init_open

abbrev functionsSourceDirectStmtForRegularStmtRunResultFromInitLoopRegular :=
  @Functions.SourceDirect.Stmt.for_regular_stmtRunResult_from_init_loop_regular

abbrev functionsSourceDirectStmtForRegularStmtRunBridgeFromInitLoopRegular :=
  @Functions.SourceDirect.Stmt.for_regular_stmtRunBridge_from_init_loop_regular

abbrev functionsSourceDirectStmtForRegularStmtRunBridgeWithLayoutFromInitLoopRegular :=
  @Functions.SourceDirect.Stmt.for_regular_stmtRunBridge_with_layout_from_init_loop_regular

abbrev functionsSourceDirectStmtForLeaveOrHaltStmtRunResultFromInitLoop :=
  @Functions.SourceDirect.Stmt.for_leave_or_halt_stmtRunResult_from_init_loop

abbrev functionsSourceDirectStmtForLeaveOrHaltStmtRunBridgeFromInitLoop :=
  @Functions.SourceDirect.Stmt.for_leave_or_halt_stmtRunBridge_from_init_loop

abbrev functionsSourceDirectStmtForLeaveOrHaltStmtRunBridgeWithLayoutFromInitLoop :=
  @Functions.SourceDirect.Stmt.for_leave_or_halt_stmtRunBridge_with_layout_from_init_loop

abbrev functionsSourceDirectStmtForStmtRunBridgeFromSourceRunWithLayout :=
  @Functions.SourceDirect.Stmt.for_stmtRunBridge_from_source_run_with_layout

abbrev functionsSourceDirectStmtForStmtRunBridgeFromExactSourceRunWithLayout :=
  @Functions.SourceDirect.Stmt.for_stmtRunBridge_from_exact_source_run_with_layout

abbrev functionsSourceDirectStmtForStmtRunBridgeFromExactSourceRunWithDispatchers :=
  @Functions.SourceDirect.Stmt.for_stmtRunBridge_from_exact_source_run_with_dispatchers

abbrev functionsSourceDirectStmtForStmtRunBridgeFromExactSourceRunWithForCallback :=
  @Functions.SourceDirect.Stmt.for_stmtRunBridge_from_exact_source_run_with_for_callback

abbrev functionsSourceDirectStmtForStmtRunBridgeFromExactSourceRunWithForCallbackBounded :=
  @Functions.SourceDirect.Stmt.for_stmtRunBridge_from_exact_source_run_with_for_callback_bounded

abbrev functionsSourceDirectStmtStmtRunBridgeFromSourceRunInvariant :=
  @Functions.SourceDirect.Stmt.stmtRunBridge_from_source_run_invariant

abbrev functionsSourceDirectStmtStmtRunBridgeFromSourceRunInvariantWithForDispatchers :=
  @Functions.SourceDirect.Stmt.stmtRunBridge_from_source_run_invariant_with_for_dispatchers

abbrev functionsSourceDirectStmtStmtRunBridgeFromSourceRunInvariantWithForCallback :=
  @Functions.SourceDirect.Stmt.stmtRunBridge_from_source_run_invariant_with_for_callback

abbrev functionsSourceDirectStmtStmtRunBridgeFromSourceRunInvariantWithForCallbackBounded :=
  @Functions.SourceDirect.Stmt.stmtRunBridge_from_source_run_invariant_with_for_callback_bounded

abbrev functionsSourceDirectStmtStmtRunBridgeFromSourceRunInvariantWithForCallbackDispatchers :=
  @Functions.SourceDirect.Stmt.stmtRunBridge_from_source_run_invariant_with_for_callback_dispatchers

abbrev functionsSourceDirectStmtStmtRunBridgeFromSourceRunInvariantWithForCallbackDispatchersBounded :=
  @Functions.SourceDirect.Stmt.stmtRunBridge_from_source_run_invariant_with_for_callback_dispatchers_bounded

abbrev functionsSourceDirectStmtLoopStmtRunBridgeFromSourceRunInvariant :=
  @Functions.SourceDirect.Stmt.loopStmtRunBridge_from_source_run_invariant

abbrev functionsSourceDirectStmtLoopStmtRunBridgeFromSourceRunInvariantWithForCallback :=
  @Functions.SourceDirect.Stmt.loopStmtRunBridge_from_source_run_invariant_with_for_callback

abbrev functionsSourceDirectStmtLoopStmtRunBridgeFromSourceRunInvariantWithForCallbackBounded :=
  @Functions.SourceDirect.Stmt.loopStmtRunBridge_from_source_run_invariant_with_for_callback_bounded

abbrev functionsSourceDirectBlockSourceRunOpenConsHead :=
  @Functions.SourceDirect.Block.source_runOpen_cons_head

abbrev functionsSourceDirectBlockRunOpenNilBridge :=
  @Functions.SourceDirect.Block.runOpen_nil_bridge

abbrev functionsSourceDirectBlockRunOpenConsRegularFromParts :=
  @Functions.SourceDirect.Block.runOpen_cons_regular_from_parts

abbrev functionsSourceDirectBlockRunOpenConsRegularFromStmtRunResult :=
  @Functions.SourceDirect.Block.runOpen_cons_regular_from_stmtRunResult

abbrev functionsSourceDirectBlockRunOpenConsNonregularFromHead :=
  @Functions.SourceDirect.Block.runOpen_cons_nonregular_from_head

abbrev functionsSourceDirectBlockRunOpenConsNonregularFromStmtRunResult :=
  @Functions.SourceDirect.Block.runOpen_cons_nonregular_from_stmtRunResult

abbrev functionsSourceDirectBlockRunOpenConsFromStmtRunResult :=
  @Functions.SourceDirect.Block.runOpen_cons_from_stmtRunResult

abbrev functionsSourceDirectBlockRunOpenConsFromStmtRunBridge :=
  @Functions.SourceDirect.Block.runOpen_cons_from_stmtRunBridge

abbrev functionsSourceDirectBlockRunOpenConsFromStmtRunBridgeWithLayout :=
  @Functions.SourceDirect.Block.runOpen_cons_from_stmtRunBridge_with_layout

abbrev functionsSourceDirectBlockRunOpenConsFromSourceRunWithLayout :=
  @Functions.SourceDirect.Block.runOpen_cons_from_source_run_with_layout

abbrev functionsSourceDirectBlockRunOpenSuccFromSourceRunWithSubfuelCallbacks :=
  @Functions.SourceDirect.Block.runOpen_succ_from_source_run_with_subfuel_callbacks

abbrev functionsSourceDirectBlockRunOpenFromSourceRunWithStmtCallback :=
  @Functions.SourceDirect.Block.runOpen_from_source_run_with_stmt_callback

abbrev functionsSourceDirectBlockRunOpenFromSourceRunWithInvariantCallback :=
  @Functions.SourceDirect.Block.runOpen_from_source_run_with_invariant_callback

abbrev functionsSourceDirectBlockRunOpenFromSourceRunWithInvariantCallbackBounded :=
  @Functions.SourceDirect.Block.runOpen_from_source_run_with_invariant_callback_bounded

abbrev functionsSourceDirectBlockRunOpenFromSourceRunWithLoopInvariantCallback :=
  @Functions.SourceDirect.Block.runOpen_from_source_run_with_loop_invariant_callback

abbrev functionsSourceDirectBlockRunOpenFromSourceRunWithLoopInvariantCallbackDepth :=
  @Functions.SourceDirect.Block.runOpen_from_source_run_with_loop_invariant_callback_depth

abbrev functionsSourceDirectBlockRunOpenFromSourceRunWithLoopInvariantCallbackDepthBounded :=
  @Functions.SourceDirect.Block.runOpen_from_source_run_with_loop_invariant_callback_depth_bounded

abbrev functionsSourceDirectBlockRunOpenFromSourceRunWithStatementDispatcher :=
  @Functions.SourceDirect.Block.runOpen_from_source_run_with_statement_dispatcher

abbrev functionsSourceDirectBlockRunOpenFromSourceRunWithStatementDispatcherForDispatchers :=
  @Functions.SourceDirect.Block.runOpen_from_source_run_with_statement_dispatcher_for_dispatchers

abbrev functionsSourceDirectBlockRunOpenFromSourceRunWithLoopStatementDispatcher :=
  @Functions.SourceDirect.Block.runOpen_from_source_run_with_loop_statement_dispatcher

abbrev functionsSourceDirectBlockRunOpenFromSourceRunWithLoopStatementDispatcherForCallback :=
  @Functions.SourceDirect.Block.runOpen_from_source_run_with_loop_statement_dispatcher_for_callback

abbrev functionsSourceDirectBlockRunOpenFromSourceRunWithLoopStatementDispatcherForCallbackBounded :=
  @Functions.SourceDirect.Block.runOpen_from_source_run_with_loop_statement_dispatcher_for_callback_bounded

abbrev functionsSourceDirectBlockScopedOutcomeRel :=
  @Functions.SourceDirect.BlockScopedOutcomeRel

abbrev functionsSourceDirectBlockScopedOutcomeRelToStmtOutcomeRelOfNotBreakContinue :=
  @Functions.SourceDirect.BlockScopedOutcomeRel.to_stmtOutcomeRel_of_not_break_continue

abbrev functionsSourceDirectBlockScopedOutcomeRelRegularStateRel :=
  @Functions.SourceDirect.BlockScopedOutcomeRel.regular_stateRel

abbrev functionsSourceDirectBlockScopedOutcomeRelLeaveStmtOutcomeRel :=
  @Functions.SourceDirect.BlockScopedOutcomeRel.leave_stmtOutcomeRel

abbrev functionsSourceDirectBlockScopedOutcomeRelHaltStmtOutcomeRel :=
  @Functions.SourceDirect.BlockScopedOutcomeRel.halt_stmtOutcomeRel

abbrev functionsSourceDirectBlockRunScopedFromOpenBridgeWithLayout :=
  @Functions.SourceDirect.Block.runScoped_from_open_bridge_with_layout

abbrev functionsSourceDirectBlockRunScopedFromSourceRunWithInvariantCallbackBounded :=
  @Functions.SourceDirect.Block.runScoped_from_source_run_with_invariant_callback_bounded

abbrev functionsSourceDirectBlockRunScopedFromSourceRunWithInvariantCallback :=
  @Functions.SourceDirect.Block.runScoped_from_source_run_with_invariant_callback

abbrev functionsSourceDirectBlockRunScopedFromLoopOpenBridgeWithLayout :=
  @Functions.SourceDirect.Block.runScoped_from_loop_open_bridge_with_layout

abbrev functionsSourceDirectBlockRunScopedFromLoopOpenBridge :=
  @Functions.SourceDirect.Block.runScoped_from_loop_open_bridge

abbrev functionsSourceDirectBlockRunScopedFromSourceRunWithLoopStmtCallback :=
  @Functions.SourceDirect.Block.runScoped_from_source_run_with_loop_stmt_callback

abbrev functionsSourceDirectBlockRunScopedFromSourceRunWithLoopInvariantCallback :=
  @Functions.SourceDirect.Block.runScoped_from_source_run_with_loop_invariant_callback

abbrev functionsSourceDirectBlockRunScopedFromSourceRunWithLoopInvariantCallbackCleanup :=
  @Functions.SourceDirect.Block.runScoped_from_source_run_with_loop_invariant_callback_cleanup

abbrev functionsSourceDirectBlockRunScopedFromSourceRunWithLoopStatementDispatcher :=
  @Functions.SourceDirect.Block.runScoped_from_source_run_with_loop_statement_dispatcher

abbrev functionsSourceDirectBlockRunScopedFromSourceRunWithLoopStatementDispatcherForCallback :=
  @Functions.SourceDirect.Block.runScoped_from_source_run_with_loop_statement_dispatcher_for_callback

abbrev functionsSourceDirectBlockRunScopedFromSourceRunWithLoopStatementDispatcherForCallbackBounded :=
  @Functions.SourceDirect.Block.runScoped_from_source_run_with_loop_statement_dispatcher_for_callback_bounded

abbrev functionsSourceDirectBlockLoopStmtRunBridgeFromSourceRunWithLoopStmtCallback :=
  @Functions.SourceDirect.Block.block_loopStmtRunBridge_from_source_run_with_loop_stmt_callback

abbrev functionsSourceDirectBlockLoopStmtRunBridgeFromSourceRunWithLoopInvariantCallback :=
  @Functions.SourceDirect.Block.block_loopStmtRunBridge_from_source_run_with_loop_invariant_callback

abbrev functionsSourceDirectBlockLoopStmtRunBridgeFromSourceRunWithLoopInvariantCallbackCleanup :=
  @Functions.SourceDirect.Block.block_loopStmtRunBridge_from_source_run_with_loop_invariant_callback_cleanup

abbrev functionsSourceDirectBlockRunScopedFromSourceRunWithStatementDispatcher :=
  @Functions.SourceDirect.Block.runScoped_from_source_run_with_statement_dispatcher

abbrev functionsSourceDirectBlockRunScopedFromSourceRunWithStatementDispatcherForDispatchers :=
  @Functions.SourceDirect.Block.runScoped_from_source_run_with_statement_dispatcher_for_dispatchers

abbrev functionsSourceDirectBlockRunOpenFromSourceRunWithStatementDispatcherForCallback :=
  @Functions.SourceDirect.Block.runOpen_from_source_run_with_statement_dispatcher_for_callback

abbrev functionsSourceDirectBlockRunOpenFromSourceRunWithStatementDispatcherForCallbackBounded :=
  @Functions.SourceDirect.Block.runOpen_from_source_run_with_statement_dispatcher_for_callback_bounded

abbrev functionsSourceDirectBlockRunScopedFromSourceRunWithStatementDispatcherForCallback :=
  @Functions.SourceDirect.Block.runScoped_from_source_run_with_statement_dispatcher_for_callback

abbrev functionsSourceDirectBlockRunScopedFromSourceRunWithStatementDispatcherForCallbackBounded :=
  @Functions.SourceDirect.Block.runScoped_from_source_run_with_statement_dispatcher_for_callback_bounded

abbrev functionsSourceDirectBlockRunOpenFromSourceRunWithStatementDispatcherForCallbackDispatchers :=
  @Functions.SourceDirect.Block.runOpen_from_source_run_with_statement_dispatcher_for_callback_dispatchers

abbrev functionsSourceDirectBlockRunOpenFromSourceRunWithStatementDispatcherForCallbackDispatchersBounded :=
  @Functions.SourceDirect.Block.runOpen_from_source_run_with_statement_dispatcher_for_callback_dispatchers_bounded

abbrev functionsSourceDirectBlockRunScopedFromSourceRunWithStatementDispatcherForCallbackDispatchers :=
  @Functions.SourceDirect.Block.runScoped_from_source_run_with_statement_dispatcher_for_callback_dispatchers

abbrev functionsSourceDirectBlockRunScopedFromSourceRunWithStatementDispatcherForCallbackDispatchersBounded :=
  @Functions.SourceDirect.Block.runScoped_from_source_run_with_statement_dispatcher_for_callback_dispatchers_bounded

abbrev functionsSourceDirectRecursiveCallbacks :=
  @Functions.SourceDirect.RecursiveCallbacks

abbrev functionsSourceDirectRecursiveCallbacksUpTo :=
  @Functions.SourceDirect.RecursiveCallbacksUpTo

abbrev functionsSourceDirectRecursiveCallbacksUpToMono :=
  @Functions.SourceDirect.RecursiveCallbacksUpTo.mono

abbrev functionsSourceDirectRecursiveCallbacksUpToZero :=
  @Functions.SourceDirect.RecursiveCallbacksUpTo.zero

abbrev functionsSourceDirectRecursiveCallbacksUpToCallBodyFromAllUpTo :=
  @Functions.SourceDirect.RecursiveCallbacksUpTo.callBody_from_all_upTo

abbrev functionsSourceDirectRecursiveCallbacksUpToSuccAll :=
  @Functions.SourceDirect.RecursiveCallbacksUpTo.succ_all

abbrev functionsSourceDirectRecursiveCallbacksUpToAll :=
  @Functions.SourceDirect.RecursiveCallbacksUpTo.all_upTo

abbrev functionsSourceDirectRecursiveCallbacksToUpTo :=
  @Functions.SourceDirect.RecursiveCallbacks.to_upTo

abbrev functionsSourceDirectRecursiveCallbacksOfForallUpTo :=
  @Functions.SourceDirect.RecursiveCallbacks.of_forall_upTo

abbrev functionsSourceDirectRecursiveCallbacksConstructed :=
  @Functions.SourceDirect.RecursiveCallbacks.constructed

abbrev functionsSourceDirectRecursiveCallbacksRunOpenFromSourceRun :=
  @Functions.SourceDirect.RecursiveCallbacks.runOpen_from_source_run

abbrev functionsSourceDirectRecursiveCallbacksRunScopedFromSourceRun :=
  @Functions.SourceDirect.RecursiveCallbacks.runScoped_from_source_run

abbrev functionsSourceDirectRecursiveCallbacksRunOpenFromSourceRunConstructed :=
  @Functions.SourceDirect.RecursiveCallbacks.runOpen_from_source_run_constructed

abbrev functionsSourceDirectRecursiveCallbacksRunScopedFromSourceRunConstructed :=
  @Functions.SourceDirect.RecursiveCallbacks.runScoped_from_source_run_constructed

abbrev functionsSourceDirectProgramRunStateToDirectExists :=
  @Functions.SourceDirect.Program.runState_toDirect_exists

abbrev functionsSourceDirectProgramRunToDirectExists :=
  @Functions.SourceDirect.Program.run_toDirect_exists

abbrev functionsSourceDirectBlockRunScopedRegularFromOpen :=
  @Functions.SourceDirect.Block.runScoped_regular_from_open

abbrev functionsSourceDirectBlockRegularStmtRunResultFromOpen :=
  @Functions.SourceDirect.Block.block_regular_stmtRunResult_from_open

abbrev functionsSourceDirectStmtRunResultRelOfNonregular :=
  @Functions.SourceDirect.StmtRunResultRel.of_nonregular

abbrev functionsSourceDirectLoopStmtRunResultRel :=
  @Functions.SourceDirect.LoopStmtRunResultRel

abbrev functionsSourceDirectLoopStmtRunResultRelToStmtRunResultRel :=
  @Functions.SourceDirect.LoopStmtRunResultRel.to_stmtRunResultRel

abbrev functionsSourceDirectLoopStmtRunResultRelOfStmtRunResultRelNotBreakContinue :=
  @Functions.SourceDirect.LoopStmtRunResultRel.of_stmtRunResultRel_not_break_continue

abbrev functionsSourceDirectLoopStmtRunResultRelOfStmtOutcomeRelSameCtx :=
  @Functions.SourceDirect.LoopStmtRunResultRel.of_stmtOutcomeRel_same_ctx

abbrev functionsSourceDirectLoopStmtRunResultRelToStmtOutcomeRelOfTargetLayout :=
  @Functions.SourceDirect.LoopStmtRunResultRel.to_stmtOutcomeRel_of_target_layout

abbrev functionsSourceDirectLoopStmtRunResultRelBreak :=
  @Functions.SourceDirect.LoopStmtRunResultRel.brk

abbrev functionsSourceDirectLoopStmtRunResultRelContinue :=
  @Functions.SourceDirect.LoopStmtRunResultRel.cont

abbrev functionsSourceDirectLoopStmtRunResultRelRegularStateRel :=
  @Functions.SourceDirect.LoopStmtRunResultRel.regular_stateRel

abbrev functionsSourceDirectLoopStmtRunBridgeWithLayout :=
  @Functions.SourceDirect.LoopStmtRunBridgeWithLayout

abbrev functionsSourceDirectLoopStmtRunBridgeWithLayoutToStmtBridgeWithLayout :=
  @Functions.SourceDirect.LoopStmtRunBridgeWithLayout.to_stmt_bridge_with_layout

abbrev functionsSourceDirectLoopStmtRunBridgeWithLayoutOfStmtBridgeWithLayoutNotBreakContinue :=
  @Functions.SourceDirect.LoopStmtRunBridgeWithLayout.of_stmt_bridge_with_layout_not_break_continue

abbrev functionsSourceDirectLoopStmtRunBridgeWithLayoutOfPartsSameCtx :=
  @Functions.SourceDirect.LoopStmtRunBridgeWithLayout.of_parts_same_ctx

abbrev functionsSourceDirectLoopStmtRunBridgeWithLayoutTargetResultOfSource :=
  @Functions.SourceDirect.LoopStmtRunBridgeWithLayout.target_result_of_source

abbrev functionsSourceDirectLoopStmtRunBridgeWithLayoutOfLoopResultSameCtx :=
  @Functions.SourceDirect.LoopStmtRunBridgeWithLayout.of_loop_result_same_ctx

abbrev functionsSourceDirectLoopBlockOpenResultRel :=
  @Functions.SourceDirect.LoopBlockOpenResultRel

abbrev functionsSourceDirectLoopBlockOpenResultRelToBlockOpenResultRel :=
  @Functions.SourceDirect.LoopBlockOpenResultRel.to_blockOpenResultRel

abbrev functionsSourceDirectLoopBlockOpenResultRelOfLoopStmtRunResultRel :=
  @Functions.SourceDirect.LoopBlockOpenResultRel.of_loopStmtRunResultRel

abbrev functionsSourceDirectLoopBlockOpenRunBridgeWithLayout :=
  @Functions.SourceDirect.LoopBlockOpenRunBridgeWithLayout

abbrev functionsSourceDirectLoopBlockOpenRunBridgeWithLayoutToBlockOpenBridgeWithLayout :=
  @Functions.SourceDirect.LoopBlockOpenRunBridgeWithLayout.to_block_open_bridge_with_layout

abbrev functionsSourceDirectLoopBlockOpenRunBridgeWithLayoutTargetResultOfSource :=
  @Functions.SourceDirect.LoopBlockOpenRunBridgeWithLayout.target_result_of_source

abbrev functionsSourceDirectLoopBlockOpenRunBridgeWithLayoutNilFromRel :=
  @Functions.SourceDirect.LoopBlockOpenRunBridgeWithLayout.nil_from_rel

abbrev functionsSourceDirectBlockRunOpenConsNonregularFromLoopStmtRunResult :=
  @Functions.SourceDirect.Block.runOpen_cons_nonregular_from_loopStmtRunResult

abbrev functionsSourceDirectBlockRunOpenConsFromSourceRunWithLoopLayout :=
  @Functions.SourceDirect.Block.runOpen_cons_from_source_run_with_loop_layout

abbrev functionsSourceDirectBlockRunOpenSuccFromSourceRunWithLoopSubfuelCallbacks :=
  @Functions.SourceDirect.Block.runOpen_succ_from_source_run_with_loop_subfuel_callbacks

abbrev functionsSourceDirectBlockRunOpenFromSourceRunWithLoopStmtCallback :=
  @Functions.SourceDirect.Block.runOpen_from_source_run_with_loop_stmt_callback

abbrev functionsSourceDirectBlockRunScopedNonregularFromOpen :=
  @Functions.SourceDirect.Block.runScoped_nonregular_from_open

abbrev functionsSourceDirectBlockNonregularStmtRunResultFromOpen :=
  @Functions.SourceDirect.Block.block_nonregular_stmtRunResult_from_open

abbrev functionsSourceDirectBlockStmtRunBridgeFromOpenBridge :=
  @Functions.SourceDirect.Block.block_stmtRunBridge_from_open_bridge

abbrev functionsSourceDirectBlockStmtRunBridgeFromOpenBridgeWithLayout :=
  @Functions.SourceDirect.Block.block_stmtRunBridge_from_open_bridge_with_layout

abbrev functionsSourceDirectBlockStmtRunBridgeWithLayoutFromOpenBridgeWithLayout :=
  @Functions.SourceDirect.Block.block_stmtRunBridgeWithLayout_from_open_bridge_with_layout

abbrev functionsSourceDirectBlockStmtRunBridgeFromSourceRunWithLayout :=
  @Functions.SourceDirect.Block.block_stmtRunBridge_from_source_run_with_layout

abbrev functionsSourceDirectBlockStmtRunBridgeFromExactSourceRunWithLayout :=
  @Functions.SourceDirect.Block.block_stmtRunBridge_from_exact_source_run_with_layout

end SourceTowerRepair

namespace ImportedYulBoundary

abbrev loweredBridgeToBytecode :=
  @Yul.Program.compile_whole_program_result_sound_of_lowered_bridge_with_result_rel

abbrev regularRootBlockBridgeToAssembly :=
  @Yul.Program.compile_preserves_of_regular_root_block_bridge

abbrev nonregularRootBlockBridgeToAssembly :=
  @Yul.Program.compile_preserves_of_nonregular_root_block_bridge

abbrev regularDispatcherBridgeToAssembly :=
  @Yul.Program.compile_preserves_of_regular_dispatcher_bridge

abbrev regularDispatcherResultBridgeToAssembly :=
  @Yul.Program.compile_preserves_of_regular_dispatcher_result_bridge

abbrev regularDispatcherResultBridgeToBytecode :=
  @Yul.Program.compile_whole_program_result_sound_of_regular_dispatcher_result_bridge

abbrev nonregularDispatcherBridgeToAssembly :=
  @Yul.Program.compile_preserves_of_nonregular_dispatcher_bridge

abbrev nonregularDispatcherResultBridgeErrorToAssembly :=
  @Yul.Program.compile_preserves_of_nonregular_dispatcher_result_bridge_error

abbrev nonregularDispatcherResultBridgeCheckpointToAssembly :=
  @Yul.Program.compile_preserves_of_nonregular_dispatcher_result_bridge_checkpoint

abbrev nonregularDispatcherResultBridgeErrorToBytecode :=
  @Yul.Program.compile_whole_program_result_sound_of_nonregular_dispatcher_result_bridge_error

abbrev nonregularDispatcherResultBridgeCheckpointToBytecode :=
  @Yul.Program.compile_whole_program_result_sound_of_nonregular_dispatcher_result_bridge_checkpoint

/--
The clean, still-unfinished bridge record from imported Nethermind Yul runs to
the compiler-facing source tower.
-/
abbrev sourceBridge :=
  @Yul.Reference.SourceBridge

/--
Current checked imported-Yul-to-gas-aware-EVM public theorem boundary.

Unlike the legacy `sourceBridge` compatibility record above, this theorem uses
the internally constructed recursive source bridge and exposes named source
acceptedness, source-facing lower compiler resources, semantic contracts,
initial-state relation, source-run/resource, compiler-success, code-size
decode-window/jumpdest facts, and gas/current-contract assumptions. The
preferred `recursiveBridgeTopToGasAwareEVM` alias now points at the result-level
`EVM.X` theorem through the no-CALL/CREATE source-compile package: absence of
external calls is derived from accepted checked compilation, and the remaining
gas behavior is the named gas-aware runner-completeness premise for replaying
checked block traces above a finite bound.
-/
abbrev recursiveBridgeTopAssumptions :=
  @Yul.Program.RecursiveBridgeTopAssumptions

abbrev recursiveBridgeTopNoCallAssumptions :=
  @Yul.Program.RecursiveBridgeTopNoCallAssumptions

abbrev recursiveBridgeTopNoCallSourceCompileAssumptions :=
  @Yul.Program.RecursiveBridgeTopNoCallSourceCompileAssumptions

abbrev recursiveBridgeTopNoCallSourceCompileToNoCallAssumptions :=
  @Yul.Program.RecursiveBridgeTopNoCallSourceCompileAssumptions.toNoCallAssumptions

abbrev recursiveBridgeTopNoCallSourceCompileWithCanonicalObservation :=
  @Yul.Program.RecursiveBridgeTopNoCallSourceCompileAssumptions.withCanonicalObservation

abbrev recursiveBridgeTopNoCallSourceCompileSourceReferenceAccepted :=
  @Yul.Program.RecursiveBridgeTopNoCallSourceCompileAssumptions.sourceReferenceAccepted

abbrev recursiveBridgeTopNoCallSourceCompilePackageAccepted :=
  @Yul.Program.RecursiveBridgeTopNoCallSourceCompileAssumptions.sourceCompile

abbrev recursiveBridgeTopNoCallSourceCompileEmittedNoCallCreate :=
  @Yul.Program.RecursiveBridgeTopNoCallSourceCompileAssumptions.emittedNoCallCreate

abbrev recursiveBridgeTopNoCallSourceCompileTargetFitsDecodeWindow :=
  @Yul.Program.RecursiveBridgeTopNoCallSourceCompileAssumptions.targetFitsDecodeWindow

abbrev recursiveBridgeTopNoCallSourceCompileTargetJumpdestCorrect :=
  @Yul.Program.RecursiveBridgeTopNoCallSourceCompileAssumptions.targetJumpdestCorrect

abbrev recursiveBridgeTopNoCallLowerObjectCompileAccepted :=
  @Yul.Program.RecursiveBridgeTopNoCallAssumptions.lowerObjectCompileAccepted

abbrev recursiveBridgeTopNoCallSourceReferenceAccepted :=
  @Yul.Program.RecursiveBridgeTopNoCallAssumptions.sourceReferenceAccepted

abbrev recursiveBridgeTopNoCallSourceCompileAccepted :=
  @Yul.Program.RecursiveBridgeTopNoCallAssumptions.sourceCompileAccepted

abbrev recursiveBridgeTopNoCallEmittedNoCallCreate :=
  @Yul.Program.RecursiveBridgeTopNoCallAssumptions.emittedNoCallCreate

abbrev recursiveBridgeTopNoCallTargetFitsDecodeWindow :=
  @Yul.Program.RecursiveBridgeTopNoCallAssumptions.targetFitsDecodeWindow

abbrev recursiveBridgeTopNoCallTargetJumpdestCorrect :=
  @Yul.Program.RecursiveBridgeTopNoCallAssumptions.targetJumpdestCorrect

abbrev recursiveBridgeSourceAccepted :=
  @Yul.Program.RecursiveBridgeSourceAccepted

abbrev recursiveBridgeFullSourceAccepted :=
  @Yul.Program.RecursiveBridgeFullSourceAccepted

abbrev recursiveBridgeFeatureCoverage :=
  @Yul.Program.RecursiveBridgeFeatureCoverage

abbrev recursiveBridgeSourceAcceptedToFullAndCoverage :=
  @Yul.Program.RecursiveBridgeSourceAccepted.toFullAndCoverage

abbrev recursiveBridgeSourceAcceptedOfFullCoverageAndCompileChecked :=
  @Yul.Program.RecursiveBridgeSourceAccepted.ofFullCoverageAndCompileChecked

abbrev recursiveBridgeCompileResources :=
  @Yul.Program.RecursiveBridgeCompileResources

abbrev recursiveBridgeSemanticContracts :=
  @Yul.Program.RecursiveBridgeSemanticContracts

abbrev recursiveBridgeSemanticCoreContracts :=
  @Yul.Program.RecursiveBridgeSemanticCoreContracts

abbrev recursiveBridgeSemanticArityContracts :=
  @Yul.Program.RecursiveBridgeSemanticArityContracts

abbrev recursiveBridgeSemanticCoreArityContracts :=
  @Yul.Program.RecursiveBridgeSemanticCoreArityContracts

abbrev recursiveBridgePrimitiveContracts :=
  @Yul.Program.RecursiveBridgePrimitiveContracts

abbrev recursiveBridgePrimitiveStackContracts :=
  @Yul.Program.RecursiveBridgePrimitiveStackContracts

abbrev recursiveBridgePrimitiveStackArityContracts :=
  @Yul.Program.RecursiveBridgePrimitiveStackArityContracts

abbrev recursiveBridgePrimitiveStackArityContractsOfStrict :=
  @Yul.Program.RecursiveBridgePrimitiveStackArityContracts.of_strict

abbrev recursiveBridgePrimitiveArityContracts :=
  @Yul.Program.RecursiveBridgePrimitiveArityContracts

abbrev recursiveBridgePrimitiveArityContractsOfStrict :=
  @Yul.Program.RecursiveBridgePrimitiveArityContracts.of_strict

abbrev recursiveBridgePrimitiveArityContractsOfStack :=
  @Yul.Program.RecursiveBridgePrimitiveArityContracts.of_stack

abbrev recursiveBridgePrimitiveArityContractsStack :=
  @Yul.Program.RecursiveBridgePrimitiveArityContracts.stack

abbrev recursiveBridgePrimitiveContractsOfStack :=
  @Yul.Program.RecursiveBridgePrimitiveContracts.of_stack

abbrev recursiveBridgePrimitiveContractsStack :=
  @Yul.Program.RecursiveBridgePrimitiveContracts.stack

abbrev recursiveBridgeTerminalContracts :=
  @Yul.Program.RecursiveBridgeTerminalContracts

abbrev recursiveBridgeExprResultContracts :=
  @Yul.Program.RecursiveBridgeExprResultContracts

abbrev recursiveBridgeExprNoSuccessfulOutOfFuelContracts :=
  @Yul.Program.RecursiveBridgeExprNoSuccessfulOutOfFuelContracts

abbrev recursiveBridgeExprResultOfNoSuccessfulOutOfFuel :=
  @Yul.Program.RecursiveBridgeExprResultContracts.ofNoSuccessfulOutOfFuel

abbrev recursiveBridgeSemanticDispatcherOutcomeRel :=
  @Yul.Program.RecursiveBridgeSemanticContracts.dispatcherOutcomeRel

abbrev recursiveBridgeSemanticCanonicalObservation :=
  @Yul.Program.RecursiveBridgeSemanticContracts.dispatcherObservationSound_canonical

abbrev recursiveBridgeSemanticArityDispatcherOutcomeRel :=
  @Yul.Program.RecursiveBridgeSemanticArityContracts.dispatcherOutcomeRel

abbrev recursiveBridgeSemanticArityOfCanonicalObservation :=
  @Yul.Program.RecursiveBridgeSemanticArityContracts.of_canonical_observation

abbrev recursiveBridgeSemanticArityOfCanonicalObservationNoSuccessfulOutOfFuel :=
  @Yul.Program.RecursiveBridgeSemanticArityContracts.of_canonical_observation_noSuccessfulOutOfFuel

abbrev recursiveBridgeSemanticArityOfStrict :=
  @Yul.Program.RecursiveBridgeSemanticArityContracts.of_strict

abbrev recursiveBridgeSemanticCoreOfBoundaries :=
  @Yul.Program.RecursiveBridgeSemanticCoreContracts.ofBoundaries

abbrev recursiveBridgeSemanticCoreArityOfNoSuccessfulOutOfFuelBoundaries :=
  @Yul.Program.RecursiveBridgeSemanticCoreContracts.ofNoSuccessfulOutOfFuelBoundaries

abbrev recursiveBridgeSemanticCoreToContracts :=
  @Yul.Program.RecursiveBridgeSemanticCoreContracts.toSemanticContracts

abbrev recursiveBridgeSemanticCoreOfContracts :=
  @Yul.Program.RecursiveBridgeSemanticCoreContracts.ofSemanticContracts

abbrev recursiveBridgeSemanticCoreArityOfBoundaries :=
  @Yul.Program.RecursiveBridgeSemanticCoreArityContracts.ofBoundaries

abbrev recursiveBridgeSemanticCoreArityOfStrict :=
  @Yul.Program.RecursiveBridgeSemanticCoreArityContracts.of_strict

abbrev recursiveBridgeSemanticCoreArityToContracts :=
  @Yul.Program.RecursiveBridgeSemanticCoreArityContracts.toSemanticContracts

abbrev recursiveBridgeSemanticCoreArityOfContracts :=
  @Yul.Program.RecursiveBridgeSemanticCoreArityContracts.ofSemanticContracts

abbrev recursiveBridgeSourceRun :=
  @Yul.Program.RecursiveBridgeSourceRun

abbrev recursiveBridgeTargetRuntime :=
  @Yul.Program.RecursiveBridgeTargetRuntime

noncomputable abbrev recursiveBridgeCompileCheckedAssemblyTarget :=
  @Yul.Program.compileCheckedAssemblyTarget?

abbrev recursiveBridgeTopToGasAwareEVMWithRuntime :=
  @Yul.Program.compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_top

abbrev recursiveBridgeTopAssumptionsAcceptedNoCallCreate :=
  @Yul.Program.RecursiveBridgeTopAssumptions.withAcceptedNoCallCreate

abbrev recursiveBridgeTopToGasAwareEVMAcceptedNoCallCreate :=
  @Yul.Program.compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_top_withAcceptedNoCallCreate

abbrev recursiveBridgeTopNoCallToGaslessEVMResult :=
  @Yul.Program.compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall

abbrev recursiveBridgeTopToGaslessEVMResult :=
  @Yul.Program.compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall

abbrev recursiveBridgeTopNoCallToEVMX :=
  @Yul.Program.compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall_X

abbrev recursiveBridgeTopNoCallToEVMXNoOutOfGas :=
  @Yul.Program.compile_whole_program_result_no_out_of_gas_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall_X

abbrev recursiveBridgeTopNoCallSourceCompileToGasAwareEVM :=
  @Yul.Program.compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile

abbrev recursiveBridgeTopNoCallSourceCompileToEVMX :=
  @Yul.Program.compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_X

abbrev recursiveBridgeTopNoCallSourceCompileCanonicalToEVMX :=
  @Yul.Program.compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_canonical_X

abbrev recursiveBridgeTopNoCallSourceCompileCanonicalToEVMXNoOutOfGas :=
  @Yul.Program.compile_whole_program_result_no_out_of_gas_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_canonical_X

abbrev recursiveBridgeTopNoCallSourceCompileCanonicalBoundariesToEVMX :=
  @Yul.Program.compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_canonicalBoundaries_X

abbrev recursiveBridgeTopNoCallSourceCompileCanonicalBoundariesToEVMXNoOutOfGas :=
  @Yul.Program.compile_whole_program_result_no_out_of_gas_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_canonicalBoundaries_X

abbrev recursiveBridgeTopNoCallSourceCompileCanonicalResourceBoundariesToEVMX :=
  @Yul.Program.compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_canonicalResourceBoundaries_X

abbrev recursiveBridgeTopNoCallSourceCompileCanonicalResourceBoundariesToEVMXNoOutOfGas :=
  @Yul.Program.compile_whole_program_result_no_out_of_gas_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_canonicalResourceBoundaries_X

abbrev recursiveBridgeTopNoCallSourceCompileCanonicalSplitResourceBoundariesToEVMX :=
  @Yul.Program.compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_canonicalSplitResourceBoundaries_X

abbrev recursiveBridgeTopNoCallSourceCompileCanonicalSplitResourceBoundariesToEVMXNoOutOfGas :=
  @Yul.Program.compile_whole_program_result_no_out_of_gas_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_canonicalSplitResourceBoundaries_X

abbrev recursiveBridgeTopNoCallSourceCompileFullSourceCoveredCanonicalSplitResourceBoundariesToEVMX :=
  @Yul.Program.compile_whole_program_result_sound_of_fullSourceCoveredRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_canonicalSplitResourceBoundaries_X

abbrev recursiveBridgeTopNoCallSourceCompileFullSourceCoveredCanonicalSplitResourceBoundariesToEVMXNoOutOfGas :=
  @Yul.Program.compile_whole_program_result_no_out_of_gas_of_fullSourceCoveredRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_canonicalSplitResourceBoundaries_X

abbrev gasAwareXResultRunnerCompleteness :=
  @Assembly.GasAware.XResultRunnerCompleteness

abbrev gasAwareXResultRunnerCompletenessToPreconditions :=
  @Assembly.GasAware.XResultRunnerCompleteness.toPreconditions

abbrev recursiveBridgeTopNoCallSourceCompileFullSourceCoveredCanonicalSplitResourceBoundariesToEVMXRunner :=
  @Yul.Program.compile_whole_program_result_sound_of_fullSourceCoveredRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_canonicalSplitResourceBoundaries_XRunner

abbrev recursiveBridgeTopNoCallSourceCompileFullSourceCoveredCanonicalSplitResourceBoundariesToEVMXRunnerNoOutOfGas :=
  @Yul.Program.compile_whole_program_result_no_out_of_gas_of_fullSourceCoveredRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_canonicalSplitResourceBoundaries_XRunner

abbrev recursiveBridgeTopNoCallSourceCompileFullSourceCoveredStructuredPrimitiveToEVMXRunner :=
  @Yul.Program.compile_whole_program_result_sound_of_fullSourceCoveredRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_XRunner

abbrev recursiveBridgeTopNoCallSourceCompileFullSourceCoveredStructuredPrimitiveToEVMXRunnerNoOutOfGas :=
  @Yul.Program.compile_whole_program_result_no_out_of_gas_of_fullSourceCoveredRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_XRunner

abbrev recursiveBridgeTopNoCallSourceCompileFullSourceCoveredStructuredPrimitiveNoSuccessfulOutOfFuelToEVMXRunner :=
  @Yul.Program.compile_whole_program_result_sound_of_fullSourceCoveredRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitiveNoSuccessfulOutOfFuel_XRunner

abbrev recursiveBridgeTopNoCallSourceCompileFullSourceCoveredStructuredPrimitiveNoSuccessfulOutOfFuelToEVMXRunnerNoOutOfGas :=
  @Yul.Program.compile_whole_program_result_no_out_of_gas_of_fullSourceCoveredRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitiveNoSuccessfulOutOfFuel_XRunner

abbrev recursiveBridgeCanonicalEntryState :=
  @Yul.Program.canonicalEntryState

abbrev recursiveBridgeTopNoCallSourceCompileFullSourceCoveredStructuredPrimitiveCanonicalEntryToEVMXRunner :=
  @Yul.Program.compile_whole_program_result_sound_of_fullSourceCoveredRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitiveNoSuccessfulOutOfFuel_canonicalEntry_XRunner

abbrev recursiveBridgeTopNoCallSourceCompileFullSourceCoveredStructuredPrimitiveCanonicalEntryToEVMXRunnerNoOutOfGas :=
  @Yul.Program.compile_whole_program_result_no_out_of_gas_of_fullSourceCoveredRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitiveNoSuccessfulOutOfFuel_canonicalEntry_XRunner

abbrev recursiveBridgeTopNoCallToGasAwareEVM :=
  @Yul.Program.compile_whole_program_result_sound_of_fullSourceCoveredRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitiveNoSuccessfulOutOfFuel_canonicalEntry_XRunner

abbrev recursiveBridgeTopToGasAwareEVM :=
  @Yul.Program.compile_whole_program_result_sound_of_fullSourceCoveredRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitiveNoSuccessfulOutOfFuel_canonicalEntry_XRunner

abbrev functionEntryListFind :=
  @Yul.Reference.SourceBridgeFacts.FunctionEntryList.find?

abbrev yulLoweringFuelListToBlockStablePair :=
  @Yul.Reference.SourceBridgeFacts.LoweringFuel.list_toBlockFuel?_stable_pair

abbrev yulLoweringFuelListToBlockToBlock :=
  @Yul.Reference.SourceBridgeFacts.LoweringFuel.list_toBlockFuel?_toBlock?

abbrev functionEntryListToFunDefsFuelFindSome :=
  @Yul.Reference.SourceBridgeFacts.FunctionEntryList.toFunDefsFuel?_find?_some

abbrev functionEntryListBodyFuelLeFunctionListFuelOfFind :=
  @Yul.Reference.SourceBridgeFacts.FunctionEntryList.body_fuel_le_functionList_fuel_of_find?

abbrev functionEntryListFindContractFunctionEntriesOfLookup :=
  @Yul.Reference.SourceBridgeFacts.FunctionEntryList.find?_contract_functionEntries_of_lookup

abbrev functionEntryListToFunDefsFindOfContractLookup :=
  @Yul.Reference.SourceBridgeFacts.FunctionEntryList.toFunDefs?_find?_of_contract_lookup

abbrev functionEntryListToFunDefsFindOfContractLookupToBlock :=
  @Yul.Reference.SourceBridgeFacts.FunctionEntryList.toFunDefs?_find?_of_contract_lookup_toBlock?

abbrev functionEntryListToObjectsFindOfContractLookup :=
  @Yul.Reference.SourceBridgeFacts.FunctionEntryList.toObjects?_find?_of_contract_lookup

abbrev functionEntryListToObjectsFindOfContractLookupToBlock :=
  @Yul.Reference.SourceBridgeFacts.FunctionEntryList.toObjects?_find?_of_contract_lookup_toBlock?

abbrev functionEntryListToFunDefsFuelFindSomeWithFresh :=
  @Yul.Reference.SourceBridgeFacts.FunctionEntryList.toFunDefsFuel?_find?_some_with_fresh

abbrev functionEntryListToFunDefsFindOfContractLookupToBlockFresh :=
  @Yul.Reference.SourceBridgeFacts.FunctionEntryList.toFunDefs?_find?_of_contract_lookup_toBlock?_fresh

abbrev functionEntryListToObjectsFindOfContractLookupToBlockFresh :=
  @Yul.Reference.SourceBridgeFacts.FunctionEntryList.toObjects?_find?_of_contract_lookup_toBlock?_fresh

abbrev noShadowingFunctionDefinitionOfContractLookup :=
  @Yul.Reference.SourceBridgeFacts.NoShadowing.functionDefinition_of_contract_lookup

abbrev noShadowingContractLookupParamReturnFacts :=
  @Yul.Reference.SourceBridgeFacts.NoShadowing.contract_lookup_param_return_facts

abbrev userCallArityExprsOkMem :=
  @Yul.Reference.SourceBridgeFacts.UserCallArity.exprsOk_mem

abbrev userCallArityFunctionListFunctionOkOfFind :=
  @Yul.Reference.SourceBridgeFacts.UserCallArity.FunctionListOk.functionOk_of_find?

abbrev userCallArityContractLookupFunctionOk :=
  @Yul.Reference.SourceBridgeFacts.UserCallArity.contract_lookup_functionOk

abbrev userCallArityContractLookupBodyOk :=
  @Yul.Reference.SourceBridgeFacts.UserCallArity.contract_lookup_bodyOk

abbrev userCallArityProgramLookupBodyOk :=
  @Yul.Reference.SourceBridgeFacts.UserCallArity.program_lookup_bodyOk

abbrev userCallArityExprStmtUserLookupReturnsNil :=
  @Yul.Reference.SourceBridgeFacts.UserCallArity.exprStmt_user_lookup_returns_nil

abbrev userCallArityExprUserLookupReturnsLengthOne :=
  @Yul.Reference.SourceBridgeFacts.UserCallArity.expr_user_lookup_returns_length_one

abbrev userCallArityExprUserLookupArgsLength :=
  @Yul.Reference.SourceBridgeFacts.UserCallArity.expr_user_lookup_args_length

abbrev userCallArityExprStmtUserLookupArgsLength :=
  @Yul.Reference.SourceBridgeFacts.UserCallArity.exprStmt_user_lookup_args_length

abbrev userCallArityAssignUserLookupTargetsLength :=
  @Yul.Reference.SourceBridgeFacts.UserCallArity.assign_user_lookup_targets_length

abbrev userCallArityAssignUserLookupIdentNamesLength :=
  @Yul.Reference.SourceBridgeFacts.UserCallArity.assign_user_lookup_identNames_length

abbrev userCallArityAssignUserLookupArgsLength :=
  @Yul.Reference.SourceBridgeFacts.UserCallArity.assign_user_lookup_args_length

abbrev userCallArityLetUserLookupTargetsLength :=
  @Yul.Reference.SourceBridgeFacts.UserCallArity.let_user_lookup_targets_length

abbrev userCallArityLetUserLookupIdentNamesLength :=
  @Yul.Reference.SourceBridgeFacts.UserCallArity.let_user_lookup_identNames_length

abbrev userCallArityLetUserLookupArgsLength :=
  @Yul.Reference.SourceBridgeFacts.UserCallArity.let_user_lookup_args_length

abbrev sourceStoreRel :=
  @Yul.Reference.SourceBridgeFacts.SourceStoreRel

abbrev sourceStateRel :=
  @Yul.Reference.SourceBridgeFacts.SourceStateRel

abbrev sourceStateRelInsertHidden :=
  @Yul.Reference.SourceBridgeFacts.SourceStateRel.insert_hidden

abbrev sourceStateRelOfHiddenMultifill :=
  @Yul.Reference.SourceBridgeFacts.SourceStateRel.of_hidden_multifill

abbrev sourceStateExactRel :=
  @Yul.Reference.SourceBridgeFacts.SourceStateExactRel

abbrev sourceStateExactRelToRel :=
  @Yul.Reference.SourceBridgeFacts.SourceStateExactRel.toRel

abbrev sourceOkOutcomeRel :=
  @Yul.Reference.SourceBridgeFacts.SourceOkOutcomeRel

abbrev sourceResultOutcomeRel :=
  @Yul.Reference.SourceBridgeFacts.SourceResultOutcomeRel

abbrev sourceResultOutcomeRelHaltError :=
  @Yul.Reference.SourceBridgeFacts.sourceResultOutcomeRel_halt_error

abbrev sourceStoreRelNil :=
  @Yul.Reference.SourceBridgeFacts.sourceStoreRel_nil

abbrev sourceStoreRelConsInsert :=
  @Yul.Reference.SourceBridgeFacts.sourceStoreRel_cons_insert

abbrev sourceStoreRelInsertVisible :=
  @Yul.Reference.SourceBridgeFacts.sourceStoreRel_insert_visible

abbrev wordBneZeroTrueOfNe :=
  @Yul.Reference.SourceBridgeFacts.word_bne_zero_true_of_ne

abbrev wordBneZeroFalseOfEq :=
  @Yul.Reference.SourceBridgeFacts.word_bne_zero_false_of_eq

abbrev sourceSwitchSelectEqDirect :=
  @Yul.Reference.SourceBridgeFacts.source_switch_select_eq_direct

abbrev sourceSwitchSelectSomeOfDirect :=
  @Yul.Reference.SourceBridgeFacts.source_switch_select_some_of_direct

abbrev sourceSwitchSelectNoneOfDirect :=
  @Yul.Reference.SourceBridgeFacts.source_switch_select_none_of_direct

abbrev sourceStateRelNil :=
  @Yul.Reference.SourceBridgeFacts.sourceStateRel_nil

abbrev sourceStateRelRestrictCompiler :=
  @Yul.Reference.SourceBridgeFacts.sourceStateRel_restrictCompiler

abbrev sourceRegularSeqRunBridge :=
  @Yul.Reference.SourceBridgeFacts.SourceRegularSeqRunBridge

abbrev sourceRegularSeqRunBridgeHidden :=
  @Yul.Reference.SourceBridgeFacts.SourceRegularSeqRunBridgeHidden

abbrev sourceRegularSeqRunBridgeHiddenOfBridge :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularSeqRunBridgeHidden_of_bridge

abbrev generatedPrelude :=
  @Yul.Reference.SourceBridgeFacts.GeneratedPrelude

abbrev generatedPreludeRunOpenAppendRegularExists :=
  @Yul.Reference.SourceBridgeFacts.generatedPrelude_runOpen_append_regular_exists

abbrev generatedPreludeRunOpenAppendExists :=
  @Yul.Reference.SourceBridgeFacts.generatedPrelude_runOpen_append_exists

abbrev generatedPreludeRunOpenRegularPreservesContains :=
  @Yul.Reference.SourceBridgeFacts.generatedPrelude_runOpen_regular_preserves_contains

abbrev sourceRegularSeqRunBridgeHiddenConsLetExprPrelude :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularSeqRunBridgeHidden_cons_let_expr_prelude

abbrev sourceRegularSeqRunBridgeHiddenConsAssignExprPrelude :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularSeqRunBridgeHidden_cons_assign_expr_prelude

abbrev sourceRegularSeqRunAt :=
  @Yul.Reference.SourceBridgeFacts.SourceRegularSeqRunAt

abbrev sourceResultSeqRunAt :=
  @Yul.Reference.SourceBridgeFacts.SourceResultSeqRunAt

abbrev sourceRegularStmtRunAt :=
  @Yul.Reference.SourceBridgeFacts.SourceRegularStmtRunAt

abbrev sourceRegularStmtSoundAt :=
  @Yul.Reference.SourceBridgeFacts.SourceRegularStmtSoundAt

abbrev sourceRegularStmtRunAtExact :=
  @Yul.Reference.SourceBridgeFacts.SourceRegularStmtRunAtExact

abbrev sourceRegularStmtSoundAtExact :=
  @Yul.Reference.SourceBridgeFacts.SourceRegularStmtSoundAtExact

abbrev sourceNonregularStmtRunAt :=
  @Yul.Reference.SourceBridgeFacts.SourceNonregularStmtRunAt

abbrev sourceRegularSeqRunBridgeOfAt :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularSeqRunBridge_of_at

abbrev sourceRegularSeqRunExact :=
  @Yul.Reference.SourceBridgeFacts.SourceRegularSeqRunExact

abbrev sourceRegularSeqRunAtOfExact :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularSeqRunAt_of_exact

abbrev sourceResultSeqRunAtOfRegularAt :=
  @Yul.Reference.SourceBridgeFacts.sourceResultSeqRunAt_of_regular_at

abbrev sourceRegularSeqRunBridgeOfExact :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularSeqRunBridge_of_exact

abbrev sourceRegularSeqRunBridgeNil :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularSeqRunBridge_nil

abbrev sourceRegularSeqRunAtNil :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularSeqRunAt_nil

abbrev sourceResultSeqRunAtNil :=
  @Yul.Reference.SourceBridgeFacts.sourceResultSeqRunAt_nil

abbrev sourceResultSeqSoundWhenAt :=
  @Yul.Reference.SourceBridgeFacts.SourceResultSeqSoundWhenAt

abbrev sourceResultSeqSoundWhenAtFuel :=
  @Yul.Reference.SourceBridgeFacts.SourceResultSeqSoundWhenAtFuel

abbrev sourceResultSeqSoundWhenAtFuelExact :=
  @Yul.Reference.SourceBridgeFacts.SourceResultSeqSoundWhenAtFuelExact

abbrev sourceResultSeqSoundWhenAtOfFuel :=
  @Yul.Reference.SourceBridgeFacts.sourceResultSeqSoundWhenAt_of_fuel

abbrev sourceResultSeqRunAtExistsOfSoundWhenAt :=
  @Yul.Reference.SourceBridgeFacts.sourceResultSeqRunAt_exists_of_sound_when_at

abbrev sourceResultSeqSoundWhenAtNil :=
  @Yul.Reference.SourceBridgeFacts.sourceResultSeqSoundWhenAt_nil

abbrev sourceResultSeqSoundWhenAtFuelNil :=
  @Yul.Reference.SourceBridgeFacts.sourceResultSeqSoundWhenAtFuel_nil

abbrev sourceResultSeqSoundWhenAtFuelExactNil :=
  @Yul.Reference.SourceBridgeFacts.sourceResultSeqSoundWhenAtFuelExact_nil

abbrev sourceResultSeqSoundWhenAtFuelConsRegularStmt :=
  @Yul.Reference.SourceBridgeFacts.sourceResultSeqSoundWhenAtFuel_cons_regular_stmt

abbrev sourceResultSeqSoundWhenAtFuelExactConsRegularStmt :=
  @Yul.Reference.SourceBridgeFacts.sourceResultSeqSoundWhenAtFuelExact_cons_regular_stmt

abbrev sourceRegularStmtSoundAtExactAssignLitSingle :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularStmtSoundAtExact_assign_lit_single

abbrev sourceRegularStmtSoundAtExactAssignVarSingle :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularStmtSoundAtExact_assign_var_single

abbrev sourceRegularStmtSoundAtExactLetNoneSingle :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularStmtSoundAtExact_let_none_single

abbrev sourceRegularStmtSoundAtExactLetLitSingle :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularStmtSoundAtExact_let_lit_single

abbrev sourceRegularStmtSoundAtExactLetVarSingle :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularStmtSoundAtExact_let_var_single

abbrev sourceResultSeqSoundWhenAtConsBreak :=
  @Yul.Reference.SourceBridgeFacts.sourceResultSeqSoundWhenAt_cons_break

abbrev sourceResultSeqSoundWhenAtConsContinue :=
  @Yul.Reference.SourceBridgeFacts.sourceResultSeqSoundWhenAt_cons_continue

abbrev sourceResultSeqSoundWhenAtConsLeave :=
  @Yul.Reference.SourceBridgeFacts.sourceResultSeqSoundWhenAt_cons_leave

abbrev sourceResultSeqRunAtConsRegularHead :=
  @Yul.Reference.SourceBridgeFacts.sourceResultSeqRunAt_cons_regular_head

abbrev sourceResultSeqRunAtConsNonregularHead :=
  @Yul.Reference.SourceBridgeFacts.sourceResultSeqRunAt_cons_nonregular_head

abbrev sourceResultSeqRunAtConsRegularStmt :=
  @Yul.Reference.SourceBridgeFacts.sourceResultSeqRunAt_cons_regular_stmt

abbrev sourceResultSeqRunAtConsNonregularStmt :=
  @Yul.Reference.SourceBridgeFacts.sourceResultSeqRunAt_cons_nonregular_stmt

abbrev sourceResultSeqRunAtConsBreak :=
  @Yul.Reference.SourceBridgeFacts.sourceResultSeqRunAt_cons_break

abbrev sourceResultSeqRunAtConsContinue :=
  @Yul.Reference.SourceBridgeFacts.sourceResultSeqRunAt_cons_continue

abbrev sourceResultSeqRunAtConsLeave :=
  @Yul.Reference.SourceBridgeFacts.sourceResultSeqRunAt_cons_leave

abbrev sourceRegularSeqRunExactNil :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularSeqRunExact_nil

abbrev sourceRegularSeqRunBridgeConsLetNoneSingle :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularSeqRunBridge_cons_let_none_single

abbrev sourceRegularSeqRunBridgeConsLetLitSingle :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularSeqRunBridge_cons_let_lit_single

abbrev sourceRegularSeqRunBridgeConsLetVarSingle :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularSeqRunBridge_cons_let_var_single

abbrev sourceRegularSeqRunBridgeConsAssignLitSingle :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularSeqRunBridge_cons_assign_lit_single

abbrev sourceRegularSeqRunBridgeConsAssignVarSingle :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularSeqRunBridge_cons_assign_var_single

abbrev sourceRegularSeqRunAtConsLetNoneSingle :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularSeqRunAt_cons_let_none_single

abbrev sourceRegularSeqRunAtConsLetLitSingle :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularSeqRunAt_cons_let_lit_single

abbrev sourceRegularSeqRunAtConsLetVarSingle :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularSeqRunAt_cons_let_var_single

abbrev sourceRegularSeqRunAtConsLetExprSingle :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularSeqRunAt_cons_let_expr_single

abbrev sourceRegularSeqRunAtConsAssignLitSingle :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularSeqRunAt_cons_assign_lit_single

abbrev sourceRegularSeqRunAtConsAssignVarSingle :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularSeqRunAt_cons_assign_var_single

abbrev sourceRegularSeqRunAtConsAssignExprSingle :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularSeqRunAt_cons_assign_expr_single

abbrev sourceRegularSeqRunExactConsLetNoneSingle :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularSeqRunExact_cons_let_none_single

abbrev sourceRegularSeqRunExactConsLetLitSingle :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularSeqRunExact_cons_let_lit_single

abbrev sourceRegularSeqRunExactConsLetVarSingle :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularSeqRunExact_cons_let_var_single

abbrev sourceRegularSeqRunExactConsAssignLitSingle :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularSeqRunExact_cons_assign_lit_single

abbrev sourceRegularSeqRunExactConsAssignVarSingle :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularSeqRunExact_cons_assign_var_single

abbrev sourceStoreRelRestrictVarStoreOfDomain :=
  @Yul.Reference.SourceBridgeFacts.sourceStoreRel_restrictVarStore_of_domain

abbrev storeDomainExactContainsOfMem :=
  @Yul.Reference.StoreDomainExact.contains_of_mem

abbrev storeDomainExactContainsOfSubset :=
  @Yul.Reference.StoreDomainExact.contains_of_subset

abbrev sourceStoreRelRestrictVarStoreOfScopeContains :=
  @Yul.Reference.SourceBridgeFacts.sourceStoreRel_restrictVarStore_of_scope_contains

abbrev sourceStateRelRestrictStoreToOfDomain :=
  @Yul.Reference.SourceBridgeFacts.sourceStateRel_restrictStoreTo_of_domain

abbrev sourceStateRelRestrictStoreToOfScopeContains :=
  @Yul.Reference.SourceBridgeFacts.SourceStateRel.restrictStoreTo_of_scope_contains

abbrev sourceOkOutcomeRelRestrictStoreToOfScopeContains :=
  @Yul.Reference.SourceBridgeFacts.SourceOkOutcomeRel.restrictStoreTo_of_scope_contains

abbrev sourceResultOutcomeRelRestrictStoreToOfScopeContains :=
  @Yul.Reference.SourceBridgeFacts.SourceResultOutcomeRel.restrictStoreTo_of_scope_contains

abbrev sourceResultOutcomeRelRestrictStoreToOfDomainExact :=
  @Yul.Reference.SourceBridgeFacts.SourceResultOutcomeRel.restrictStoreTo_of_domain_exact

abbrev sourceOkOutcomeRelModeNeRegularOfCheckpoint :=
  @Yul.Reference.SourceBridgeFacts.SourceOkOutcomeRel.mode_ne_regular_of_checkpoint

abbrev sourceResultOutcomeRelModeNeRegularOfCheckpoint :=
  @Yul.Reference.SourceBridgeFacts.SourceResultOutcomeRel.mode_ne_regular_of_checkpoint

abbrev sourceResultOutcomeRelModeNeRegularOfError :=
  @Yul.Reference.SourceBridgeFacts.SourceResultOutcomeRel.mode_ne_regular_of_error

abbrev sourceRegularBlockRunBridge :=
  @Yul.Reference.SourceBridgeFacts.SourceRegularBlockRunBridge

abbrev sourceRegularBlockRunAt :=
  @Yul.Reference.SourceBridgeFacts.SourceRegularBlockRunAt

abbrev sourceRegularBlockRunBridgeOfAt :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularBlockRunBridge_of_at

abbrev sourceBlockRunBridge :=
  @Yul.Reference.SourceBridgeFacts.SourceBlockRunBridge

abbrev sourceResultBlockRunAt :=
  @Yul.Reference.SourceBridgeFacts.SourceResultBlockRunAt

abbrev sourceNonregularBlockRunAt :=
  @Yul.Reference.SourceBridgeFacts.SourceNonregularBlockRunAt

abbrev sourceNonregularBlockRunAtOfResultSeqRunAtCheckpoint :=
  @Yul.Reference.SourceBridgeFacts.sourceNonregularBlockRunAt_of_resultSeqRunAt_checkpoint

abbrev sourceNonregularBlockRunAtOfResultSeqRunAtError :=
  @Yul.Reference.SourceBridgeFacts.sourceNonregularBlockRunAt_of_resultSeqRunAt_error

abbrev sourceNonregularBlockRunAtOfResultSeqRunAtCheckpointDomain :=
  @Yul.Reference.SourceBridgeFacts.sourceNonregularBlockRunAt_of_resultSeqRunAt_checkpoint_domain

abbrev sourceNonregularBlockRunAtOfResultSeqRunAtErrorDomain :=
  @Yul.Reference.SourceBridgeFacts.sourceNonregularBlockRunAt_of_resultSeqRunAt_error_domain

abbrev sourceResultSeqRunAtConsBlockRegularBodyOfSeq :=
  @Yul.Reference.SourceBridgeFacts.sourceResultSeqRunAt_cons_block_regular_body_of_seq

abbrev sourceResultSeqRunAtConsBlockNonregularBodyOfResultSeqCheckpoint :=
  @Yul.Reference.SourceBridgeFacts.sourceResultSeqRunAt_cons_block_nonregular_body_of_resultSeq_checkpoint

abbrev sourceResultSeqRunAtConsBlockNonregularBodyOfResultSeqError :=
  @Yul.Reference.SourceBridgeFacts.sourceResultSeqRunAt_cons_block_nonregular_body_of_resultSeq_error

abbrev sourceResultSeqRunAtConsBlockNonregularBodyOfResultSeqCheckpointDomain :=
  @Yul.Reference.SourceBridgeFacts.sourceResultSeqRunAt_cons_block_nonregular_body_of_resultSeq_checkpoint_domain

abbrev sourceResultSeqRunAtConsBlockNonregularBodyOfResultSeqErrorDomain :=
  @Yul.Reference.SourceBridgeFacts.sourceResultSeqRunAt_cons_block_nonregular_body_of_resultSeq_error_domain

abbrev sourceBreakBlockRunAt :=
  @Yul.Reference.SourceBridgeFacts.SourceBreakBlockRunAt

abbrev sourceContinueBlockRunAt :=
  @Yul.Reference.SourceBridgeFacts.SourceContinueBlockRunAt

abbrev sourceLeaveBlockRunAt :=
  @Yul.Reference.SourceBridgeFacts.SourceLeaveBlockRunAt

abbrev sourceHaltBlockRunAt :=
  @Yul.Reference.SourceBridgeFacts.SourceHaltBlockRunAt

abbrev sourceResultBlockRunBridge :=
  @Yul.Reference.SourceBridgeFacts.SourceResultBlockRunBridge

abbrev sourceResultBlockSound :=
  @Yul.Reference.SourceBridgeFacts.SourceResultBlockSound

abbrev sourceResultBlockRunBridgeOfAt :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockRunBridge_of_at

abbrev sourceResultBlockRunAtOfRegularAt :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockRunAt_of_regular_at

abbrev exprValueSound :=
  @Yul.Reference.SourceBridgeFacts.ExprValueSound

abbrev exprValueSoundLit :=
  @Yul.Reference.SourceBridgeFacts.exprValueSound_lit

abbrev exprValueSoundVar :=
  @Yul.Reference.SourceBridgeFacts.exprValueSound_var

abbrev exprArgListSound :=
  @Yul.Reference.SourceBridgeFacts.ExprArgListSound

abbrev exprArgListSoundNil :=
  @Yul.Reference.SourceBridgeFacts.exprArgListSound_nil

abbrev exprArgListSoundSingletonLit :=
  @Yul.Reference.SourceBridgeFacts.exprArgListSound_singleton_lit

abbrev exprArgListSoundSingletonVar :=
  @Yul.Reference.SourceBridgeFacts.exprArgListSound_singleton_var

abbrev exprValueSoundPrimitiveOfArgList :=
  @Yul.Reference.SourceBridgeFacts.exprValueSound_prim_of_arg_list

abbrev exprValueSoundAddress :=
  @Yul.Reference.SourceBridgeFacts.exprValueSound_address

abbrev exprArgPreludeSound :=
  @Yul.Reference.SourceBridgeFacts.ExprArgPreludeSound

abbrev exprArgStackPreludeSound :=
  @Yul.Reference.SourceBridgeFacts.ExprArgStackPreludeSound

abbrev exprArgPreludeSoundNil :=
  @Yul.Reference.SourceBridgeFacts.exprArgPreludeSound_nil

abbrev exprArgStackPreludeSoundNil :=
  @Yul.Reference.SourceBridgeFacts.exprArgStackPreludeSound_nil

abbrev exprArgPreludeSoundSingletonLit :=
  @Yul.Reference.SourceBridgeFacts.exprArgPreludeSound_singleton_lit

abbrev exprArgStackPreludeSoundSingletonLit :=
  @Yul.Reference.SourceBridgeFacts.exprArgStackPreludeSound_singleton_lit

abbrev exprArgPreludeSoundSingletonVar :=
  @Yul.Reference.SourceBridgeFacts.exprArgPreludeSound_singleton_var

abbrev exprArgStackPreludeSoundSingletonVar :=
  @Yul.Reference.SourceBridgeFacts.exprArgStackPreludeSound_singleton_var

abbrev exprArgStackPreludeSoundPairLitLit :=
  @Yul.Reference.SourceBridgeFacts.exprArgStackPreludeSound_pair_lit_lit

abbrev exprValuePreludeSound :=
  @Yul.Reference.SourceBridgeFacts.ExprValuePreludeSound

abbrev exprEvalPreludeSoundOk :=
  @Yul.Reference.SourceBridgeFacts.ExprEvalPreludeSoundOk

abbrev primitiveStackSoundAt :=
  @Yul.Reference.SourceBridgeFacts.PrimitiveStackSoundAt

abbrev primitiveStackSoundAtArity :=
  @Yul.Reference.SourceBridgeFacts.PrimitiveStackSoundAtArity

abbrev primitiveStackSoundAtArityOfStackSoundAt :=
  @Yul.Reference.SourceBridgeFacts.primitiveStackSoundAtArity_of_stackSoundAt

abbrev yulPrimitiveBinaryOneSound :=
  @Yul.Reference.SourceBridgeFacts.YulPrimitiveBinaryOneSound

abbrev sourcePrimitiveBinaryOneSound :=
  @Yul.Reference.SourceBridgeFacts.SourcePrimitiveBinaryOneSound

abbrev primitiveStackSoundAtOfBinaryOne :=
  @Yul.Reference.SourceBridgeFacts.primitiveStackSoundAt_of_binary_one

abbrev primitiveStackSoundAtArityOfNullarySharedOne :=
  @Yul.Reference.SourceBridgeFacts.primitiveStackSoundAtArity_of_nullary_shared_one

abbrev yulPrimitiveBinaryOneSoundAdd :=
  @Yul.Reference.SourceBridgeFacts.yulPrimitiveBinaryOneSound_add

abbrev yulPrimitiveBinaryOneSoundMul :=
  @Yul.Reference.SourceBridgeFacts.yulPrimitiveBinaryOneSound_mul

abbrev yulPrimitiveBinaryOneSoundSub :=
  @Yul.Reference.SourceBridgeFacts.yulPrimitiveBinaryOneSound_sub

abbrev yulPrimitiveBinaryOneSoundDiv :=
  @Yul.Reference.SourceBridgeFacts.yulPrimitiveBinaryOneSound_div

abbrev yulPrimitiveBinaryOneSoundMod :=
  @Yul.Reference.SourceBridgeFacts.yulPrimitiveBinaryOneSound_mod

abbrev yulPrimitiveBinaryOneSoundSdiv :=
  @Yul.Reference.SourceBridgeFacts.yulPrimitiveBinaryOneSound_sdiv

abbrev yulPrimitiveBinaryOneSoundSmod :=
  @Yul.Reference.SourceBridgeFacts.yulPrimitiveBinaryOneSound_smod

abbrev yulPrimitiveBinaryOneSoundExp :=
  @Yul.Reference.SourceBridgeFacts.yulPrimitiveBinaryOneSound_exp

abbrev yulPrimitiveBinaryOneSoundSignextend :=
  @Yul.Reference.SourceBridgeFacts.yulPrimitiveBinaryOneSound_signextend

abbrev yulPrimitiveBinaryOneSoundLt :=
  @Yul.Reference.SourceBridgeFacts.yulPrimitiveBinaryOneSound_lt

abbrev yulPrimitiveBinaryOneSoundGt :=
  @Yul.Reference.SourceBridgeFacts.yulPrimitiveBinaryOneSound_gt

abbrev yulPrimitiveBinaryOneSoundSlt :=
  @Yul.Reference.SourceBridgeFacts.yulPrimitiveBinaryOneSound_slt

abbrev yulPrimitiveBinaryOneSoundSgt :=
  @Yul.Reference.SourceBridgeFacts.yulPrimitiveBinaryOneSound_sgt

abbrev yulPrimitiveBinaryOneSoundEq :=
  @Yul.Reference.SourceBridgeFacts.yulPrimitiveBinaryOneSound_eq

abbrev yulPrimitiveBinaryOneSoundAnd :=
  @Yul.Reference.SourceBridgeFacts.yulPrimitiveBinaryOneSound_and

abbrev yulPrimitiveBinaryOneSoundOr :=
  @Yul.Reference.SourceBridgeFacts.yulPrimitiveBinaryOneSound_or

abbrev yulPrimitiveBinaryOneSoundXor :=
  @Yul.Reference.SourceBridgeFacts.yulPrimitiveBinaryOneSound_xor

abbrev yulPrimitiveBinaryOneSoundByte :=
  @Yul.Reference.SourceBridgeFacts.yulPrimitiveBinaryOneSound_byte

abbrev yulPrimitiveBinaryOneSoundShl :=
  @Yul.Reference.SourceBridgeFacts.yulPrimitiveBinaryOneSound_shl

abbrev yulPrimitiveBinaryOneSoundShr :=
  @Yul.Reference.SourceBridgeFacts.yulPrimitiveBinaryOneSound_shr

abbrev yulPrimitiveBinaryOneSoundSar :=
  @Yul.Reference.SourceBridgeFacts.yulPrimitiveBinaryOneSound_sar

abbrev yulPrimitiveUnaryOneSoundIszero :=
  @Yul.Reference.SourceBridgeFacts.yulPrimitiveUnaryOneSound_iszero

abbrev yulPrimitiveUnaryOneSoundNot :=
  @Yul.Reference.SourceBridgeFacts.yulPrimitiveUnaryOneSound_not

abbrev yulPrimitiveTernaryOneSoundAddmod :=
  @Yul.Reference.SourceBridgeFacts.yulPrimitiveTernaryOneSound_addmod

abbrev yulPrimitiveTernaryOneSoundMulmod :=
  @Yul.Reference.SourceBridgeFacts.yulPrimitiveTernaryOneSound_mulmod

abbrev yulPrimitiveBinaryZeroSoundMstore :=
  @Yul.Reference.SourceBridgeFacts.yulPrimitiveBinaryZeroSound_mstore

abbrev yulPrimitiveBinaryZeroSoundMstore8 :=
  @Yul.Reference.SourceBridgeFacts.yulPrimitiveBinaryZeroSound_mstore8

abbrev yulPrimitiveTernaryZeroSoundMcopy :=
  @Yul.Reference.SourceBridgeFacts.yulPrimitiveTernaryZeroSound_mcopy

abbrev yulPrimitiveTernaryZeroSoundCalldatacopy :=
  @Yul.Reference.SourceBridgeFacts.yulPrimitiveTernaryZeroSound_calldatacopy

abbrev yulPrimitiveTernaryZeroSoundReturndatacopy :=
  @Yul.Reference.SourceBridgeFacts.yulPrimitiveTernaryZeroSound_returndatacopy

abbrev yulPrimitiveUnarySharedOneSoundMload :=
  @Yul.Reference.SourceBridgeFacts.yulPrimitiveUnarySharedOneSound_mload

abbrev sourcePrimitiveBinaryOneSoundStructuredOfBin :=
  @Yul.Reference.SourceBridgeFacts.sourcePrimitiveBinaryOneSound_structured_of_bin

abbrev sourcePrimitiveBinaryOneSoundStructuredAdd :=
  @Yul.Reference.SourceBridgeFacts.sourcePrimitiveBinaryOneSound_structured_add

abbrev sourcePrimitiveBinaryOneSoundStructuredMul :=
  @Yul.Reference.SourceBridgeFacts.sourcePrimitiveBinaryOneSound_structured_mul

abbrev sourcePrimitiveBinaryOneSoundStructuredSub :=
  @Yul.Reference.SourceBridgeFacts.sourcePrimitiveBinaryOneSound_structured_sub

abbrev sourcePrimitiveBinaryOneSoundStructuredDiv :=
  @Yul.Reference.SourceBridgeFacts.sourcePrimitiveBinaryOneSound_structured_div

abbrev sourcePrimitiveBinaryOneSoundStructuredMod :=
  @Yul.Reference.SourceBridgeFacts.sourcePrimitiveBinaryOneSound_structured_mod

abbrev sourcePrimitiveBinaryOneSoundStructuredSdiv :=
  @Yul.Reference.SourceBridgeFacts.sourcePrimitiveBinaryOneSound_structured_sdiv

abbrev sourcePrimitiveBinaryOneSoundStructuredSmod :=
  @Yul.Reference.SourceBridgeFacts.sourcePrimitiveBinaryOneSound_structured_smod

abbrev sourcePrimitiveBinaryOneSoundStructuredExp :=
  @Yul.Reference.SourceBridgeFacts.sourcePrimitiveBinaryOneSound_structured_exp

abbrev sourcePrimitiveBinaryOneSoundStructuredSignextend :=
  @Yul.Reference.SourceBridgeFacts.sourcePrimitiveBinaryOneSound_structured_signextend

abbrev sourcePrimitiveBinaryOneSoundStructuredLt :=
  @Yul.Reference.SourceBridgeFacts.sourcePrimitiveBinaryOneSound_structured_lt

abbrev sourcePrimitiveBinaryOneSoundStructuredGt :=
  @Yul.Reference.SourceBridgeFacts.sourcePrimitiveBinaryOneSound_structured_gt

abbrev sourcePrimitiveBinaryOneSoundStructuredSlt :=
  @Yul.Reference.SourceBridgeFacts.sourcePrimitiveBinaryOneSound_structured_slt

abbrev sourcePrimitiveBinaryOneSoundStructuredSgt :=
  @Yul.Reference.SourceBridgeFacts.sourcePrimitiveBinaryOneSound_structured_sgt

abbrev sourcePrimitiveBinaryOneSoundStructuredEq :=
  @Yul.Reference.SourceBridgeFacts.sourcePrimitiveBinaryOneSound_structured_eq

abbrev sourcePrimitiveBinaryOneSoundStructuredAnd :=
  @Yul.Reference.SourceBridgeFacts.sourcePrimitiveBinaryOneSound_structured_and

abbrev sourcePrimitiveBinaryOneSoundStructuredOr :=
  @Yul.Reference.SourceBridgeFacts.sourcePrimitiveBinaryOneSound_structured_or

abbrev sourcePrimitiveBinaryOneSoundStructuredXor :=
  @Yul.Reference.SourceBridgeFacts.sourcePrimitiveBinaryOneSound_structured_xor

abbrev sourcePrimitiveBinaryOneSoundStructuredByte :=
  @Yul.Reference.SourceBridgeFacts.sourcePrimitiveBinaryOneSound_structured_byte

abbrev sourcePrimitiveBinaryOneSoundStructuredShl :=
  @Yul.Reference.SourceBridgeFacts.sourcePrimitiveBinaryOneSound_structured_shl

abbrev sourcePrimitiveBinaryOneSoundStructuredShr :=
  @Yul.Reference.SourceBridgeFacts.sourcePrimitiveBinaryOneSound_structured_shr

abbrev sourcePrimitiveBinaryOneSoundStructuredSar :=
  @Yul.Reference.SourceBridgeFacts.sourcePrimitiveBinaryOneSound_structured_sar

abbrev sourcePrimitiveUnaryOneSoundStructuredOfUn :=
  @Yul.Reference.SourceBridgeFacts.sourcePrimitiveUnaryOneSound_structured_of_un

abbrev sourcePrimitiveUnaryOneSoundStructuredIszero :=
  @Yul.Reference.SourceBridgeFacts.sourcePrimitiveUnaryOneSound_structured_iszero

abbrev sourcePrimitiveUnaryOneSoundStructuredNot :=
  @Yul.Reference.SourceBridgeFacts.sourcePrimitiveUnaryOneSound_structured_not

abbrev sourcePrimitiveTernaryOneSoundStructuredOfTri :=
  @Yul.Reference.SourceBridgeFacts.sourcePrimitiveTernaryOneSound_structured_of_tri

abbrev sourcePrimitiveTernaryOneSoundStructuredAddmod :=
  @Yul.Reference.SourceBridgeFacts.sourcePrimitiveTernaryOneSound_structured_addmod

abbrev sourcePrimitiveTernaryOneSoundStructuredMulmod :=
  @Yul.Reference.SourceBridgeFacts.sourcePrimitiveTernaryOneSound_structured_mulmod

abbrev sourcePrimitiveBinaryZeroSoundStructuredOfBinaryMachineState :=
  @Yul.Reference.SourceBridgeFacts.sourcePrimitiveBinaryZeroSound_structured_of_binaryMachineState

abbrev sourcePrimitiveBinaryZeroSoundStructuredMstore :=
  @Yul.Reference.SourceBridgeFacts.sourcePrimitiveBinaryZeroSound_structured_mstore

abbrev sourcePrimitiveBinaryZeroSoundStructuredMstore8 :=
  @Yul.Reference.SourceBridgeFacts.sourcePrimitiveBinaryZeroSound_structured_mstore8

abbrev sourcePrimitiveTernaryZeroSoundStructuredOfTernaryMachineState :=
  @Yul.Reference.SourceBridgeFacts.sourcePrimitiveTernaryZeroSound_structured_of_ternaryMachineState

abbrev sourcePrimitiveTernaryZeroSoundStructuredMcopy :=
  @Yul.Reference.SourceBridgeFacts.sourcePrimitiveTernaryZeroSound_structured_mcopy

abbrev sourcePrimitiveTernaryZeroSoundStructuredOfTernaryCopy :=
  @Yul.Reference.SourceBridgeFacts.sourcePrimitiveTernaryZeroSound_structured_of_ternaryCopy

abbrev sourcePrimitiveTernaryZeroSoundStructuredCalldatacopy :=
  @Yul.Reference.SourceBridgeFacts.sourcePrimitiveTernaryZeroSound_structured_calldatacopy

abbrev sourcePrimitiveTernaryZeroSoundStructuredReturndatacopy :=
  @Yul.Reference.SourceBridgeFacts.sourcePrimitiveTernaryZeroSound_structured_returndatacopy

abbrev sourcePrimitiveUnarySharedOneSoundStructuredMload :=
  @Yul.Reference.SourceBridgeFacts.sourcePrimitiveUnarySharedOneSound_structured_mload

abbrev yulPrimitiveNullarySharedOneSoundAtArityReturndatasize :=
  @Yul.Reference.SourceBridgeFacts.yulPrimitiveNullarySharedOneSoundAtArity_returndatasize

abbrev yulPrimitiveNullarySharedOneSoundAtArityOfPrimCallOk :=
  @Yul.Reference.SourceBridgeFacts.yulPrimitiveNullarySharedOneSoundAtArity_of_primCall_ok

abbrev yulPrimitiveNullarySharedOneSoundAtArityMsize :=
  @Yul.Reference.SourceBridgeFacts.yulPrimitiveNullarySharedOneSoundAtArity_msize

abbrev yulPrimitiveNullarySharedOneSoundAtArityGas :=
  @Yul.Reference.SourceBridgeFacts.yulPrimitiveNullarySharedOneSoundAtArity_gas

abbrev sourcePrimitiveNullarySharedOneSoundStructuredOfMachineState :=
  @Yul.Reference.SourceBridgeFacts.sourcePrimitiveNullarySharedOneSound_structured_of_machineState

abbrev sourcePrimitiveNullarySharedOneSoundStructuredOfExecutionEnv :=
  @Yul.Reference.SourceBridgeFacts.sourcePrimitiveNullarySharedOneSound_structured_of_executionEnv

abbrev sourcePrimitiveNullarySharedOneSoundStructuredOfState :=
  @Yul.Reference.SourceBridgeFacts.sourcePrimitiveNullarySharedOneSound_structured_of_state

abbrev sourcePrimitiveNullarySharedOneSoundStructuredReturndatasize :=
  @Yul.Reference.SourceBridgeFacts.sourcePrimitiveNullarySharedOneSound_structured_returndatasize

abbrev sourcePrimitiveNullarySharedOneSoundStructuredMsize :=
  @Yul.Reference.SourceBridgeFacts.sourcePrimitiveNullarySharedOneSound_structured_msize

abbrev sourcePrimitiveNullarySharedOneSoundStructuredGas :=
  @Yul.Reference.SourceBridgeFacts.sourcePrimitiveNullarySharedOneSound_structured_gas

abbrev primitiveStackSoundAtStructuredAdd :=
  @Yul.Reference.SourceBridgeFacts.primitiveStackSoundAt_structured_add

abbrev primitiveStackSoundAtStructuredMul :=
  @Yul.Reference.SourceBridgeFacts.primitiveStackSoundAt_structured_mul

abbrev primitiveStackSoundAtStructuredSub :=
  @Yul.Reference.SourceBridgeFacts.primitiveStackSoundAt_structured_sub

abbrev primitiveStackSoundAtStructuredDiv :=
  @Yul.Reference.SourceBridgeFacts.primitiveStackSoundAt_structured_div

abbrev primitiveStackSoundAtStructuredMod :=
  @Yul.Reference.SourceBridgeFacts.primitiveStackSoundAt_structured_mod

abbrev primitiveStackSoundAtStructuredOfPureBin :=
  @Yul.Reference.SourceBridgeFacts.primitiveStackSoundAt_structured_of_pure_bin

abbrev primitiveStackSoundAtStructuredSdiv :=
  @Yul.Reference.SourceBridgeFacts.primitiveStackSoundAt_structured_sdiv

abbrev primitiveStackSoundAtStructuredSmod :=
  @Yul.Reference.SourceBridgeFacts.primitiveStackSoundAt_structured_smod

abbrev primitiveStackSoundAtStructuredExp :=
  @Yul.Reference.SourceBridgeFacts.primitiveStackSoundAt_structured_exp

abbrev primitiveStackSoundAtStructuredSignextend :=
  @Yul.Reference.SourceBridgeFacts.primitiveStackSoundAt_structured_signextend

abbrev primitiveStackSoundAtStructuredLt :=
  @Yul.Reference.SourceBridgeFacts.primitiveStackSoundAt_structured_lt

abbrev primitiveStackSoundAtStructuredGt :=
  @Yul.Reference.SourceBridgeFacts.primitiveStackSoundAt_structured_gt

abbrev primitiveStackSoundAtStructuredSlt :=
  @Yul.Reference.SourceBridgeFacts.primitiveStackSoundAt_structured_slt

abbrev primitiveStackSoundAtStructuredSgt :=
  @Yul.Reference.SourceBridgeFacts.primitiveStackSoundAt_structured_sgt

abbrev primitiveStackSoundAtStructuredEq :=
  @Yul.Reference.SourceBridgeFacts.primitiveStackSoundAt_structured_eq

abbrev primitiveStackSoundAtStructuredAnd :=
  @Yul.Reference.SourceBridgeFacts.primitiveStackSoundAt_structured_and

abbrev primitiveStackSoundAtStructuredOr :=
  @Yul.Reference.SourceBridgeFacts.primitiveStackSoundAt_structured_or

abbrev primitiveStackSoundAtStructuredXor :=
  @Yul.Reference.SourceBridgeFacts.primitiveStackSoundAt_structured_xor

abbrev primitiveStackSoundAtStructuredByte :=
  @Yul.Reference.SourceBridgeFacts.primitiveStackSoundAt_structured_byte

abbrev primitiveStackSoundAtStructuredShl :=
  @Yul.Reference.SourceBridgeFacts.primitiveStackSoundAt_structured_shl

abbrev primitiveStackSoundAtStructuredShr :=
  @Yul.Reference.SourceBridgeFacts.primitiveStackSoundAt_structured_shr

abbrev primitiveStackSoundAtStructuredSar :=
  @Yul.Reference.SourceBridgeFacts.primitiveStackSoundAt_structured_sar

abbrev primitiveStackSoundAtStructuredOfPureUn :=
  @Yul.Reference.SourceBridgeFacts.primitiveStackSoundAt_structured_of_pure_un

abbrev primitiveStackSoundAtStructuredIszero :=
  @Yul.Reference.SourceBridgeFacts.primitiveStackSoundAt_structured_iszero

abbrev primitiveStackSoundAtStructuredNot :=
  @Yul.Reference.SourceBridgeFacts.primitiveStackSoundAt_structured_not

abbrev primitiveStackSoundAtStructuredOfPureTri :=
  @Yul.Reference.SourceBridgeFacts.primitiveStackSoundAt_structured_of_pure_tri

abbrev primitiveStackSoundAtStructuredAddmod :=
  @Yul.Reference.SourceBridgeFacts.primitiveStackSoundAt_structured_addmod

abbrev primitiveStackSoundAtStructuredMulmod :=
  @Yul.Reference.SourceBridgeFacts.primitiveStackSoundAt_structured_mulmod

abbrev primitiveStackSoundAtStructuredMstore :=
  @Yul.Reference.SourceBridgeFacts.primitiveStackSoundAt_structured_mstore

abbrev primitiveStackSoundAtStructuredMstore8 :=
  @Yul.Reference.SourceBridgeFacts.primitiveStackSoundAt_structured_mstore8

abbrev primitiveStackSoundAtStructuredMcopy :=
  @Yul.Reference.SourceBridgeFacts.primitiveStackSoundAt_structured_mcopy

abbrev primitiveStackSoundAtStructuredCalldatacopy :=
  @Yul.Reference.SourceBridgeFacts.primitiveStackSoundAt_structured_calldatacopy

abbrev primitiveStackSoundAtStructuredReturndatacopy :=
  @Yul.Reference.SourceBridgeFacts.primitiveStackSoundAt_structured_returndatacopy

abbrev primitiveStackSoundAtStructuredMload :=
  @Yul.Reference.SourceBridgeFacts.primitiveStackSoundAt_structured_mload

abbrev primitiveStackSoundAtArityStructuredReturndatasize :=
  @Yul.Reference.SourceBridgeFacts.primitiveStackSoundAtArity_structured_returndatasize

abbrev primitiveStackSoundAtArityStructuredMsize :=
  @Yul.Reference.SourceBridgeFacts.primitiveStackSoundAtArity_structured_msize

abbrev primitiveStackSoundAtArityStructuredGas :=
  @Yul.Reference.SourceBridgeFacts.primitiveStackSoundAtArity_structured_gas

abbrev primitiveStackSoundAtArityStructuredOfNullaryExecutionEnv :=
  @Yul.Reference.SourceBridgeFacts.primitiveStackSoundAtArity_structured_of_nullary_executionEnv

abbrev primitiveStackSoundAtArityStructuredOfNullaryState :=
  @Yul.Reference.SourceBridgeFacts.primitiveStackSoundAtArity_structured_of_nullary_state

abbrev primitiveStackSoundAtArityStructuredAddress :=
  @Yul.Reference.SourceBridgeFacts.primitiveStackSoundAtArity_structured_address

abbrev primitiveStackSoundAtArityStructuredOrigin :=
  @Yul.Reference.SourceBridgeFacts.primitiveStackSoundAtArity_structured_origin

abbrev primitiveStackSoundAtArityStructuredCaller :=
  @Yul.Reference.SourceBridgeFacts.primitiveStackSoundAtArity_structured_caller

abbrev primitiveStackSoundAtArityStructuredCallvalue :=
  @Yul.Reference.SourceBridgeFacts.primitiveStackSoundAtArity_structured_callvalue

abbrev primitiveStackSoundAtArityStructuredCalldatasize :=
  @Yul.Reference.SourceBridgeFacts.primitiveStackSoundAtArity_structured_calldatasize

abbrev primitiveStackSoundAtArityStructuredGasprice :=
  @Yul.Reference.SourceBridgeFacts.primitiveStackSoundAtArity_structured_gasprice

abbrev primitiveStackSoundAtArityStructuredPrevrandao :=
  @Yul.Reference.SourceBridgeFacts.primitiveStackSoundAtArity_structured_prevrandao

abbrev primitiveStackSoundAtArityStructuredBasefee :=
  @Yul.Reference.SourceBridgeFacts.primitiveStackSoundAtArity_structured_basefee

abbrev primitiveStackSoundAtArityStructuredBlobbasefee :=
  @Yul.Reference.SourceBridgeFacts.primitiveStackSoundAtArity_structured_blobbasefee

abbrev primitiveStackSoundAtArityStructuredCoinbase :=
  @Yul.Reference.SourceBridgeFacts.primitiveStackSoundAtArity_structured_coinbase

abbrev primitiveStackSoundAtArityStructuredTimestamp :=
  @Yul.Reference.SourceBridgeFacts.primitiveStackSoundAtArity_structured_timestamp

abbrev primitiveStackSoundAtArityStructuredNumber :=
  @Yul.Reference.SourceBridgeFacts.primitiveStackSoundAtArity_structured_number

abbrev primitiveStackSoundAtArityStructuredGaslimit :=
  @Yul.Reference.SourceBridgeFacts.primitiveStackSoundAtArity_structured_gaslimit

abbrev primitiveStackSoundAtArityStructuredChainid :=
  @Yul.Reference.SourceBridgeFacts.primitiveStackSoundAtArity_structured_chainid

abbrev primitiveStackSoundAtArityStructuredSelfbalance :=
  @Yul.Reference.SourceBridgeFacts.primitiveStackSoundAtArity_structured_selfbalance

abbrev checkedBlockLoweringSound :=
  @Yul.Reference.SourceBridgeFacts.CheckedBlockLoweringSound

abbrev sourceResultBlockSoundWhen :=
  @Yul.Reference.SourceBridgeFacts.SourceResultBlockSoundWhen

abbrev sourceResultBlockSoundWhenOfSound :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSoundWhen_of_sound

abbrev sourceResultBlockRunBridgeOfSoundWhen :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockRunBridge_of_sound_when

abbrev freshCoversLayout :=
  @Yul.Reference.SourceBridgeFacts.FreshCoversLayout

abbrev freshCoversLayoutInitialSelf :=
  @Yul.Reference.SourceBridgeFacts.freshCoversLayout_initial_self

abbrev freshCoversLayoutOfSubsetContractNamesInitial :=
  @Yul.Reference.SourceBridgeFacts.freshCoversLayout_of_subset_contractNames_initial

abbrev freshCoversDispatcherNamesInitial :=
  @Yul.Reference.SourceBridgeFacts.freshCoversDispatcherNames_initial

abbrev freshCoversDispatcherNamesInitialRootLayout :=
  @Yul.Reference.SourceBridgeFacts.freshCoversDispatcherNames_initial_rootLayout

abbrev freshCoversLayoutAppendRight :=
  @Yul.Reference.SourceBridgeFacts.freshCoversLayout_append_right

abbrev freshCoversLayoutMemLeft :=
  @Yul.Reference.SourceBridgeFacts.freshCoversLayout_mem_left

abbrev freshCoversLayoutAppendConsOfMem :=
  @Yul.Reference.SourceBridgeFacts.freshCoversLayout_append_cons_of_mem

abbrev freshCoversLayoutCons :=
  @Yul.Reference.SourceBridgeFacts.freshCoversLayout_cons

abbrev freshCoversLayoutAppendLeft :=
  @Yul.Reference.SourceBridgeFacts.freshCoversLayout_append_left

abbrev freshCoversLayoutOfUsedSubset :=
  @Yul.Reference.SourceBridgeFacts.freshCoversLayout_of_used_subset

abbrev freshCoversLayoutFresh :=
  @Yul.Reference.SourceBridgeFacts.freshCoversLayout_fresh?

abbrev freshCoversLayoutLower :=
  @Yul.Reference.SourceBridgeFacts.freshCoversLayout_lower?_of_some

abbrev freshCoversLayoutLower1 :=
  @Yul.Reference.SourceBridgeFacts.freshCoversLayout_lower1?_of_some

abbrev freshCoversLayoutLower0 :=
  @Yul.Reference.SourceBridgeFacts.freshCoversLayout_lower0?_of_some

abbrev freshCoversLayoutLowerBound1 :=
  @Yul.Reference.SourceBridgeFacts.freshCoversLayout_lowerBound1?_of_some

abbrev freshCoversLayoutLowerBoundLit :=
  @Yul.Reference.SourceBridgeFacts.freshCoversLayout_lowerBound1?_lit_of_some

abbrev freshCoversLayoutLowerBoundLitLit :=
  @Yul.Reference.SourceBridgeFacts.freshCoversLayout_lowerBound1?_lit_lit_of_some

abbrev freshCoversLayoutToFunctionsListFuelOfSome :=
  @Yul.Reference.SourceBridgeFacts.freshCoversLayout_toFunctionsListFuel?_of_some

abbrev freshCoversLayoutListToFunctionsFuelOfSome :=
  @Yul.Reference.SourceBridgeFacts.freshCoversLayout_listToFunctionsFuel?_of_some

abbrev freshCoversLayoutCaseListToFunctionsFuelOfSome :=
  @Yul.Reference.SourceBridgeFacts.freshCoversLayout_caseListToFunctionsFuel?_of_some

abbrev freshCoversLayoutToBlockFuelOfSome :=
  @Yul.Reference.SourceBridgeFacts.freshCoversLayout_toBlockFuel?_of_some

abbrev checkedBlockLoweringSoundFresh :=
  @Yul.Reference.SourceBridgeFacts.CheckedBlockLoweringSoundFresh

abbrev checkedStmtBlockLoweringSound :=
  @Yul.Reference.SourceBridgeFacts.CheckedStmtBlockLoweringSound

abbrev checkedStmtBlockLoweringSoundFresh :=
  @Yul.Reference.SourceBridgeFacts.CheckedStmtBlockLoweringSoundFresh

abbrev checkedBlockLoweringSoundWhenFreshNamesAtExact :=
  @Yul.Reference.SourceBridgeFacts.CheckedBlockLoweringSoundWhenFreshNamesAtExact

abbrev checkedBlockLoweringSoundWhenFreshNamesAtExactToHiddenScope :=
  @Yul.Reference.SourceBridgeFacts.CheckedBlockLoweringSoundWhenFreshNamesAtExact.to_hiddenScope

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExact :=
  @Yul.Reference.SourceBridgeFacts.CheckedStmtBlockLoweringSoundWhenFreshNamesAtExact

abbrev checkedRegularSeqLoweringSoundWhenFreshNamesAtCompileFuelExactDomain :=
  @Yul.Reference.SourceBridgeFacts.CheckedRegularSeqLoweringSoundWhenFreshNamesAtCompileFuelExactDomain

abbrev checkedRegularStmtSingletonSoundAtExactWithNames :=
  @Yul.Reference.SourceBridgeFacts.CheckedRegularStmtSingletonSoundAtExactWithNames

abbrev checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelExact :=
  @Yul.Reference.SourceBridgeFacts.CheckedSeqLoweringSoundWhenFreshNamesAtCompileFuelExact

abbrev checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelExactNil :=
  @Yul.Reference.SourceBridgeFacts.checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelExact_nil

abbrev checkedRegularSeqLoweringSoundWhenFreshNamesAtCompileFuelExactDomainNil :=
  @Yul.Reference.SourceBridgeFacts.checkedRegularSeqLoweringSoundWhenFreshNamesAtCompileFuelExactDomain_nil

abbrev checkedBlockLoweringSoundWhen :=
  @Yul.Reference.SourceBridgeFacts.CheckedBlockLoweringSoundWhen

abbrev checkedBlockLoweringSoundWhenFresh :=
  @Yul.Reference.SourceBridgeFacts.CheckedBlockLoweringSoundWhenFresh

abbrev checkedBlockLoweringSoundWhenFreshAt :=
  @Yul.Reference.SourceBridgeFacts.CheckedBlockLoweringSoundWhenFreshAt

abbrev checkedSeqLoweringSoundWhenFreshAt :=
  @Yul.Reference.SourceBridgeFacts.CheckedSeqLoweringSoundWhenFreshAt

abbrev checkedSeqLoweringSoundWhenFreshAtCompileFuel :=
  @Yul.Reference.SourceBridgeFacts.CheckedSeqLoweringSoundWhenFreshAtCompileFuel

abbrev checkedSeqLoweringSoundWhenFreshAtCompileFuelExact :=
  @Yul.Reference.SourceBridgeFacts.CheckedSeqLoweringSoundWhenFreshAtCompileFuelExact

abbrev checkedRegularStmtSingletonSoundAt :=
  @Yul.Reference.SourceBridgeFacts.CheckedRegularStmtSingletonSoundAt

abbrev checkedRegularStmtSingletonSoundAtExact :=
  @Yul.Reference.SourceBridgeFacts.CheckedRegularStmtSingletonSoundAtExact

abbrev checkedBlockLoweringSoundWhenFreshOfAt :=
  @Yul.Reference.SourceBridgeFacts.checkedBlockLoweringSoundWhenFresh_of_at

abbrev checkedStmtBlockLoweringSoundWhen :=
  @Yul.Reference.SourceBridgeFacts.CheckedStmtBlockLoweringSoundWhen

abbrev checkedStmtBlockLoweringSoundWhenFresh :=
  @Yul.Reference.SourceBridgeFacts.CheckedStmtBlockLoweringSoundWhenFresh

abbrev checkedStmtBlockLoweringSoundWhenFreshAt :=
  @Yul.Reference.SourceBridgeFacts.CheckedStmtBlockLoweringSoundWhenFreshAt

abbrev checkedStmtBlockLoweringSoundWhenFreshOfAt :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFresh_of_at

abbrev sourceResultBlockSoundWhenNil :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSoundWhen_nil

abbrev sourceResultBlockSoundWhenAt :=
  @Yul.Reference.SourceBridgeFacts.SourceResultBlockSoundWhenAt

abbrev sourceResultBlockSoundWhenOfAt :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSoundWhen_of_at

abbrev sourceResultBlockSoundWhenAtOfWhen :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSoundWhenAt_of_when

abbrev sourceStateExactRelDomain :=
  @Yul.Reference.SourceBridgeFacts.SourceStateExactRel.domain

abbrev sourceStateExactRelOfRelDomain :=
  @Yul.Reference.SourceBridgeFacts.SourceStateExactRel.ofRelDomain

abbrev sourceStateRelContainsOfDomain :=
  @Yul.Reference.SourceBridgeFacts.SourceStateRel.contains_of_domain

abbrev sourceStateRelPreContainsOfEvalDomain :=
  @Yul.Reference.SourceBridgeFacts.SourceStateRel.preContains_of_eval_domain

abbrev sourceStateRelPreContainsOfEvalSeqDomain :=
  @Yul.Reference.SourceBridgeFacts.SourceStateRel.preContains_of_evalSeq_domain

abbrev sourceVarsContains :=
  @Yul.Reference.SourceBridgeFacts.SourceVarsContains

abbrev sourceVarsContainsOfLookupMany :=
  @Yul.Reference.SourceBridgeFacts.SourceVarsContains.of_lookupMany

abbrev sourceVarsContainsLookupManyExists :=
  @Yul.Reference.SourceBridgeFacts.SourceVarsContains.lookupMany_exists

abbrev sourceVarsContainsInsert :=
  @Yul.Reference.SourceBridgeFacts.SourceVarsContains.insert

abbrev sourceVarsContainsRestrictTo :=
  @Yul.Reference.SourceBridgeFacts.SourceVarsContains.restrictTo

abbrev sourceVarsContainsOfRestrictTo :=
  @Yul.Reference.SourceBridgeFacts.SourceVarsContains.of_restrictTo

abbrev sourceVarsContainsOfEval :=
  @Yul.Reference.SourceBridgeFacts.SourceVarsContains.of_eval

abbrev sourceVarsContainsOfEvalOne :=
  @Yul.Reference.SourceBridgeFacts.SourceVarsContains.of_evalOne

abbrev sourceVarsContainsOfEvalSeq :=
  @Yul.Reference.SourceBridgeFacts.SourceVarsContains.of_evalSeq

abbrev sourceArgListEvalVarsEq :=
  @Yul.Reference.SourceBridgeFacts.sourceArgList_eval_vars_eq

abbrev sourceVarsContainsOfArgListEval :=
  @Yul.Reference.SourceBridgeFacts.SourceVarsContains.of_argList_eval

abbrev sourceVarsContainsOfRunOpenRegular :=
  @Yul.Reference.SourceBridgeFacts.SourceVarsContains.of_runOpen_regular

abbrev sourceVarsContainsOfRunOpenRegularArgListEval :=
  @Yul.Reference.SourceBridgeFacts.SourceVarsContains.of_runOpen_regular_argList_eval

abbrev sourceVarsContainsOfRunOpenRegularArgListEvalOfInitialExact :=
  @Yul.Reference.SourceBridgeFacts.SourceVarsContains.of_runOpen_regular_argList_eval_of_initial_exact

abbrev sourceContainsPreservingPrelude :=
  Yul.Reference.SourceBridgeFacts.SourceContainsPreservingPrelude

abbrev lower1SourceContainsPreservingPrelude :=
  @Yul.Reference.SourceBridgeFacts.lower1?_sourceContainsPreservingPrelude

abbrev lowerBound1SourceContainsPreservingPrelude :=
  @Yul.Reference.SourceBridgeFacts.lowerBound1?_sourceContainsPreservingPrelude

abbrev sourceContainsPreservingPreludeRunOpenRegular :=
  @Yul.Reference.SourceBridgeFacts.sourceContainsPreservingPrelude_runOpen_regular

abbrev sourceContainsPreservingPreludeRunOpenRegularArgList :=
  @Yul.Reference.SourceBridgeFacts.sourceContainsPreservingPrelude_runOpen_regular_argList

abbrev sourceVarsContainsInsertManyPreserves :=
  @Yul.Reference.SourceBridgeFacts.SourceVarsContains.insertMany_preserves

abbrev sourceVarsContainsInitReturnsPreserves :=
  @Yul.Reference.SourceBridgeFacts.SourceVarsContains.initReturns_preserves

abbrev sourceVarsContainsAssignManyPreserves :=
  @Yul.Reference.SourceBridgeFacts.SourceVarsContains.assignMany_preserves

abbrev sourceStoreRelLookupManyEqMapLookupBang :=
  @Yul.Reference.SourceBridgeFacts.sourceStoreRel_lookupMany_eq_map_lookup!

abbrev sourceStoreRelLookupManyOfDomain :=
  @Yul.Reference.SourceBridgeFacts.sourceStoreRel_lookupMany_of_domain

abbrev sourceStoreRelLookupManyOfContains :=
  @Yul.Reference.SourceBridgeFacts.sourceStoreRel_lookupMany_of_contains

abbrev sourceStoreRelLookupManyOfSourceContains :=
  @Yul.Reference.SourceBridgeFacts.sourceStoreRel_lookupMany_of_source_contains

abbrev sourceStateRelLookupManyEqMapLookupBang :=
  @Yul.Reference.SourceBridgeFacts.sourceStateRel_lookupMany_eq_map_lookup!

abbrev sourceStateRelLookupManyOfContains :=
  @Yul.Reference.SourceBridgeFacts.sourceStateRel_lookupMany_of_contains

abbrev sourceStateRelLookupManyOfSourceContains :=
  @Yul.Reference.SourceBridgeFacts.sourceStateRel_lookupMany_of_source_contains

abbrev sourceStateExactRelLookupManyOfDomain :=
  @Yul.Reference.SourceBridgeFacts.sourceStateExactRel_lookupMany_of_domain

abbrev sourceInsertManyExistsOfLength :=
  @Yul.Reference.SourceBridgeFacts.source_insertMany_exists_of_length

abbrev sourceAssignManyExistsOfLengthContains :=
  @Yul.Reference.SourceBridgeFacts.source_assignMany_exists_of_length_contains

abbrev sourceAssignManyPreservesOfNotMem :=
  @Yul.Reference.SourceBridgeFacts.source_assignMany_preserves_of_not_mem

abbrev sourceStoreRelAssignManyInsertPairs :=
  @Yul.Reference.SourceBridgeFacts.sourceStoreRel_assignMany_insertPairs

abbrev sourceStoreRelAssignManyInsertPairsExtend :=
  @Yul.Reference.SourceBridgeFacts.sourceStoreRel_assignMany_insertPairs_extend

abbrev sourceStoreLookupManyOfRestrictToOfMem :=
  @Yul.Reference.SourceBridgeFacts.sourceStore_lookupMany_of_restrictTo_of_mem

abbrev sourceRunScopedRegularOpenLookupManyOfExact :=
  @Yul.Reference.SourceBridgeFacts.sourceRunScoped_regular_open_lookupMany_of_exact

abbrev sourceFunDefRunBodyReturnedOfRunScopedRegularExact :=
  @Yul.Reference.SourceBridgeFacts.sourceFunDef_runBody_returned_of_runScoped_regular_exact

abbrev sourceFunDefRunBodyReturnedLookupOfRunScopedRegularExact :=
  @Yul.Reference.SourceBridgeFacts.sourceFunDef_runBody_returned_lookup_of_runScoped_regular_exact

abbrev sourceFunDefRunBodyReturnedLookupOfRunScopedRegularContains :=
  @Yul.Reference.SourceBridgeFacts.sourceFunDef_runBody_returned_lookup_of_runScoped_regular_contains

abbrev sourceRunScopedLeaveEqOpen :=
  @Yul.Reference.SourceBridgeFacts.sourceRunScoped_leave_eq_open

abbrev sourceFunDefRunBodyReturnedOfRunScopedLeaveDomain :=
  @Yul.Reference.SourceBridgeFacts.sourceFunDef_runBody_returned_of_runScoped_leave_domain

abbrev sourceFunDefRunBodyReturnedLookupOfRunScopedLeaveDomain :=
  @Yul.Reference.SourceBridgeFacts.sourceFunDef_runBody_returned_lookup_of_runScoped_leave_domain

abbrev sourceFunDefRunBodyReturnedLookupOfRunScopedLeaveContains :=
  @Yul.Reference.SourceBridgeFacts.sourceFunDef_runBody_returned_lookup_of_runScoped_leave_contains

abbrev sourceFunDefRunBodyReturnedOfBodySoundOk :=
  @Yul.Reference.SourceBridgeFacts.sourceFunDef_runBody_returned_of_bodySound_ok

abbrev sourceFunDefRunBodyReturnedLookupOfBodySoundOk :=
  @Yul.Reference.SourceBridgeFacts.sourceFunDef_runBody_returned_lookup_of_bodySound_ok

abbrev sourceFunDefRunBodyReturnedLookupOfBodySoundContainsOk :=
  @Yul.Reference.SourceBridgeFacts.sourceFunDef_runBody_returned_lookup_of_bodySound_contains_ok

abbrev sourceFunDefRunBodyReturnedLookupOfBodySoundSourceOk :=
  @Yul.Reference.SourceBridgeFacts.sourceFunDef_runBody_returned_lookup_of_bodySound_source_ok

abbrev sourceStateRelUserCallNoTargetsOfRevive :=
  @Yul.Reference.SourceBridgeFacts.sourceStateRel_userCall_noTargets_of_revive

abbrev sourceStateRelUserCallTargetsOfRevive :=
  @Yul.Reference.SourceBridgeFacts.sourceStateRel_userCall_targets_of_revive

abbrev sourceStateRelUserCallLetTargetsOfRevive :=
  @Yul.Reference.SourceBridgeFacts.sourceStateRel_userCall_letTargets_of_revive

abbrev sourceOkOutcomeRelLookupManyEqMapLookupBang :=
  @Yul.Reference.SourceBridgeFacts.sourceOkOutcomeRel_lookupMany_eq_map_lookup!

abbrev sourceStateRelInitcallOfInsertMany :=
  @Yul.Reference.SourceBridgeFacts.sourceStateRel_initcall_of_insertMany

abbrev sourceStateExactRelInitcallOfInsertMany :=
  @Yul.Reference.SourceBridgeFacts.sourceStateExactRel_initcall_of_insertMany

abbrev callOkStoreEq :=
  @Yul.Reference.SourceBridgeFacts.call_ok_store_eq

abbrev callUserOkContractBody :=
  @Yul.Reference.SourceBridgeFacts.call_user_ok_contract_body

abbrev execCallUserOkContractBody :=
  @Yul.Reference.SourceBridgeFacts.execCall_user_ok_contract_body

abbrev execCallUserOkContractBodyExists :=
  @Yul.Reference.SourceBridgeFacts.execCall_user_ok_contract_body_exists

abbrev execCallUserErrorContractBodyExistsOfRelatable :=
  @Yul.Reference.SourceBridgeFacts.execCall_user_error_contract_body_exists_of_relatable

abbrev callUserErrorContractBodyExistsOfRelatable :=
  @Yul.Reference.SourceBridgeFacts.call_user_error_contract_body_exists_of_relatable

abbrev execBlockExprUserCallEvalArgsSplitOfRelatable :=
  @Yul.Reference.SourceBridgeFacts.exec_block_expr_user_call_evalArgs_split_of_relatable

abbrev execBlockExprPrimCallEvalArgsSplitOfRelatable :=
  @Yul.Reference.SourceBridgeFacts.exec_block_expr_prim_call_evalArgs_split_of_relatable

abbrev evalValuesPrimCallOkOfEvalArgsOkPrimCallOk :=
  @Yul.Reference.SourceBridgeFacts.evalValues_prim_call_ok_of_evalArgs_ok_primCall_ok

abbrev execBlockExprPrimCallErrorOfEvalArgsOkPrimCallError :=
  @Yul.Reference.SourceBridgeFacts.exec_block_expr_prim_call_error_of_evalArgs_ok_primCall_error

abbrev execBlockAssignPrimCallErrorOfEvalArgsOkPrimCallError :=
  @Yul.Reference.SourceBridgeFacts.exec_block_assign_prim_call_error_of_evalArgs_ok_primCall_error

abbrev execBlockLetPrimCallErrorOfEvalArgsOkPrimCallError :=
  @Yul.Reference.SourceBridgeFacts.exec_block_let_prim_call_error_of_evalArgs_ok_primCall_error

abbrev execBlockExprUserCallErrorBodyExistsOfEvalArgsRelatable :=
  @Yul.Reference.SourceBridgeFacts.exec_block_expr_user_call_error_body_exists_of_evalArgs_relatable

abbrev execBlockExprUserCallOkExecCallOfEvalArgs :=
  @Yul.Reference.SourceBridgeFacts.exec_block_expr_user_call_ok_execCall_of_evalArgs

abbrev execExprUserCallOkOfEvalArgsExecCall :=
  @Yul.Reference.SourceBridgeFacts.exec_expr_user_call_ok_of_evalArgs_execCall

abbrev execBlockAssignUserCallErrorBodyExistsOfEvalArgsRelatable :=
  @Yul.Reference.SourceBridgeFacts.exec_block_assign_user_call_error_body_exists_of_evalArgs_relatable

abbrev execBlockAssignUserCallEvalArgsSplitOfRelatable :=
  @Yul.Reference.SourceBridgeFacts.exec_block_assign_user_call_evalArgs_split_of_relatable

abbrev execBlockAssignPrimCallEvalArgsSplitOfRelatable :=
  @Yul.Reference.SourceBridgeFacts.exec_block_assign_prim_call_evalArgs_split_of_relatable

abbrev execBlockAssignUserCallOkPartsOfEvalArgs :=
  @Yul.Reference.SourceBridgeFacts.exec_block_assign_user_call_ok_parts_of_evalArgs

abbrev execBlockAssignUserCallOkCheckAssignmentOfEvalArgs :=
  @Yul.Reference.SourceBridgeFacts.exec_block_assign_user_call_ok_checkAssignment_of_evalArgs

abbrev execBlockAssignUserCallErrorCheckAssignmentOfEvalArgsRelatable :=
  @Yul.Reference.SourceBridgeFacts.exec_block_assign_user_call_error_checkAssignment_of_evalArgs_relatable

abbrev execBlockLetUserCallErrorBodyExistsOfEvalArgsRelatable :=
  @Yul.Reference.SourceBridgeFacts.exec_block_let_user_call_error_body_exists_of_evalArgs_relatable

abbrev execBlockLetUserCallEvalArgsSplitOfRelatable :=
  @Yul.Reference.SourceBridgeFacts.exec_block_let_user_call_evalArgs_split_of_relatable

abbrev execBlockLetPrimCallEvalArgsSplitOfRelatable :=
  @Yul.Reference.SourceBridgeFacts.exec_block_let_prim_call_evalArgs_split_of_relatable

abbrev execBlockLetUserCallOkPartsOfEvalArgs :=
  @Yul.Reference.SourceBridgeFacts.exec_block_let_user_call_ok_parts_of_evalArgs

abbrev callOkDomainExact :=
  @Yul.Reference.SourceBridgeFacts.call_ok_domain_exact

abbrev callOkStateDomainExact :=
  @Yul.Reference.SourceBridgeFacts.call_ok_state_domain_exact

abbrev callOkStateDomainExactOfState :=
  @Yul.Reference.SourceBridgeFacts.call_ok_state_domain_exact_of_state

abbrev execCallUserOkDomainExactOfArgDomain :=
  @Yul.Reference.SourceBridgeFacts.execCall_user_ok_domain_exact_of_arg_domain

abbrev storeDomainExactDeclaredOfCheckAssignmentOk :=
  @Yul.Reference.SourceBridgeFacts.storeDomainExact_declared_of_checkAssignment_ok

abbrev sourceAssignTargetsContainsOfCheckAssignmentEvalArgsDomain :=
  @Yul.Reference.SourceBridgeFacts.sourceAssignTargets_contains_of_checkAssignment_evalArgs_domain

abbrev sourceAssignTargetsContainsOfCheckAssignmentStoreContains :=
  @Yul.Reference.SourceBridgeFacts.sourceAssignTargets_contains_of_checkAssignment_store_contains

abbrev sourceAssignTargetsContainsOfCheckAssignmentStateContains :=
  @Yul.Reference.SourceBridgeFacts.sourceAssignTargets_contains_of_checkAssignment_state_contains

abbrev sourceAssignTargetsContainsOfCheckAssignmentEvalArgsExact :=
  @Yul.Reference.SourceBridgeFacts.sourceAssignTargets_contains_of_checkAssignment_evalArgs_exact

abbrev sourceAssignTargetsContainsOfCheckAssignmentRunOpenArgList :=
  @Yul.Reference.SourceBridgeFacts.sourceAssignTargets_contains_of_checkAssignment_runOpen_argList

abbrev callOkStateContainsOfState :=
  @Yul.Reference.SourceBridgeFacts.call_ok_state_contains_of_state

abbrev sourceResultStoreContains :=
  @Yul.Reference.SourceBridgeFacts.SourceResultStoreContains

abbrev sourcePairResultStoreContains :=
  @Yul.Reference.SourceBridgeFacts.SourcePairResultStoreContains

abbrev sourcePairResultStoreContainsOk :=
  @Yul.Reference.SourceBridgeFacts.SourcePairResultStoreContains.ok

abbrev sourcePairResultStoreContainsReverse :=
  @Yul.Reference.SourceBridgeFacts.SourcePairResultStoreContains.reverse'

abbrev sourcePairResultStoreContainsHead :=
  @Yul.Reference.SourceBridgeFacts.SourcePairResultStoreContains.head'

abbrev sourcePairResultStoreContainsCons :=
  @Yul.Reference.SourceBridgeFacts.SourcePairResultStoreContains.cons'

abbrev sourcePairResultStoreContainsEvalTailZero :=
  @Yul.Reference.SourceBridgeFacts.SourcePairResultStoreContains.evalTail_zero

abbrev sourcePairResultStoreContainsEvalTailSuccOfHeadTail :=
  @Yul.Reference.SourceBridgeFacts.SourcePairResultStoreContains.evalTail_succ_of_head_tail

abbrev sourcePairResultStoreContainsCallOfState :=
  @Yul.Reference.SourceBridgeFacts.SourcePairResultStoreContains.call_of_state

abbrev sourcePairResultStoreContainsStateOfOk :=
  @Yul.Reference.SourceBridgeFacts.SourcePairResultStoreContains.state_of_ok

abbrev sourceResultStoreContainsOfState :=
  @Yul.Reference.SourceBridgeFacts.SourceResultStoreContains.of_state

abbrev sourceResultStoreContainsMultifill :=
  @Yul.Reference.SourceBridgeFacts.SourceResultStoreContains.multifill'

abbrev storeDomainCallSound :=
  Yul.Reference.SourceBridgeFacts.StoreDomainCallSound

abbrev storeDomainCallSoundOfPrim :=
  @Yul.Reference.SourceBridgeFacts.StoreDomainCallSound.of_prim

abbrev storeDomainCallSoundOfPrimitiveFamilies :=
  Yul.Reference.SourceBridgeFacts.StoreDomainCallSound.of_primitive_families

abbrev storeDomainExpressionSound :=
  Yul.Reference.SourceBridgeFacts.StoreDomainExpressionSound

abbrev storeDomainExpressionSoundOfCallSound :=
  @Yul.Reference.SourceBridgeFacts.StoreDomainExpressionSound.of_callSound

abbrev storeDomainExpressionSoundOfPrimitiveFamilies :=
  Yul.Reference.SourceBridgeFacts.StoreDomainExpressionSound.of_primitive_families

abbrev storeDomainExpressionSoundEvalArgsReverseOkStoreContainsOfExact :=
  @Yul.Reference.SourceBridgeFacts.StoreDomainExpressionSound.evalArgs_reverse_ok_store_contains_of_exact

abbrev sourceResultStoreContainsLoopCheckpoint :=
  @Yul.Reference.SourceBridgeFacts.SourceResultStoreContains.loop_checkpoint

abbrev sourceResultStoreContainsExecForOfLoopInput :=
  @Yul.Reference.SourceBridgeFacts.SourceResultStoreContains.exec_for_of_loop_input

abbrev sourceResultStoreContainsLoopSuccSuccOfParts :=
  @Yul.Reference.SourceBridgeFacts.SourceResultStoreContains.loop_succ_succ_of_parts

abbrev sourceResultStoreContainsLoopSuccSuccOfOkParts :=
  @Yul.Reference.SourceBridgeFacts.SourceResultStoreContains.loop_succ_succ_of_ok_parts

abbrev evalValuesLitOkStoreEq :=
  @Yul.Reference.SourceBridgeFacts.evalValues_lit_ok_store_eq

abbrev evalValuesVarOkStoreEq :=
  @Yul.Reference.SourceBridgeFacts.evalValues_var_ok_store_eq

abbrev evalValuesLitOkDomainExact :=
  @Yul.Reference.SourceBridgeFacts.evalValues_lit_ok_domain_exact

abbrev evalValuesVarOkDomainExact :=
  @Yul.Reference.SourceBridgeFacts.evalValues_var_ok_domain_exact

abbrev evalValuesUserCallOkStoreEqOfArgStore :=
  @Yul.Reference.SourceBridgeFacts.evalValues_user_call_ok_store_eq_of_arg_store

abbrev evalValuesUserCallOkDomainExactOfArgDomain :=
  @Yul.Reference.SourceBridgeFacts.evalValues_user_call_ok_domain_exact_of_arg_domain

abbrev evalValuesUserCallOkDomainExactOfEvalOkDomain :=
  @Yul.Reference.SourceBridgeFacts.evalValues_user_call_ok_domain_exact_of_eval_ok_domain

abbrev evalValuesPrimCallOkDomainExactOfPrimStore :=
  @Yul.Reference.SourceBridgeFacts.evalValues_prim_call_ok_domain_exact_of_prim_store

abbrev primCallSafeNonOkStateEqOfOk :=
  @Yul.Reference.SourceBridgeFacts.primCall_safe_nonOk_state_eq_of_ok

abbrev primCallSafeStateDomainExactOfOk :=
  @Yul.Reference.SourceBridgeFacts.primCall_safe_state_domain_exact_of_ok

abbrev evalValuesEvalArgsStateDomainExactOfSafePrimitiveFamilies :=
  @Yul.Reference.SourceBridgeFacts.evalValues_evalArgs_state_domain_exact_of_safe_primitiveFamilies

abbrev evalValuesStateDomainExactOfSafePrimitiveFamilies :=
  @Yul.Reference.SourceBridgeFacts.evalValues_state_domain_exact_of_safe_primitiveFamilies

abbrev evalValuesPrimCallOkDomainExactOfEvalOkDomainAndPrimStore :=
  @Yul.Reference.SourceBridgeFacts.evalValues_prim_call_ok_domain_exact_of_eval_ok_domain_and_prim_store

abbrev primCallOkStoreEqOfYulPrimitiveBinaryZeroSound :=
  @Yul.Reference.SourceBridgeFacts.primCall_ok_store_eq_of_yulPrimitiveBinaryZeroSound

abbrev primCallOkStoreEqOfYulPrimitiveTernaryZeroSound :=
  @Yul.Reference.SourceBridgeFacts.primCall_ok_store_eq_of_yulPrimitiveTernaryZeroSound

abbrev evalValuesPrimCallOkDomainExactOfYulPrimitiveBinaryZeroSound :=
  @Yul.Reference.SourceBridgeFacts.evalValues_prim_call_ok_domain_exact_of_yulPrimitiveBinaryZeroSound

abbrev evalValuesPrimCallOkDomainExactOfYulPrimitiveTernaryZeroSound :=
  @Yul.Reference.SourceBridgeFacts.evalValues_prim_call_ok_domain_exact_of_yulPrimitiveTernaryZeroSound

abbrev evalValuesPrimCallOkDomainExactOfEvalOkDomainAndYulPrimitiveBinaryZeroSound :=
  @Yul.Reference.SourceBridgeFacts.evalValues_prim_call_ok_domain_exact_of_eval_ok_domain_and_yulPrimitiveBinaryZeroSound

abbrev evalValuesPrimCallOkDomainExactOfEvalOkDomainAndYulPrimitiveTernaryZeroSound :=
  @Yul.Reference.SourceBridgeFacts.evalValues_prim_call_ok_domain_exact_of_eval_ok_domain_and_yulPrimitiveTernaryZeroSound

abbrev primitiveCallStorePreservingForSafe :=
  Yul.Reference.SourceBridgeFacts.PrimitiveCallStorePreservingForSafe

abbrev primitiveCallStorePreservingForSafeOfPrimitiveFamilies :=
  @Yul.Reference.SourceBridgeFacts.PrimitiveCallStorePreservingForSafe.of_primitive_families

abbrev primitiveCallCheckpointAllowedForSafe :=
  Yul.Reference.SourceBridgeFacts.PrimitiveCallCheckpointAllowedForSafe

abbrev primitiveCallCheckpointAllowedForSafeState :=
  Yul.Reference.SourceBridgeFacts.PrimitiveCallCheckpointAllowedForSafeState

abbrev primitiveCallCheckpointAllowedForSafeNonOk :=
  Yul.Reference.SourceBridgeFacts.PrimitiveCallCheckpointAllowedForSafeNonOk

abbrev primitiveCallCheckpointAllowedForSafeOfPrimitiveFamilies :=
  @Yul.Reference.SourceBridgeFacts.PrimitiveCallCheckpointAllowedForSafe.of_primitive_families

abbrev primitiveCallCheckpointAllowedForSafeNonOkOfPrimitiveFamilies :=
  @Yul.Reference.SourceBridgeFacts.PrimitiveCallCheckpointAllowedForSafeNonOk.of_primitive_families

abbrev primitiveCallCheckpointAllowedForSafeStateOfOkAndNonOk :=
  @Yul.Reference.SourceBridgeFacts.PrimitiveCallCheckpointAllowedForSafeState.of_ok_and_nonOk

abbrev safeExprsMem :=
  @Yul.Reference.SourceBridgeFacts.safe_exprs_mem

abbrev safeExprsAppend :=
  @Yul.Reference.SourceBridgeFacts.safe_exprs_append

abbrev safeExprsReverse :=
  @Yul.Reference.SourceBridgeFacts.safe_exprs_reverse

abbrev safeExprsOfSafeExprStmtUserCall :=
  @Yul.Reference.SourceBridgeFacts.safe_exprs_of_safe_exprStmt_user_call

abbrev unsupportedFalseOfSafeExprStmtUserCall :=
  @Yul.Reference.SourceBridgeFacts.unsupported_false_of_safe_exprStmt_user_call

abbrev safeExprsOfSafeAssignUserCall :=
  @Yul.Reference.SourceBridgeFacts.safe_exprs_of_safe_assign_user_call

abbrev unsupportedFalseOfSafeAssignUserCall :=
  @Yul.Reference.SourceBridgeFacts.unsupported_false_of_safe_assign_user_call

abbrev safeExprsOfSafeLetUserCall :=
  @Yul.Reference.SourceBridgeFacts.safe_exprs_of_safe_let_user_call

abbrev unsupportedFalseOfSafeLetUserCall :=
  @Yul.Reference.SourceBridgeFacts.unsupported_false_of_safe_let_user_call

abbrev safeCasesSelectSwitchCase :=
  @Yul.Reference.SourceBridgeFacts.safe_cases_selectSwitchCase

abbrev evalValuesPrimCallOkDomainExactOfSafePrimStore :=
  @Yul.Reference.SourceBridgeFacts.evalValues_prim_call_ok_domain_exact_of_safe_prim_store

abbrev evalValuesPrimCallOkDomainExactOfSafePrimitiveFamilies :=
  @Yul.Reference.SourceBridgeFacts.evalValues_prim_call_ok_domain_exact_of_safe_primitiveFamilies

abbrev evalValuesPrimCallOkDomainExactOfEvalOkDomainAndSafePrimStore :=
  @Yul.Reference.SourceBridgeFacts.evalValues_prim_call_ok_domain_exact_of_eval_ok_domain_and_safe_prim_store

abbrev evalValuesPrimCallOkDomainExactOfEvalOkDomainAndSafePrimitiveFamilies :=
  @Yul.Reference.SourceBridgeFacts.evalValues_prim_call_ok_domain_exact_of_eval_ok_domain_and_safe_primitiveFamilies

abbrev evalLitOkStoreEq :=
  @Yul.Reference.SourceBridgeFacts.eval_lit_ok_store_eq

abbrev evalVarOkStoreEq :=
  @Yul.Reference.SourceBridgeFacts.eval_var_ok_store_eq

abbrev evalLitOkDomainExact :=
  @Yul.Reference.SourceBridgeFacts.eval_lit_ok_domain_exact

abbrev evalVarOkDomainExact :=
  @Yul.Reference.SourceBridgeFacts.eval_var_ok_domain_exact

abbrev evalUserCallOkStoreEqOfArgStore :=
  @Yul.Reference.SourceBridgeFacts.eval_user_call_ok_store_eq_of_arg_store

abbrev evalUserCallOkDomainExactOfArgDomain :=
  @Yul.Reference.SourceBridgeFacts.eval_user_call_ok_domain_exact_of_arg_domain

abbrev evalUserCallOkDomainExactOfEvalOkDomain :=
  @Yul.Reference.SourceBridgeFacts.eval_user_call_ok_domain_exact_of_eval_ok_domain

abbrev evalPrimCallOkDomainExactOfPrimStore :=
  @Yul.Reference.SourceBridgeFacts.eval_prim_call_ok_domain_exact_of_prim_store

abbrev evalPrimCallOkDomainExactOfEvalOkDomainAndPrimStore :=
  @Yul.Reference.SourceBridgeFacts.eval_prim_call_ok_domain_exact_of_eval_ok_domain_and_prim_store

abbrev evalPrimCallOkDomainExactOfSafePrimStore :=
  @Yul.Reference.SourceBridgeFacts.eval_prim_call_ok_domain_exact_of_safe_prim_store

abbrev evalPrimCallOkDomainExactOfSafePrimitiveFamilies :=
  @Yul.Reference.SourceBridgeFacts.eval_prim_call_ok_domain_exact_of_safe_primitiveFamilies

abbrev evalPrimCallOkDomainExactOfEvalOkDomainAndSafePrimStore :=
  @Yul.Reference.SourceBridgeFacts.eval_prim_call_ok_domain_exact_of_eval_ok_domain_and_safe_prim_store

abbrev evalPrimCallOkDomainExactOfEvalOkDomainAndSafePrimitiveFamilies :=
  @Yul.Reference.SourceBridgeFacts.eval_prim_call_ok_domain_exact_of_eval_ok_domain_and_safe_primitiveFamilies

abbrev evalStateDomainExactOfSafePrimitiveFamilies :=
  @Yul.Reference.SourceBridgeFacts.eval_state_domain_exact_of_safe_primitiveFamilies

abbrev evalArgsStateDomainExactOfSafePrimitiveFamilies :=
  @Yul.Reference.SourceBridgeFacts.evalArgs_state_domain_exact_of_safe_primitiveFamilies

abbrev evalArgsReverseStateDomainExactOfSafePrimitiveFamilies :=
  @Yul.Reference.SourceBridgeFacts.evalArgs_reverse_state_domain_exact_of_safe_primitiveFamilies

abbrev callOutOfFuelStateEqOfOk :=
  @Yul.Reference.SourceBridgeFacts.call_outOfFuel_state_eq_of_ok

abbrev evalOutOfFuelStateEqOfSafePrimitiveFamilies :=
  @Yul.Reference.SourceBridgeFacts.eval_outOfFuel_state_eq_of_safe_primitiveFamilies

abbrev execOutOfFuelStateEqOfSafePrimitiveFamilies :=
  @Yul.Reference.SourceBridgeFacts.exec_outOfFuel_state_eq_of_safe_primitiveFamilies

abbrev execBlockOutOfFuelStateEqOfSafePrimitiveFamilies :=
  @Yul.Reference.SourceBridgeFacts.exec_block_outOfFuel_state_eq_of_safe_primitiveFamilies

abbrev evalOkOrOutOfFuelDomainExactOfSafePrimitiveFamilies :=
  @Yul.Reference.SourceBridgeFacts.eval_ok_or_outOfFuel_domain_exact_of_safe_primitiveFamilies

abbrev evalOkOrOutOfFuelDomainContainsOfSafePrimitiveFamilies :=
  @Yul.Reference.SourceBridgeFacts.eval_ok_or_outOfFuel_domain_contains_of_safe_primitiveFamilies

abbrev evalOkDomainExactOfSafePrimitiveFamilies :=
  @Yul.Reference.SourceBridgeFacts.eval_ok_domain_exact_of_safe_primitiveFamilies

abbrev evalArgsReverseOkDomainExactOfSafePrimitiveFamilies :=
  @Yul.Reference.SourceBridgeFacts.evalArgs_reverse_ok_domain_exact_of_safe_primitiveFamilies

abbrev evalArgsOkDomainExactOfEvalOkDomain :=
  @Yul.Reference.SourceBridgeFacts.evalArgs_ok_domain_exact_of_eval_ok_domain

abbrev evalArgsReverseOkDomainExactOfEvalOkDomain :=
  @Yul.Reference.SourceBridgeFacts.evalArgs_reverse_ok_domain_exact_of_eval_ok_domain

abbrev sourceResultBlockSoundWhenAtExact :=
  @Yul.Reference.SourceBridgeFacts.SourceResultBlockSoundWhenAtExact

abbrev sourceResultBlockSoundWhenAtExactToHiddenScope :=
  @Yul.Reference.SourceBridgeFacts.SourceResultBlockSoundWhenAtExact.to_hiddenScope

abbrev sourceResultBlockSoundWhenAtExactOfExecOutOfFuel :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSoundWhenAtExact_of_exec_outOfFuel

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactOfExecOutOfFuel :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_of_exec_outOfFuel

abbrev checkedBlockLoweringSoundWhenFreshNamesAtExactOfExecOutOfFuel :=
  @Yul.Reference.SourceBridgeFacts.checkedBlockLoweringSoundWhenFreshNamesAtExact_of_exec_outOfFuel

abbrev checkedStmtBlockLoweringSoundWhenFreshAtExact :=
  @Yul.Reference.SourceBridgeFacts.CheckedStmtBlockLoweringSoundWhenFreshAtExact

abbrev checkedBlockLoweringSoundWhenFreshAtExact :=
  @Yul.Reference.SourceBridgeFacts.CheckedBlockLoweringSoundWhenFreshAtExact

abbrev sourceRegularSeqRunAtExactDomain :=
  @Yul.Reference.SourceBridgeFacts.SourceRegularSeqRunAtExactDomain

abbrev sourceRegularSeqSoundAtFuelExactDomain :=
  @Yul.Reference.SourceBridgeFacts.SourceRegularSeqSoundAtFuelExactDomain

abbrev sourceRegularSeqRunAtExactDomainNil :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularSeqRunAtExactDomain_nil

abbrev sourceRegularSeqSoundAtFuelExactDomainNil :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularSeqSoundAtFuelExactDomain_nil

abbrev sourceRegularSeqRunAtExactDomainConsRegularStmt :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularSeqRunAtExactDomain_cons_regular_stmt

abbrev sourceRegularSeqSoundAtFuelExactDomainConsRegularStmt :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularSeqSoundAtFuelExactDomain_cons_regular_stmt

abbrev sourceRegularBlockRunAtExact :=
  @Yul.Reference.SourceBridgeFacts.SourceRegularBlockRunAtExact

abbrev sourceRegularBlockRunAtExactOfResultBlockSoundOkDomain :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularBlockRunAtExact_of_resultBlockSound_ok_domain

abbrev sourceRegularBlockRunAtExactOfSeqDomain :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularBlockRunAtExact_of_seqDomain

abbrev sourceRegularStmtSoundAtExactBlockOfRegularBlock :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularStmtSoundAtExact_block_of_regular_block

abbrev sourceResultSeqSoundWhenAtFuelExactConsBlockRegularBody :=
  @Yul.Reference.SourceBridgeFacts.sourceResultSeqSoundWhenAtFuelExact_cons_block_regular_body

abbrev sourceRegularSeqSoundAtFuelExactDomainConsBlockRegularSeqDomain :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularSeqSoundAtFuelExactDomain_cons_block_regular_seqDomain

abbrev sourceResultSeqSoundWhenAtFuelExactConsBlockRegularSeqDomain :=
  @Yul.Reference.SourceBridgeFacts.sourceResultSeqSoundWhenAtFuelExact_cons_block_regular_seqDomain

abbrev sourceResultBlockSoundWhenAtExactOfRegularSeqExactDomainSame :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSoundWhenAtExact_of_regularSeqExactDomain_same

abbrev sourceResultBlockSoundWhenAtExactOfRegularSeqExactDomainCompat :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSoundWhenAtExact_of_regularSeqExactDomain_compat

abbrev checkedRegularSeqLoweringSoundWhenFreshAtCompileFuelExactDomain :=
  @Yul.Reference.SourceBridgeFacts.CheckedRegularSeqLoweringSoundWhenFreshAtCompileFuelExactDomain

abbrev checkedRegularSeqLoweringSoundWhenFreshAtCompileFuelExactDomainNil :=
  @Yul.Reference.SourceBridgeFacts.checkedRegularSeqLoweringSoundWhenFreshAtCompileFuelExactDomain_nil

abbrev checkedRegularStmtSingletonSoundAtExactBlockOfRegularSeqExactDomain :=
  @Yul.Reference.SourceBridgeFacts.checkedRegularStmtSingletonSoundAtExact_block_of_regularSeqExactDomain

abbrev checkedRegularSeqLoweringSoundWhenFreshAtCompileFuelExactDomainConsRegularStmtSingle :=
  @Yul.Reference.SourceBridgeFacts.checkedRegularSeqLoweringSoundWhenFreshAtCompileFuelExactDomain_cons_regular_stmt_single

abbrev checkedRegularSeqLoweringSoundWhenFreshAtCompileFuelParamExactDomainConsRegularStmtSingle :=
  @Yul.Reference.SourceBridgeFacts.checkedRegularSeqLoweringSoundWhenFreshAtCompileFuelParamExactDomain_cons_regular_stmt_single

abbrev checkedRegularSeqLoweringSoundWhenFreshNamesAtCompileFuelExactDomainConsRegularStmtSingle :=
  @Yul.Reference.SourceBridgeFacts.checkedRegularSeqLoweringSoundWhenFreshNamesAtCompileFuelExactDomain_cons_regular_stmt_single

abbrev checkedRegularSeqLoweringSoundWhenFreshNamesAtCompileFuelParamExactDomainConsRegularStmtSingle :=
  @Yul.Reference.SourceBridgeFacts.checkedRegularSeqLoweringSoundWhenFreshNamesAtCompileFuelParamExactDomain_cons_regular_stmt_single

abbrev checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelExactConsRegularStmtSingle :=
  @Yul.Reference.SourceBridgeFacts.checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelExact_cons_regular_stmt_single

abbrev checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelParamExactConsRegularStmtSingle :=
  @Yul.Reference.SourceBridgeFacts.checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelParamExact_cons_regular_stmt_single

abbrev checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelParamExactConsAssignLitSingle :=
  @Yul.Reference.SourceBridgeFacts.checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelParamExact_cons_assign_lit_single

abbrev checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelParamExactConsAssignVarSingle :=
  @Yul.Reference.SourceBridgeFacts.checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelParamExact_cons_assign_var_single

abbrev checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelParamExactConsLetNoneSingle :=
  @Yul.Reference.SourceBridgeFacts.checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelParamExact_cons_let_none_single

abbrev checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelParamExactConsLetLitSingle :=
  @Yul.Reference.SourceBridgeFacts.checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelParamExact_cons_let_lit_single

abbrev checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelParamExactConsLetVarSingle :=
  @Yul.Reference.SourceBridgeFacts.checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelParamExact_cons_let_var_single

abbrev checkedRegularStmtSingletonSoundAtExactWithNamesAssignLitSingle :=
  @Yul.Reference.SourceBridgeFacts.checkedRegularStmtSingletonSoundAtExactWithNames_assign_lit_single

abbrev checkedRegularSeqLoweringSoundWhenFreshNamesAtCompileFuelExactDomainConsAssignLitSingle :=
  @Yul.Reference.SourceBridgeFacts.checkedRegularSeqLoweringSoundWhenFreshNamesAtCompileFuelExactDomain_cons_assign_lit_single

abbrev checkedRegularStmtSingletonSoundAtExactWithNamesAssignVarSingle :=
  @Yul.Reference.SourceBridgeFacts.checkedRegularStmtSingletonSoundAtExactWithNames_assign_var_single

abbrev checkedRegularSeqLoweringSoundWhenFreshNamesAtCompileFuelExactDomainConsAssignVarSingle :=
  @Yul.Reference.SourceBridgeFacts.checkedRegularSeqLoweringSoundWhenFreshNamesAtCompileFuelExactDomain_cons_assign_var_single

abbrev checkedRegularSeqLoweringSoundWhenFreshAtCompileFuelExactDomainConsAssignLitSingle :=
  @Yul.Reference.SourceBridgeFacts.checkedRegularSeqLoweringSoundWhenFreshAtCompileFuelExactDomain_cons_assign_lit_single

abbrev checkedRegularSeqLoweringSoundWhenFreshAtCompileFuelParamExactDomainConsAssignLitSingle :=
  @Yul.Reference.SourceBridgeFacts.checkedRegularSeqLoweringSoundWhenFreshAtCompileFuelParamExactDomain_cons_assign_lit_single

abbrev checkedRegularSeqLoweringSoundWhenFreshAtCompileFuelExactDomainConsAssignVarSingle :=
  @Yul.Reference.SourceBridgeFacts.checkedRegularSeqLoweringSoundWhenFreshAtCompileFuelExactDomain_cons_assign_var_single

abbrev checkedRegularSeqLoweringSoundWhenFreshAtCompileFuelParamExactDomainConsAssignVarSingle :=
  @Yul.Reference.SourceBridgeFacts.checkedRegularSeqLoweringSoundWhenFreshAtCompileFuelParamExactDomain_cons_assign_var_single

abbrev checkedRegularSeqLoweringSoundWhenFreshAtCompileFuelExactDomainConsLetNoneSingle :=
  @Yul.Reference.SourceBridgeFacts.checkedRegularSeqLoweringSoundWhenFreshAtCompileFuelExactDomain_cons_let_none_single

abbrev checkedRegularSeqLoweringSoundWhenFreshAtCompileFuelParamExactDomainConsLetNoneSingle :=
  @Yul.Reference.SourceBridgeFacts.checkedRegularSeqLoweringSoundWhenFreshAtCompileFuelParamExactDomain_cons_let_none_single

abbrev checkedRegularStmtSingletonSoundAtExactWithNamesLetNoneSingle :=
  @Yul.Reference.SourceBridgeFacts.checkedRegularStmtSingletonSoundAtExactWithNames_let_none_single

abbrev checkedRegularSeqLoweringSoundWhenFreshNamesAtCompileFuelExactDomainConsLetNoneSingle :=
  @Yul.Reference.SourceBridgeFacts.checkedRegularSeqLoweringSoundWhenFreshNamesAtCompileFuelExactDomain_cons_let_none_single

abbrev checkedRegularSeqLoweringSoundWhenFreshAtCompileFuelExactDomainConsLetLitSingle :=
  @Yul.Reference.SourceBridgeFacts.checkedRegularSeqLoweringSoundWhenFreshAtCompileFuelExactDomain_cons_let_lit_single

abbrev checkedRegularSeqLoweringSoundWhenFreshAtCompileFuelParamExactDomainConsLetLitSingle :=
  @Yul.Reference.SourceBridgeFacts.checkedRegularSeqLoweringSoundWhenFreshAtCompileFuelParamExactDomain_cons_let_lit_single

abbrev checkedRegularStmtSingletonSoundAtExactWithNamesLetLitSingle :=
  @Yul.Reference.SourceBridgeFacts.checkedRegularStmtSingletonSoundAtExactWithNames_let_lit_single

abbrev checkedRegularSeqLoweringSoundWhenFreshNamesAtCompileFuelExactDomainConsLetLitSingle :=
  @Yul.Reference.SourceBridgeFacts.checkedRegularSeqLoweringSoundWhenFreshNamesAtCompileFuelExactDomain_cons_let_lit_single

abbrev checkedRegularSeqLoweringSoundWhenFreshAtCompileFuelExactDomainConsLetVarSingle :=
  @Yul.Reference.SourceBridgeFacts.checkedRegularSeqLoweringSoundWhenFreshAtCompileFuelExactDomain_cons_let_var_single

abbrev checkedRegularSeqLoweringSoundWhenFreshAtCompileFuelParamExactDomainConsLetVarSingle :=
  @Yul.Reference.SourceBridgeFacts.checkedRegularSeqLoweringSoundWhenFreshAtCompileFuelParamExactDomain_cons_let_var_single

abbrev checkedRegularStmtSingletonSoundAtExactWithNamesLetVarSingle :=
  @Yul.Reference.SourceBridgeFacts.checkedRegularStmtSingletonSoundAtExactWithNames_let_var_single

abbrev checkedRegularSeqLoweringSoundWhenFreshNamesAtCompileFuelExactDomainConsLetVarSingle :=
  @Yul.Reference.SourceBridgeFacts.checkedRegularSeqLoweringSoundWhenFreshNamesAtCompileFuelExactDomain_cons_let_var_single

abbrev checkedRegularSeqLoweringSoundWhenFreshAtCompileFuelExactDomainConsBlockRegularSeqDomain :=
  @Yul.Reference.SourceBridgeFacts.checkedRegularSeqLoweringSoundWhenFreshAtCompileFuelExactDomain_cons_block_regular_seqDomain

abbrev checkedSeqLoweringSoundWhenFreshAtCompileFuelExactConsBlockRegularSeqDomain :=
  @Yul.Reference.SourceBridgeFacts.checkedSeqLoweringSoundWhenFreshAtCompileFuelExact_cons_block_regular_seqDomain

abbrev checkedRegularSeqLoweringSoundWhenFreshAtCompileFuelExactDomainConsBlockRegularSingleton :=
  @Yul.Reference.SourceBridgeFacts.checkedRegularSeqLoweringSoundWhenFreshAtCompileFuelExactDomain_cons_block_regular_singleton

abbrev checkedSeqLoweringSoundWhenFreshAtCompileFuelExactConsBlockRegularSingleton :=
  @Yul.Reference.SourceBridgeFacts.checkedSeqLoweringSoundWhenFreshAtCompileFuelExact_cons_block_regular_singleton

abbrev checkedRegularSeqLoweringSoundWhenFreshAtCompileFuelParamExactDomainConsBlockRegularSingleton :=
  @Yul.Reference.SourceBridgeFacts.checkedRegularSeqLoweringSoundWhenFreshAtCompileFuelParamExactDomain_cons_block_regular_singleton

abbrev checkedSeqLoweringSoundWhenFreshAtCompileFuelParamExactConsBlockRegularSingleton :=
  @Yul.Reference.SourceBridgeFacts.checkedSeqLoweringSoundWhenFreshAtCompileFuelParamExact_cons_block_regular_singleton

abbrev checkedBlockLoweringSoundWhenFreshAtExactOfRegularSeqCompileFuelExactDomainSame :=
  @Yul.Reference.SourceBridgeFacts.checkedBlockLoweringSoundWhenFreshAtExact_of_regularSeqCompileFuelExactDomain_same

abbrev checkedBlockLoweringSoundWhenFreshAtExactOfRegularSeqCompileFuelExactDomainCompat :=
  @Yul.Reference.SourceBridgeFacts.checkedBlockLoweringSoundWhenFreshAtExact_of_regularSeqCompileFuelExactDomain_compat

abbrev checkedBlockLoweringSoundWhenFreshNamesAtExactOfRegularSeqCompileFuelExactDomainCompat :=
  @Yul.Reference.SourceBridgeFacts.checkedBlockLoweringSoundWhenFreshNamesAtExact_of_regularSeqCompileFuelExactDomain_compat

abbrev checkedBlockLoweringSoundWhenFreshNamesAtExactOfSeqCompileFuelExactSame :=
  @Yul.Reference.SourceBridgeFacts.checkedBlockLoweringSoundWhenFreshNamesAtExact_of_seqCompileFuelExact_same

abbrev checkedBlockLoweringSoundWhenFreshNamesAtExactOfSeqCompileFuelExactCompat :=
  @Yul.Reference.SourceBridgeFacts.checkedBlockLoweringSoundWhenFreshNamesAtExact_of_seqCompileFuelExact_compat

abbrev checkedBlockLoweringSoundWhenFreshNamesAtExactOfSeqCompileFuelParamExactSame :=
  @Yul.Reference.SourceBridgeFacts.checkedBlockLoweringSoundWhenFreshNamesAtExact_of_seqCompileFuelParamExact_same

abbrev checkedBlockLoweringSoundWhenFreshNamesAtExactOfSeqCompileFuelParamExactCompat :=
  @Yul.Reference.SourceBridgeFacts.checkedBlockLoweringSoundWhenFreshNamesAtExact_of_seqCompileFuelParamExact_compat

abbrev checkedBlockLoweringSoundWhenFreshNamesAtExactConsRegularStmtSingleOfSeqTail :=
  @Yul.Reference.SourceBridgeFacts.checkedBlockLoweringSoundWhenFreshNamesAtExact_cons_regular_stmt_single_of_seq_tail

abbrev checkedBlockLoweringSoundWhenFreshAtExactOfRegularSeqCompileFuelParamExactDomainSame :=
  @Yul.Reference.SourceBridgeFacts.checkedBlockLoweringSoundWhenFreshAtExact_of_regularSeqCompileFuelParamExactDomain_same

abbrev checkedBlockLoweringSoundWhenFreshAtExactOfRegularSeqCompileFuelParamExactDomainCompat :=
  @Yul.Reference.SourceBridgeFacts.checkedBlockLoweringSoundWhenFreshAtExact_of_regularSeqCompileFuelParamExactDomain_compat

abbrev sourceStateExactRelOfInitialScopeDefault :=
  @Yul.Reference.SourceBridgeFacts.SourceStateExactRel.of_initial_scope_default

abbrev storeDomainExactRestrictVarStoreOfDomain :=
  @Yul.Reference.SourceBridgeFacts.StoreDomainExact.restrictVarStore_of_domain

abbrev sourceStateExactRelRestrictStoreToOfDomain :=
  @Yul.Reference.SourceBridgeFacts.SourceStateExactRel.restrictStoreTo_of_domain

abbrev sourceResultOutcomeLayoutCompatible :=
  @Yul.Reference.SourceBridgeFacts.SourceResultOutcomeLayoutCompatible

abbrev sourceResultOutcomeLayoutCompatibleRestrictStoreTo :=
  @Yul.Reference.SourceBridgeFacts.SourceResultOutcomeLayoutCompatible.restrictStoreTo

abbrev sourceResultOutcomeLayoutCompatibleOfRestrictStoreTo :=
  @Yul.Reference.SourceBridgeFacts.SourceResultOutcomeLayoutCompatible.of_restrictStoreTo

abbrev recursiveSourceBridgeWhenUpToAtExact :=
  @Yul.Reference.SourceBridgeFacts.RecursiveSourceBridgeWhenUpToAtExact

abbrev recursiveSourceBridgeWhenUpToAtExactCompat :=
  @Yul.Reference.SourceBridgeFacts.RecursiveSourceBridgeWhenUpToAtExactCompat

abbrev recursiveSourceBridgeWhenUpToAtExactCompatNames :=
  @Yul.Reference.SourceBridgeFacts.RecursiveSourceBridgeWhenUpToAtExactCompatNames

abbrev programRecursiveSourceBridgeWhenUpToAtExactCompatNames :=
  @Yul.Reference.SourceBridgeFacts.ProgramRecursiveSourceBridgeWhenUpToAtExactCompatNames

abbrev programBridgeContext :=
  @Yul.Reference.SourceBridgeFacts.ProgramBridgeContext

abbrev programBridgeContextDispatcherFacts :=
  @Yul.Reference.SourceBridgeFacts.ProgramBridgeContext.dispatcher_facts

abbrev programBridgeContextFunctionBodyFactsOfLookup :=
  @Yul.Reference.SourceBridgeFacts.ProgramBridgeContext.function_body_facts_of_lookup

abbrev programBridgeContextDispatcherSourceScoped :=
  @Yul.Reference.SourceBridgeFacts.ProgramBridgeContext.dispatcher_source_scoped

abbrev programBridgeContextFunctionBodySourceScopedOfLookup :=
  @Yul.Reference.SourceBridgeFacts.ProgramBridgeContext.function_body_source_scoped_of_lookup

abbrev programBridgeContextFunctionBodySourceScopedOfLookupLower :=
  @Yul.Reference.SourceBridgeFacts.ProgramBridgeContext.function_body_source_scoped_of_lookup_lower

abbrev sourceLexicalStmtScoped :=
  @Yul.Reference.SourceBridgeFacts.SourceLexical.StmtScoped

abbrev sourceLexicalStmtsScoped :=
  @Yul.Reference.SourceBridgeFacts.SourceLexical.StmtsScoped

abbrev sourceLexicalProgramScoped :=
  @Yul.Reference.SourceBridgeFacts.SourceLexical.ProgramScoped

abbrev sourceLexicalExprStmtUserCallArgs :=
  @Yul.Reference.SourceBridgeFacts.SourceLexical.exprStmt_user_call_args

abbrev sourceLexicalAssignUserCallArgs :=
  @Yul.Reference.SourceBridgeFacts.SourceLexical.assign_user_call_args

abbrev sourceLexicalLetUserCallArgs :=
  @Yul.Reference.SourceBridgeFacts.SourceLexical.let_user_call_args

abbrev sourceLexicalAssignNamesNodup :=
  @Yul.Reference.SourceBridgeFacts.SourceLexical.assign_names_nodup

abbrev sourceLexicalAssignNamesMem :=
  @Yul.Reference.SourceBridgeFacts.SourceLexical.assign_names_mem

abbrev sourceLexicalAssignValueScoped :=
  @Yul.Reference.SourceBridgeFacts.SourceLexical.assign_value_scoped

abbrev sourceLexicalLetNoneNamesNodup :=
  @Yul.Reference.SourceBridgeFacts.SourceLexical.let_none_names_nodup

abbrev sourceLexicalLetNoneNamesFresh :=
  @Yul.Reference.SourceBridgeFacts.SourceLexical.let_none_names_fresh

abbrev sourceLexicalLetSomeNamesNodup :=
  @Yul.Reference.SourceBridgeFacts.SourceLexical.let_some_names_nodup

abbrev sourceLexicalLetSomeNamesFresh :=
  @Yul.Reference.SourceBridgeFacts.SourceLexical.let_some_names_fresh

abbrev sourceLexicalLetSomeValueScoped :=
  @Yul.Reference.SourceBridgeFacts.SourceLexical.let_some_value_scoped

abbrev sourceLexicalIfCondScoped :=
  @Yul.Reference.SourceBridgeFacts.SourceLexical.if_cond_scoped

abbrev sourceLexicalIfBodyScoped :=
  @Yul.Reference.SourceBridgeFacts.SourceLexical.if_body_scoped

abbrev sourceLexicalSwitchScrutineeScoped :=
  @Yul.Reference.SourceBridgeFacts.SourceLexical.switch_scrutinee_scoped

abbrev sourceLexicalSwitchCasesScoped :=
  @Yul.Reference.SourceBridgeFacts.SourceLexical.switch_cases_scoped

abbrev sourceLexicalSwitchDefaultScoped :=
  @Yul.Reference.SourceBridgeFacts.SourceLexical.switch_default_scoped

abbrev sourceLexicalCasesScopedSelectSwitchCase :=
  @Yul.Reference.SourceBridgeFacts.SourceLexical.casesScoped_selectSwitchCase

abbrev sourceLexicalSwitchSelectedScoped :=
  @Yul.Reference.SourceBridgeFacts.SourceLexical.switch_selected_scoped

abbrev sourceLexicalForCondScoped :=
  @Yul.Reference.SourceBridgeFacts.SourceLexical.for_cond_scoped

abbrev sourceLexicalForPostScoped :=
  @Yul.Reference.SourceBridgeFacts.SourceLexical.for_post_scoped

abbrev sourceLexicalForBodyScoped :=
  @Yul.Reference.SourceBridgeFacts.SourceLexical.for_body_scoped

abbrev programAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNames :=
  @Yul.Reference.SourceBridgeFacts.ProgramAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNames

abbrev programAcceptedRecursiveSourceBridgeAtExactFuelCompatNames :=
  @Yul.Reference.SourceBridgeFacts.ProgramAcceptedRecursiveSourceBridgeAtExactFuelCompatNames

abbrev recursiveSourceBridgeWhenUpToAtExactZero :=
  @Yul.Reference.SourceBridgeFacts.recursiveSourceBridgeWhenUpToAtExact_zero

abbrev recursiveSourceBridgeWhenUpToAtExactCompatZero :=
  @Yul.Reference.SourceBridgeFacts.recursiveSourceBridgeWhenUpToAtExactCompat_zero

abbrev recursiveSourceBridgeWhenUpToAtExactCompatNamesZero :=
  @Yul.Reference.SourceBridgeFacts.recursiveSourceBridgeWhenUpToAtExactCompatNames_zero

abbrev programRecursiveSourceBridgeWhenUpToAtExactCompatNamesZero :=
  @Yul.Reference.SourceBridgeFacts.programRecursiveSourceBridgeWhenUpToAtExactCompatNames_zero

abbrev programAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNamesZero :=
  @Yul.Reference.SourceBridgeFacts.programAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNames_zero

abbrev recursiveSourceBridgeWhenUpToAtExactMono :=
  @Yul.Reference.SourceBridgeFacts.RecursiveSourceBridgeWhenUpToAtExact.mono

abbrev recursiveSourceBridgeWhenUpToAtExactCompatMono :=
  @Yul.Reference.SourceBridgeFacts.RecursiveSourceBridgeWhenUpToAtExactCompat.mono

abbrev recursiveSourceBridgeWhenUpToAtExactCompatNamesMono :=
  @Yul.Reference.SourceBridgeFacts.RecursiveSourceBridgeWhenUpToAtExactCompatNames.mono

abbrev programRecursiveSourceBridgeWhenUpToAtExactCompatNamesMono :=
  @Yul.Reference.SourceBridgeFacts.ProgramRecursiveSourceBridgeWhenUpToAtExactCompatNames.mono

abbrev programAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNamesMono :=
  @Yul.Reference.SourceBridgeFacts.ProgramAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNames.mono

abbrev programAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNamesSuccOfAtExactFuel :=
  @Yul.Reference.SourceBridgeFacts.ProgramAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNames.succ_of_atExactFuel

abbrev programAcceptedRecursiveSourceBridgeAtExactFuelCompatNamesOfWhenUpTo :=
  @Yul.Reference.SourceBridgeFacts.ProgramAcceptedRecursiveSourceBridgeAtExactFuelCompatNames.of_whenUpTo

abbrev programAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNamesBlockOfFunctionLookup :=
  @Yul.Reference.SourceBridgeFacts.ProgramAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNames.block_of_function_lookup

abbrev recursiveSourceBridgeWhenUpToAtExactToCompat :=
  @Yul.Reference.SourceBridgeFacts.RecursiveSourceBridgeWhenUpToAtExact.to_compat

abbrev recursiveSourceBridgeWhenUpToAtExactCompatToNames :=
  @Yul.Reference.SourceBridgeFacts.RecursiveSourceBridgeWhenUpToAtExactCompat.to_names

abbrev sourceResultOutcomeLayoutCompatibleBodyCtxSameOfCheckpoint :=
  @Yul.Reference.SourceBridgeFacts.sourceResultOutcomeLayoutCompatible_bodyCtx_same_of_checkpoint

abbrev sourceResultBlockSoundWhenAtExactOfRecursiveActualOk :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSoundWhenAtExact_of_recursive_actual_ok

abbrev sourceResultBlockSoundWhenAtExactOfRecursiveActualError :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSoundWhenAtExact_of_recursive_actual_error

abbrev sourceResultBlockSoundWhenAtExactOfProgramRecursiveActualOk :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSoundWhenAtExact_of_program_recursive_actual_ok

abbrev sourceResultBlockSoundWhenAtExactOfProgramRecursiveActualError :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSoundWhenAtExact_of_program_recursive_actual_error

abbrev sourceResultBlockSoundWhenAtExactOfProgramAcceptedRecursiveActualOk :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSoundWhenAtExact_of_program_accepted_recursive_actual_ok

abbrev sourceResultBlockSoundWhenAtExactOfProgramAcceptedRecursiveActualError :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSoundWhenAtExact_of_program_accepted_recursive_actual_error

abbrev sourceFunDefRunBodyReturnedLookupOfRecursiveActualOk :=
  @Yul.Reference.SourceBridgeFacts.sourceFunDef_runBody_returned_lookup_of_recursive_actual_ok

abbrev sourceFunDefRunBodyReturnedLookupOfRecursiveActualContainsOk :=
  @Yul.Reference.SourceBridgeFacts.sourceFunDef_runBody_returned_lookup_of_recursive_actual_contains_ok

abbrev sourceFunDefRunBodyReturnedLookupOfRecursiveActualSourceOk :=
  @Yul.Reference.SourceBridgeFacts.sourceFunDef_runBody_returned_lookup_of_recursive_actual_source_ok

abbrev sourceFunDefRunBodyHaltedOfRecursiveActualError :=
  @Yul.Reference.SourceBridgeFacts.sourceFunDef_runBody_halted_of_recursive_actual_error

abbrev sourceFunDefRunBodyReturnedLookupOfProgramRecursiveActualOk :=
  @Yul.Reference.SourceBridgeFacts.sourceFunDef_runBody_returned_lookup_of_program_recursive_actual_ok

abbrev sourceFunDefRunBodyReturnedLookupOfProgramRecursiveActualContainsOk :=
  @Yul.Reference.SourceBridgeFacts.sourceFunDef_runBody_returned_lookup_of_program_recursive_actual_contains_ok

abbrev sourceFunDefRunBodyReturnedLookupOfProgramRecursiveActualSourceOk :=
  @Yul.Reference.SourceBridgeFacts.sourceFunDef_runBody_returned_lookup_of_program_recursive_actual_source_ok

abbrev sourceFunDefRunBodyHaltedOfProgramRecursiveActualError :=
  @Yul.Reference.SourceBridgeFacts.sourceFunDef_runBody_halted_of_program_recursive_actual_error

abbrev sourceFunDefRunBodyReturnedLookupOfProgramAcceptedRecursiveActualSourceOk :=
  @Yul.Reference.SourceBridgeFacts.sourceFunDef_runBody_returned_lookup_of_program_accepted_recursive_actual_source_ok

abbrev sourceFunDefRunBodyHaltedOfProgramAcceptedRecursiveActualError :=
  @Yul.Reference.SourceBridgeFacts.sourceFunDef_runBody_halted_of_program_accepted_recursive_actual_error

abbrev sourceNoTargetUserCallRegularOfExecCallRecursive :=
  @Yul.Reference.SourceBridgeFacts.sourceNoTargetUserCall_regular_of_execCall_recursive

abbrev sourceNoTargetUserCallRegularOfExecCallProgramRecursive :=
  @Yul.Reference.SourceBridgeFacts.sourceNoTargetUserCall_regular_of_execCall_program_recursive

abbrev sourceNoTargetUserCallRegularOfExecCallProgramAcceptedRecursive :=
  @Yul.Reference.SourceBridgeFacts.sourceNoTargetUserCall_regular_of_execCall_program_accepted_recursive

abbrev sourceUserCallTerminalOfRecursiveError :=
  @Yul.Reference.SourceBridgeFacts.sourceUserCall_terminal_of_recursive_error

abbrev sourceUserCallTerminalOfProgramRecursiveError :=
  @Yul.Reference.SourceBridgeFacts.sourceUserCall_terminal_of_program_recursive_error

abbrev sourceUserCallTerminalOfProgramAcceptedRecursiveError :=
  @Yul.Reference.SourceBridgeFacts.sourceUserCall_terminal_of_program_accepted_recursive_error

abbrev sourceExprPreludeTerminalAtUserCallGeneratedOfProgramAcceptedRecursiveError :=
  @Yul.Reference.SourceBridgeFacts.sourceExprPreludeTerminalAt_user_call_generated_of_program_accepted_recursive_error

abbrev sourceExprPreludeTerminalAtUserCallDirectOfProgramAcceptedRecursiveError :=
  @Yul.Reference.SourceBridgeFacts.sourceExprPreludeTerminalAt_user_call_direct_of_program_accepted_recursive_error

abbrev sourceExprEvalPreludeSoundUserCallGeneratedOkOfProgramAcceptedRecursive :=
  @Yul.Reference.SourceBridgeFacts.sourceExprEvalPreludeSound_user_call_generated_ok_of_program_accepted_recursive

abbrev sourceExprEvalPreludeSoundUserCallDirectOkOfProgramAcceptedRecursive :=
  @Yul.Reference.SourceBridgeFacts.sourceExprEvalPreludeSound_user_call_direct_ok_of_program_accepted_recursive

abbrev lower1UserCallExprEvalPreludeSoundOkOfArgRegularAllScopedAt :=
  @Yul.Reference.SourceBridgeFacts.lower1?_user_call_exprEvalPreludeSoundOk_of_argRegularAllScopedAt

abbrev lower1UserCallExprEvalPreludeSoundOfArgRegularAllScopedAt :=
  @Yul.Reference.SourceBridgeFacts.lower1?_user_call_exprEvalPreludeSound_of_argRegularAllScopedAt

abbrev lower1ExprEvalPreludeSoundOfArgRegularAllScopedAt :=
  @Yul.Reference.SourceBridgeFacts.lower1?_exprEvalPreludeSound_of_argRegularAllScopedAt

abbrev lower1UserCallExprEvalPreludeSoundOkOfArgRegularAllCheckedAt :=
  @Yul.Reference.SourceBridgeFacts.lower1?_user_call_exprEvalPreludeSoundOk_of_argRegularAllCheckedAt

abbrev lower1UserCallExprEvalPreludeSoundOfArgRegularAllCheckedAt :=
  @Yul.Reference.SourceBridgeFacts.lower1?_user_call_exprEvalPreludeSound_of_argRegularAllCheckedAt

abbrev lower1ExprEvalPreludeSoundOfArgRegularAllCheckedAt :=
  @Yul.Reference.SourceBridgeFacts.lower1?_exprEvalPreludeSound_of_argRegularAllCheckedAt

abbrev sourceAssignUserCallRegularOfExecCallRecursive :=
  @Yul.Reference.SourceBridgeFacts.sourceAssignUserCall_regular_of_execCall_recursive

abbrev sourceAssignUserCallRegularOfExecCallProgramRecursive :=
  @Yul.Reference.SourceBridgeFacts.sourceAssignUserCall_regular_of_execCall_program_recursive

abbrev sourceAssignUserCallRegularOfExecCallProgramAcceptedRecursive :=
  @Yul.Reference.SourceBridgeFacts.sourceAssignUserCall_regular_of_execCall_program_accepted_recursive

abbrev sourceLetUserCallRegularOfExecCallRecursive :=
  @Yul.Reference.SourceBridgeFacts.sourceLetUserCall_regular_of_execCall_recursive

abbrev sourceLetUserCallRegularOfExecCallProgramRecursive :=
  @Yul.Reference.SourceBridgeFacts.sourceLetUserCall_regular_of_execCall_program_recursive

abbrev sourceLetUserCallRegularOfExecCallProgramAcceptedRecursive :=
  @Yul.Reference.SourceBridgeFacts.sourceLetUserCall_regular_of_execCall_program_accepted_recursive

abbrev sourceResultBlockRunBridgeOfSoundWhenExact :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockRunBridge_of_sound_when_exact

abbrev checkedDispatcherLoweringSoundWhenExact :=
  @Yul.Reference.SourceBridgeFacts.CheckedDispatcherLoweringSoundWhenExact

abbrev checkedDispatcherLoweringSoundWhenExactOfStmtBlockLoweringSoundWhenFreshAtExact :=
  @Yul.Reference.SourceBridgeFacts.checkedDispatcherLoweringSoundWhenExact_of_stmtBlockLoweringSoundWhenFreshAtExact

abbrev checkedDispatcherLoweringSoundWhenExactOfStmtBlockLoweringSoundWhenFreshNamesAtExact :=
  @Yul.Reference.SourceBridgeFacts.checkedDispatcherLoweringSoundWhenExact_of_stmtBlockLoweringSoundWhenFreshNamesAtExact

abbrev sourceResultBlockSoundWhenAtExactOfWhenAt :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSoundWhenAtExact_of_whenAt

abbrev checkedStmtBlockLoweringSoundWhenFreshAtExactOfWhenAt :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshAtExact_of_whenAt

abbrev checkedBlockLoweringSoundWhenFreshAtExactOfWhenAt :=
  @Yul.Reference.SourceBridgeFacts.checkedBlockLoweringSoundWhenFreshAtExact_of_whenAt

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactOfFreshAtExact :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_of_freshAtExact

abbrev checkedBlockLoweringSoundWhenFreshNamesAtExactOfFreshAtExact :=
  @Yul.Reference.SourceBridgeFacts.checkedBlockLoweringSoundWhenFreshNamesAtExact_of_freshAtExact

abbrev sourceResultNoCheckpoint :=
  @Yul.Reference.SourceBridgeFacts.SourceResultNoCheckpoint

abbrev stateCheckpointAllowed :=
  @Yul.Reference.SourceBridgeFacts.StateCheckpointAllowed

abbrev sourceResultCheckpointAllowed :=
  @Yul.Reference.SourceBridgeFacts.SourceResultCheckpointAllowed

abbrev sourcePairResultCheckpointAllowed :=
  @Yul.Reference.SourceBridgeFacts.SourcePairResultCheckpointAllowed

abbrev stateCheckpointAllowedRestrictStoreTo :=
  @Yul.Reference.SourceBridgeFacts.StateCheckpointAllowed.restrictStoreTo

abbrev stateCheckpointAllowedMono :=
  @Yul.Reference.SourceBridgeFacts.StateCheckpointAllowed.mono

abbrev stateCheckpointAllowedOfNoLoopControl :=
  @Yul.Reference.SourceBridgeFacts.StateCheckpointAllowed.of_no_loop_control

abbrev stateCheckpointAllowedMkOk :=
  @Yul.Reference.SourceBridgeFacts.StateCheckpointAllowed.mkOk

abbrev stateCheckpointAllowedReviveJump :=
  @Yul.Reference.SourceBridgeFacts.StateCheckpointAllowed.reviveJump

abbrev stateCheckpointAllowedSetBreak :=
  @Yul.Reference.SourceBridgeFacts.StateCheckpointAllowed.setBreak

abbrev stateCheckpointAllowedSetContinue :=
  @Yul.Reference.SourceBridgeFacts.StateCheckpointAllowed.setContinue

abbrev stateCheckpointAllowedSetLeave :=
  @Yul.Reference.SourceBridgeFacts.StateCheckpointAllowed.setLeave

abbrev stateCheckpointAllowedInsert :=
  @Yul.Reference.SourceBridgeFacts.StateCheckpointAllowed.insert

abbrev stateCheckpointAllowedZeroFill :=
  @Yul.Reference.SourceBridgeFacts.StateCheckpointAllowed.zeroFill

abbrev stateCheckpointAllowedMultifill :=
  @Yul.Reference.SourceBridgeFacts.StateCheckpointAllowed.multifill

abbrev stateCheckpointAllowedSetSharedState :=
  @Yul.Reference.SourceBridgeFacts.StateCheckpointAllowed.setSharedState

abbrev stateCheckpointAllowedSetMachineState :=
  @Yul.Reference.SourceBridgeFacts.StateCheckpointAllowed.setMachineState

abbrev stateCheckpointAllowedSetState :=
  @Yul.Reference.SourceBridgeFacts.StateCheckpointAllowed.setState

abbrev stateCheckpointAllowedSetStore :=
  @Yul.Reference.SourceBridgeFacts.StateCheckpointAllowed.setStore

abbrev stateCheckpointAllowedOverwriteOfRightOk :=
  @Yul.Reference.SourceBridgeFacts.StateCheckpointAllowed.overwrite?_of_right_ok

abbrev stateCheckpointAllowedOverwrite :=
  @Yul.Reference.SourceBridgeFacts.StateCheckpointAllowed.overwrite?

abbrev stateCheckpointAllowedCallReturnOfOkCaller :=
  @Yul.Reference.SourceBridgeFacts.StateCheckpointAllowed.callReturn_of_ok_caller

abbrev stateCheckpointAllowedCallReturn :=
  @Yul.Reference.SourceBridgeFacts.StateCheckpointAllowed.callReturn

abbrev sourceResultCheckpointAllowedOfState :=
  @Yul.Reference.SourceBridgeFacts.SourceResultCheckpointAllowed.of_state

abbrev sourceResultCheckpointAllowedMono :=
  @Yul.Reference.SourceBridgeFacts.SourceResultCheckpointAllowed.mono

abbrev sourceResultCheckpointAllowedOfNoLoopControl :=
  @Yul.Reference.SourceBridgeFacts.SourceResultCheckpointAllowed.of_no_loop_control

abbrev sourcePairResultCheckpointAllowedOfState :=
  @Yul.Reference.SourceBridgeFacts.SourcePairResultCheckpointAllowed.of_state

abbrev sourcePairResultCheckpointAllowedOk :=
  @Yul.Reference.SourceBridgeFacts.SourcePairResultCheckpointAllowed.ok

abbrev sourcePairResultCheckpointAllowedMono :=
  @Yul.Reference.SourceBridgeFacts.SourcePairResultCheckpointAllowed.mono

abbrev sourcePairResultCheckpointAllowedHead :=
  @Yul.Reference.SourceBridgeFacts.SourcePairResultCheckpointAllowed.head'

abbrev sourcePairResultCheckpointAllowedReverse :=
  @Yul.Reference.SourceBridgeFacts.SourcePairResultCheckpointAllowed.reverse'

abbrev sourcePairResultCheckpointAllowedCons :=
  @Yul.Reference.SourceBridgeFacts.SourcePairResultCheckpointAllowed.cons'

abbrev sourcePairResultCheckpointAllowedCallOfState :=
  @Yul.Reference.SourceBridgeFacts.SourcePairResultCheckpointAllowed.call_of_ok_state

abbrev sourcePairResultCheckpointAllowedCallOfAllowedState :=
  @Yul.Reference.SourceBridgeFacts.SourcePairResultCheckpointAllowed.call_of_allowed_state

abbrev sourcePairResultCheckpointAllowedCallDispatcherOfState :=
  @Yul.Reference.SourceBridgeFacts.SourcePairResultCheckpointAllowed.callDispatcher_of_ok_state

abbrev sourcePairResultCheckpointAllowedEvalValuesLitSuccOfState :=
  @Yul.Reference.SourceBridgeFacts.SourcePairResultCheckpointAllowed.evalValues_lit_succ_of_state

abbrev sourcePairResultCheckpointAllowedEvalValuesVarSuccOfState :=
  @Yul.Reference.SourceBridgeFacts.SourcePairResultCheckpointAllowed.evalValues_var_succ_of_state

abbrev sourcePairResultCheckpointAllowedEvalArgsNilSuccOfState :=
  @Yul.Reference.SourceBridgeFacts.SourcePairResultCheckpointAllowed.evalArgs_nil_succ_of_state

abbrev sourcePairResultCheckpointAllowedEvalTailZero :=
  @Yul.Reference.SourceBridgeFacts.SourcePairResultCheckpointAllowed.evalTail_zero

abbrev sourcePairResultCheckpointAllowedEvalTailSuccOfHeadTail :=
  @Yul.Reference.SourceBridgeFacts.SourcePairResultCheckpointAllowed.evalTail_succ_of_head_tail

abbrev sourcePairResultCheckpointAllowedEvalArgsConsSuccOfEvalTail :=
  @Yul.Reference.SourceBridgeFacts.SourcePairResultCheckpointAllowed.evalArgs_cons_succ_of_eval_tail

abbrev sourcePairResultCheckpointAllowedEvalValuesUserCallSuccOfArgsOk :=
  @Yul.Reference.SourceBridgeFacts.SourcePairResultCheckpointAllowed.evalValues_user_call_succ_of_args_ok

abbrev sourcePairResultCheckpointAllowedEvalUserCallSuccOfArgsOk :=
  @Yul.Reference.SourceBridgeFacts.SourcePairResultCheckpointAllowed.eval_user_call_succ_of_args_ok

abbrev sourcePairResultCheckpointAllowedEvalValuesPrimCallSuccOfArgsOk :=
  @Yul.Reference.SourceBridgeFacts.SourcePairResultCheckpointAllowed.evalValues_prim_call_succ_of_args_ok

abbrev sourcePairResultCheckpointAllowedEvalPrimCallSuccOfArgsOk :=
  @Yul.Reference.SourceBridgeFacts.SourcePairResultCheckpointAllowed.eval_prim_call_succ_of_args_ok

abbrev sourcePairResultCheckpointAllowedPrimCallZero :=
  @Yul.Reference.SourceBridgeFacts.SourcePairResultCheckpointAllowed.primCall_zero

abbrev sourcePairResultCheckpointAllowedPrimCallOfSafeOk :=
  @Yul.Reference.SourceBridgeFacts.SourcePairResultCheckpointAllowed.primCall_of_safe_ok

abbrev sourcePairResultCheckpointAllowedPrimCallOfStateEqOnOk :=
  @Yul.Reference.SourceBridgeFacts.SourcePairResultCheckpointAllowed.primCall_of_state_eq_on_ok

abbrev sourcePairResultCheckpointAllowedPrimCallStopArith :=
  @Yul.Reference.SourceBridgeFacts.SourcePairResultCheckpointAllowed.primCall_stopArith

abbrev sourcePairResultCheckpointAllowedPrimCallCompBit :=
  @Yul.Reference.SourceBridgeFacts.SourcePairResultCheckpointAllowed.primCall_compBit

abbrev sourcePairResultCheckpointAllowedPrimCallBlockOfNonOk :=
  @Yul.Reference.SourceBridgeFacts.SourcePairResultCheckpointAllowed.primCall_block_of_nonOk

abbrev sourcePairResultCheckpointAllowedPrimCallEnvOfSafeNonOk :=
  @Yul.Reference.SourceBridgeFacts.SourcePairResultCheckpointAllowed.primCall_env_of_safe_nonOk

abbrev sourcePairResultCheckpointAllowedPrimCallStackMemFlowOfSafeNonOk :=
  @Yul.Reference.SourceBridgeFacts.SourcePairResultCheckpointAllowed.primCall_stackMemFlow_of_safe_nonOk

abbrev sourcePairResultCheckpointAllowedPrimCallReturn :=
  @Yul.Reference.SourceBridgeFacts.SourcePairResultCheckpointAllowed.primCall_return

abbrev sourcePairResultCheckpointAllowedPrimCallRevert :=
  @Yul.Reference.SourceBridgeFacts.SourcePairResultCheckpointAllowed.primCall_revert

abbrev sourcePairResultCheckpointAllowedPrimCallInvalid :=
  @Yul.Reference.SourceBridgeFacts.SourcePairResultCheckpointAllowed.primCall_invalid

abbrev sourceResultCheckpointAllowedRestrictStoreTo :=
  @Yul.Reference.SourceBridgeFacts.SourceResultCheckpointAllowed.restrictStoreTo

abbrev sourceResultCheckpointAllowedMultifill :=
  @Yul.Reference.SourceBridgeFacts.SourceResultCheckpointAllowed.multifill'

abbrev sourceResultCheckpointAllowedExecExprPrimCallSuccOfArgsOk :=
  @Yul.Reference.SourceBridgeFacts.SourceResultCheckpointAllowed.exec_expr_prim_call_succ_of_args_ok

abbrev sourceResultCheckpointAllowedExecExprUserCallSuccOfArgsOk :=
  @Yul.Reference.SourceBridgeFacts.SourceResultCheckpointAllowed.exec_expr_user_call_succ_of_args_ok

abbrev sourceResultCheckpointAllowedExecBreakSucc :=
  @Yul.Reference.SourceBridgeFacts.SourceResultCheckpointAllowed.exec_break_succ

abbrev sourceResultCheckpointAllowedExecContinueSucc :=
  @Yul.Reference.SourceBridgeFacts.SourceResultCheckpointAllowed.exec_continue_succ

abbrev sourceResultCheckpointAllowedExecLeaveSucc :=
  @Yul.Reference.SourceBridgeFacts.SourceResultCheckpointAllowed.exec_leave_succ

abbrev sourceResultCheckpointAllowedExecSeqNilSucc :=
  @Yul.Reference.SourceBridgeFacts.SourceResultCheckpointAllowed.execSeq_nil_succ

abbrev sourceResultCheckpointAllowedExecSeqConsSucc :=
  @Yul.Reference.SourceBridgeFacts.SourceResultCheckpointAllowed.execSeq_cons_succ

abbrev sourceResultCheckpointAllowedExecBlockSuccOfExecSeq :=
  @Yul.Reference.SourceBridgeFacts.SourceResultCheckpointAllowed.exec_block_succ_of_execSeq

abbrev sourceResultCheckpointAllowedExecLetNoneSuccOfState :=
  @Yul.Reference.SourceBridgeFacts.SourceResultCheckpointAllowed.exec_let_none_succ_of_state

abbrev sourceResultCheckpointAllowedExecLetSomeSuccOfEvalValues :=
  @Yul.Reference.SourceBridgeFacts.SourceResultCheckpointAllowed.exec_let_some_succ_of_evalValues

abbrev sourceResultCheckpointAllowedExecAssignSuccOfEvalValues :=
  @Yul.Reference.SourceBridgeFacts.SourceResultCheckpointAllowed.exec_assign_succ_of_evalValues

abbrev sourceResultCheckpointAllowedNoCheckpointOfTop :=
  @Yul.Reference.SourceBridgeFacts.SourceResultCheckpointAllowed.no_checkpoint_of_top

abbrev sourceResultCheckpointAllowedExecBreakSuccOfScoped :=
  @Yul.Reference.SourceBridgeFacts.SourceResultCheckpointAllowed.exec_break_succ_of_scoped

abbrev sourceResultCheckpointAllowedExecContinueSuccOfScoped :=
  @Yul.Reference.SourceBridgeFacts.SourceResultCheckpointAllowed.exec_continue_succ_of_scoped

abbrev sourceResultCheckpointAllowedExecLeaveSuccOfScoped :=
  @Yul.Reference.SourceBridgeFacts.SourceResultCheckpointAllowed.exec_leave_succ_of_scoped

abbrev sourcePairResultCheckpointAllowedEvalOfEvalValues :=
  @Yul.Reference.SourceBridgeFacts.SourcePairResultCheckpointAllowed.eval_of_evalValues

abbrev sourceResultCheckpointAllowedExecIfSuccOfEvalAndBody :=
  @Yul.Reference.SourceBridgeFacts.SourceResultCheckpointAllowed.exec_if_succ_of_eval_and_body

abbrev sourceResultCheckpointAllowedExecIfSuccOfScopedBody :=
  @Yul.Reference.SourceBridgeFacts.SourceResultCheckpointAllowed.exec_if_succ_of_scoped_body

abbrev sourceResultCheckpointAllowedExecSwitchSuccOfEvalAndCase :=
  @Yul.Reference.SourceBridgeFacts.SourceResultCheckpointAllowed.exec_switch_succ_of_eval_and_case

abbrev sourceResultCheckpointAllowedExecSwitchSuccOfScopedCase :=
  @Yul.Reference.SourceBridgeFacts.SourceResultCheckpointAllowed.exec_switch_succ_of_scoped_case

abbrev sourceResultCheckpointAllowedLoopZero :=
  @Yul.Reference.SourceBridgeFacts.SourceResultCheckpointAllowed.loop_zero

abbrev sourceResultCheckpointAllowedLoopOne :=
  @Yul.Reference.SourceBridgeFacts.SourceResultCheckpointAllowed.loop_one

abbrev sourceResultCheckpointAllowedLoopSuccSuccOfParts :=
  @Yul.Reference.SourceBridgeFacts.SourceResultCheckpointAllowed.loop_succ_succ_of_parts

abbrev sourceResultCheckpointAllowedExecForSuccSuccSuccOfScopedParts :=
  @Yul.Reference.SourceBridgeFacts.SourceResultCheckpointAllowed.exec_for_succ_succ_succ_of_scoped_parts

abbrev checkpointExpressionSound :=
  Yul.Reference.SourceBridgeFacts.CheckpointExpressionSound

abbrev checkpointCallSound :=
  Yul.Reference.SourceBridgeFacts.CheckpointCallSound

abbrev checkpointExpressionSoundOfEvalValuesExprStmtCall :=
  @Yul.Reference.SourceBridgeFacts.CheckpointExpressionSound.of_evalValues_exprStmtCall

abbrev checkpointExpressionSoundOfCallSound :=
  @Yul.Reference.SourceBridgeFacts.CheckpointExpressionSound.of_callSound

abbrev checkpointCallSoundOfPrimitiveCallCheckpointAllowedForSafeState :=
  @Yul.Reference.SourceBridgeFacts.CheckpointCallSound.of_primitiveCallCheckpointAllowedForSafeState

abbrev checkpointCallSoundOfPrimitiveCallCheckpointAllowedForSafe :=
  @Yul.Reference.SourceBridgeFacts.CheckpointCallSound.of_primitiveCallCheckpointAllowedForSafe

abbrev stateCheckpointAllowedOfPairResultOk :=
  @Yul.Reference.SourceBridgeFacts.StateCheckpointAllowed.of_pair_result_ok

abbrev stateCheckpointAllowedOfResultOk :=
  @Yul.Reference.SourceBridgeFacts.StateCheckpointAllowed.of_result_ok

abbrev sourceResultCheckpointAllowedExecAndExecSeqOfScopedSafe :=
  @Yul.Reference.SourceBridgeFacts.SourceResultCheckpointAllowed.exec_and_execSeq_of_scoped_safe

abbrev sourceResultCheckpointAllowedExecOfScopedSafe :=
  @Yul.Reference.SourceBridgeFacts.SourceResultCheckpointAllowed.exec_of_scoped_safe

abbrev sourceResultCheckpointAllowedExecSeqOfScopedSafe :=
  @Yul.Reference.SourceBridgeFacts.SourceResultCheckpointAllowed.execSeq_of_scoped_safe

abbrev yulControlScopedStmt :=
  @Yul.Reference.SourceBridgeFacts.ControlFlow.ScopedStmt

abbrev yulControlScopedStmts :=
  @Yul.Reference.SourceBridgeFacts.ControlFlow.ScopedStmts

abbrev yulControlScopedCases :=
  @Yul.Reference.SourceBridgeFacts.ControlFlow.ScopedCases

abbrev yulControlFunctionScoped :=
  @Yul.Reference.SourceBridgeFacts.ControlFlow.FunctionScoped

abbrev yulControlFunctionListScoped :=
  @Yul.Reference.SourceBridgeFacts.ControlFlow.FunctionListScoped

abbrev yulControlContractScoped :=
  @Yul.Reference.SourceBridgeFacts.ControlFlow.ContractScoped

abbrev yulControlProgramScoped :=
  @Yul.Reference.SourceBridgeFacts.ControlFlow.ProgramScoped

abbrev yulControlScopedBlock :=
  @Yul.Reference.SourceBridgeFacts.ControlFlow.scoped_block

abbrev yulControlScopedSwitch :=
  @Yul.Reference.SourceBridgeFacts.ControlFlow.scoped_switch

abbrev yulControlScopedCasesSelectSwitchCase :=
  @Yul.Reference.SourceBridgeFacts.ControlFlow.scopedCases_selectSwitchCase

abbrev yulControlScopedFor :=
  @Yul.Reference.SourceBridgeFacts.ControlFlow.scoped_for

abbrev yulControlScopedIf :=
  @Yul.Reference.SourceBridgeFacts.ControlFlow.scoped_if

abbrev yulControlContractScopedDispatcher :=
  @Yul.Reference.SourceBridgeFacts.ControlFlow.contract_scoped_dispatcher

abbrev yulControlContractScopedFunctions :=
  @Yul.Reference.SourceBridgeFacts.ControlFlow.contract_scoped_functions

abbrev yulControlProgramScopedDispatcher :=
  @Yul.Reference.SourceBridgeFacts.ControlFlow.program_scoped_dispatcher

abbrev yulControlProgramScopedFunctions :=
  @Yul.Reference.SourceBridgeFacts.ControlFlow.program_scoped_functions

abbrev yulControlNotScopedTopBreak :=
  @Yul.Reference.SourceBridgeFacts.ControlFlow.not_scoped_top_break

abbrev yulControlNotScopedTopContinue :=
  @Yul.Reference.SourceBridgeFacts.ControlFlow.not_scoped_top_continue

abbrev yulControlNotScopedTopLeave :=
  @Yul.Reference.SourceBridgeFacts.ControlFlow.not_scoped_top_leave

abbrev sourceResultOutcomeRelRelayoutOfCompatibleNoCheckpoint :=
  @Yul.Reference.SourceBridgeFacts.SourceResultOutcomeRel.relayout_of_compatible_no_checkpoint

abbrev sourceResultBlockSoundWhenAtExactSameLayoutOfCompatNoCheckpoint :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSoundWhenAtExact_same_layout_of_compat_no_checkpoint

abbrev checkedStmtBlockLoweringSoundWhenFreshAtExactSameLayoutOfCompatNoCheckpoint :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshAtExact_same_layout_of_compat_no_checkpoint

abbrev checkedBlockLoweringSoundWhenFreshAtExactSameLayoutOfCompatNoCheckpoint :=
  @Yul.Reference.SourceBridgeFacts.checkedBlockLoweringSoundWhenFreshAtExact_same_layout_of_compat_no_checkpoint

abbrev checkedBlockLoweringSoundWhenFreshAtExactNil :=
  @Yul.Reference.SourceBridgeFacts.checkedBlockLoweringSoundWhenFreshAtExact_nil

abbrev checkedBlockLoweringSoundWhenFreshAtExactNilOfCompat :=
  @Yul.Reference.SourceBridgeFacts.checkedBlockLoweringSoundWhenFreshAtExact_nil_of_compat

abbrev checkedBlockLoweringSoundWhenFreshNamesAtExactNilOfCompat :=
  @Yul.Reference.SourceBridgeFacts.checkedBlockLoweringSoundWhenFreshNamesAtExact_nil_of_compat

abbrev checkedStmtBlockLoweringSoundWhenFreshAtExactBlockEmptyOfCompat :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshAtExact_block_empty_of_compat

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactBlockEmptyOfCompat :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_block_empty_of_compat

abbrev checkedStmtBlockLoweringSoundWhenFreshAtExactLetNoneOfCompat :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshAtExact_let_none_of_compat

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactLetNoneOfCompat :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_let_none_of_compat

abbrev checkedStmtBlockLoweringSoundWhenFreshAtExactLetSingleNoneOfCompat :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshAtExact_let_single_none_of_compat

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactLetSingleNoneOfCompat :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_let_single_none_of_compat

abbrev execBlockLetSingleLitCleanOfFresh :=
  @Yul.Reference.SourceBridgeFacts.exec_block_let_single_lit_succ_succ_succ_succ_clean_of_fresh

abbrev execBlockLetSingleLitErrorOfDeclared :=
  @Yul.Reference.SourceBridgeFacts.exec_block_let_single_lit_succ_succ_succ_succ_error_of_declared

abbrev sourceResultBlockSoundWhenAtLetLitSingle :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSoundWhenAt_let_lit_single

abbrev checkedStmtBlockLoweringSoundWhenFreshAtLetLitSingle :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshAt_let_lit_single

abbrev checkedStmtBlockLoweringSoundWhenFreshAtExactLetLitSingleOfCompat :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshAtExact_let_lit_single_of_compat

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactLetLitSingleOfCompat :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_let_lit_single_of_compat

abbrev execBlockLetVarCleanOfFresh :=
  @Yul.Reference.SourceBridgeFacts.exec_block_let_var_succ_succ_succ_succ_clean_of_fresh

abbrev sourceResultBlockSoundWhenAtExactLetVarSingleOfCompat :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSoundWhenAtExact_let_var_single_of_compat

abbrev checkedStmtBlockLoweringSoundWhenFreshAtExactLetVarSingleOfCompat :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshAtExact_let_var_single_of_compat

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactLetVarSingleOfCompat :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_let_var_single_of_compat

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactLetNoneOfSourceScoped :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_let_none_of_sourceScoped

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactLetLitSingleOfSourceScoped :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_let_lit_single_of_sourceScoped

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactLetVarSingleOfSourceScoped :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_let_var_single_of_sourceScoped

abbrev execBlockAssignLitOfCheck :=
  @Yul.Reference.SourceBridgeFacts.exec_block_assign_lit_succ_succ_succ_succ_of_check

abbrev sourceResultBlockSoundWhenAtExactAssignLitSingleOfCompat :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSoundWhenAtExact_assign_lit_single_of_compat

abbrev checkedStmtBlockLoweringSoundWhenFreshAtExactAssignLitSingleOfCompat :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshAtExact_assign_lit_single_of_compat

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactAssignLitSingleOfCompat :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_assign_lit_single_of_compat

abbrev execBlockAssignVarOfCheckLookup :=
  @Yul.Reference.SourceBridgeFacts.exec_block_assign_var_succ_succ_succ_succ_of_check_lookup

abbrev sourceResultBlockSoundWhenAtExactAssignVarSingleOfCompat :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSoundWhenAtExact_assign_var_single_of_compat

abbrev checkedStmtBlockLoweringSoundWhenFreshAtExactAssignVarSingleOfCompat :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshAtExact_assign_var_single_of_compat

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactAssignVarSingleOfCompat :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_assign_var_single_of_compat

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactAssignLitSingleOfSourceScoped :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_assign_lit_single_of_sourceScoped

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactAssignVarSingleOfSourceScoped :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_assign_var_single_of_sourceScoped

abbrev checkedStmtBlockLoweringSoundWhenFreshAtExactIfZeroEmptyOfCompat :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshAtExact_if_zero_empty_of_compat

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactIfZeroEmptyOfCompat :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_if_zero_empty_of_compat

abbrev sourceResultBlockSoundWhenAtExactBreakOfCompat :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSoundWhenAtExact_break_of_compat

abbrev sourceResultBlockSoundWhenAtExactContinueOfCompat :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSoundWhenAtExact_continue_of_compat

abbrev sourceResultBlockSoundWhenAtExactLeaveOfCompat :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSoundWhenAtExact_leave_of_compat

abbrev checkedStmtBlockLoweringSoundWhenFreshAtExactBreakOfCompat :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshAtExact_break_of_compat

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactBreakOfCompat :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_break_of_compat

abbrev checkedStmtBlockLoweringSoundWhenFreshAtExactContinueOfCompat :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshAtExact_continue_of_compat

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactContinueOfCompat :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_continue_of_compat

abbrev checkedStmtBlockLoweringSoundWhenFreshAtExactLeaveOfCompat :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshAtExact_leave_of_compat

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactLeaveOfCompat :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_leave_of_compat

abbrev sourceResultBlockSoundWhenAtExactConsBreakOfCompat :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSoundWhenAtExact_cons_break_of_compat

abbrev checkedBlockLoweringSoundWhenFreshAtExactConsBreakOfCompat :=
  @Yul.Reference.SourceBridgeFacts.checkedBlockLoweringSoundWhenFreshAtExact_cons_break_of_compat

abbrev checkedBlockLoweringSoundWhenFreshNamesAtExactConsBreakOfCompat :=
  @Yul.Reference.SourceBridgeFacts.checkedBlockLoweringSoundWhenFreshNamesAtExact_cons_break_of_compat

abbrev sourceResultBlockSoundWhenAtExactConsContinueOfCompat :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSoundWhenAtExact_cons_continue_of_compat

abbrev checkedBlockLoweringSoundWhenFreshAtExactConsContinueOfCompat :=
  @Yul.Reference.SourceBridgeFacts.checkedBlockLoweringSoundWhenFreshAtExact_cons_continue_of_compat

abbrev checkedBlockLoweringSoundWhenFreshNamesAtExactConsContinueOfCompat :=
  @Yul.Reference.SourceBridgeFacts.checkedBlockLoweringSoundWhenFreshNamesAtExact_cons_continue_of_compat

abbrev sourceResultBlockSoundWhenAtExactConsLeaveOfCompat :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSoundWhenAtExact_cons_leave_of_compat

abbrev checkedBlockLoweringSoundWhenFreshAtExactConsLeaveOfCompat :=
  @Yul.Reference.SourceBridgeFacts.checkedBlockLoweringSoundWhenFreshAtExact_cons_leave_of_compat

abbrev checkedBlockLoweringSoundWhenFreshNamesAtExactConsLeaveOfCompat :=
  @Yul.Reference.SourceBridgeFacts.checkedBlockLoweringSoundWhenFreshNamesAtExact_cons_leave_of_compat

abbrev recursiveSourceBridgeWhenUpToAtExactOfNonexact :=
  @Yul.Reference.SourceBridgeFacts.RecursiveSourceBridgeWhenUpToAtExact.of_nonexact

abbrev recursiveSourceBridgeWhenUpToAtExactCompatOfNonexact :=
  @Yul.Reference.SourceBridgeFacts.RecursiveSourceBridgeWhenUpToAtExactCompat.of_nonexact

abbrev sourceResultBlockSoundWhenAtExactOfRegularSeqRunBridgeHidden :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSoundWhenAtExact_of_regularSeqRunBridgeHidden

abbrev sourceResultBlockSoundWhenAtExactOfRegularSeqRunBridgeHiddenCompat :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSoundWhenAtExact_of_regularSeqRunBridgeHidden_compat

abbrev checkedStmtBlockLoweringSoundWhenFreshAtExactOfRegularSeqRunBridgeHiddenCompat :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshAtExact_of_regularSeqRunBridgeHidden_compat

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactOfRegularSeqRunBridgeHiddenCompat :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_of_regularSeqRunBridgeHidden_compat

abbrev checkedBlockLoweringSoundWhenFreshAtExactOfRegularSeqRunBridgeHiddenCompat :=
  @Yul.Reference.SourceBridgeFacts.checkedBlockLoweringSoundWhenFreshAtExact_of_regularSeqRunBridgeHidden_compat

abbrev checkedBlockLoweringSoundWhenFreshNamesAtExactOfRegularSeqRunBridgeHiddenCompat :=
  @Yul.Reference.SourceBridgeFacts.checkedBlockLoweringSoundWhenFreshNamesAtExact_of_regularSeqRunBridgeHidden_compat

abbrev checkedBlockLoweringSoundWhenFreshNamesAtExactOfRegularSeqRunBridgeHiddenExactCompat :=
  @Yul.Reference.SourceBridgeFacts.checkedBlockLoweringSoundWhenFreshNamesAtExact_of_regularSeqRunBridgeHidden_exact_compat

abbrev sourceRegularStmtRunHiddenExact :=
  @Yul.Reference.SourceBridgeFacts.SourceRegularStmtRunHiddenExact

abbrev sourceNonregularStmtRunHiddenExact :=
  @Yul.Reference.SourceBridgeFacts.SourceNonregularStmtRunHiddenExact

abbrev sourceResultSeqSoundWhenAtExactHiddenCtx :=
  @Yul.Reference.SourceBridgeFacts.SourceResultSeqSoundWhenAtExactHiddenCtx

abbrev checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx :=
  @Yul.Reference.SourceBridgeFacts.CheckedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx

abbrev sourceResultSeqSoundWhenAtExactHiddenCtxOfFuelExact :=
  @Yul.Reference.SourceBridgeFacts.SourceResultSeqSoundWhenAtExactHiddenCtx.of_fuel_exact

abbrev sourceResultSeqSoundWhenAtExactHiddenCtxConsRegularHidden :=
  @Yul.Reference.SourceBridgeFacts.sourceResultSeqSoundWhenAtExactHiddenCtx_cons_regular_hidden

abbrev sourceResultSeqSoundWhenAtExactHiddenCtxConsNonregularHidden :=
  @Yul.Reference.SourceBridgeFacts.sourceResultSeqSoundWhenAtExactHiddenCtx_cons_nonregular_hidden

abbrev sourceResultSeqSoundWhenAtExactHiddenCtxSingleRegularHidden :=
  @Yul.Reference.SourceBridgeFacts.sourceResultSeqSoundWhenAtExactHiddenCtx_single_regular_hidden

abbrev sourceResultSeqSoundWhenAtExactHiddenCtxSingleNonregularHidden :=
  @Yul.Reference.SourceBridgeFacts.sourceResultSeqSoundWhenAtExactHiddenCtx_single_nonregular_hidden

abbrev sourceResultSeqSoundWhenAtExactHiddenCtxFinishSingleRegularHidden :=
  @Yul.Reference.SourceBridgeFacts.sourceResultSeqSoundWhenAtExactHiddenCtx_finish_single_regular_hidden

abbrev sourceResultSeqSoundWhenAtExactHiddenCtxFinishSingleNonregularHidden :=
  @Yul.Reference.SourceBridgeFacts.sourceResultSeqSoundWhenAtExactHiddenCtx_finish_single_nonregular_hidden

abbrev sourceResultSeqSoundWhenAtExactHiddenCtxSingleHiddenOfRegularOrNonregular :=
  @Yul.Reference.SourceBridgeFacts.sourceResultSeqSoundWhenAtExactHiddenCtx_single_hidden_of_regular_or_nonregular

abbrev sourceResultSeqSoundWhenAtExactHiddenCtxSingleHiddenOfCurrentRegularOrNonregular :=
  @Yul.Reference.SourceBridgeFacts.sourceResultSeqSoundWhenAtExactHiddenCtx_single_hidden_of_current_regular_or_nonregular

abbrev resultEqOfExecSeqSingleSucc :=
  @Yul.Reference.SourceBridgeFacts.result_eq_of_execSeq_single_succ

abbrev allowedOfExecSeqSingleSucc :=
  @Yul.Reference.SourceBridgeFacts.allowed_of_execSeq_single_succ

abbrev sourceResultBlockSoundWhenAtExactOfHiddenCtxCompat :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSoundWhenAtExact_of_hiddenCtx_compat

abbrev sourceScopeContainsOfRunOpenRegular :=
  @Yul.Reference.SourceBridgeFacts.sourceScopeContains_of_runOpen_regular

abbrev sourceResultBlockSoundWhenAtExactHiddenScopeOfHiddenCtxCompat :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSoundWhenAtExactHiddenScope_of_hiddenCtx_compat

abbrev sourceResultBlockSoundWhenAtExactHiddenScopeOkRegularExact :=
  @Yul.Reference.SourceBridgeFacts.SourceResultBlockSoundWhenAtExactHiddenScope.ok_regular_exact

abbrev sourceResultBlockSoundWhenAtExactHiddenScopeOkBreak :=
  @Yul.Reference.SourceBridgeFacts.SourceResultBlockSoundWhenAtExactHiddenScope.ok_break

abbrev sourceResultBlockSoundWhenAtExactHiddenScopeOkContinue :=
  @Yul.Reference.SourceBridgeFacts.SourceResultBlockSoundWhenAtExactHiddenScope.ok_continue

abbrev sourceResultBlockSoundWhenAtExactHiddenScopeOkLeave :=
  @Yul.Reference.SourceBridgeFacts.SourceResultBlockSoundWhenAtExactHiddenScope.ok_leave

abbrev sourceResultBlockSoundWhenAtExactHiddenScopeErrorHalt :=
  @Yul.Reference.SourceBridgeFacts.SourceResultBlockSoundWhenAtExactHiddenScope.error_halt

abbrev checkedBlockLoweringSoundWhenFreshNamesAtExactOfHiddenCtxCompat :=
  @Yul.Reference.SourceBridgeFacts.checkedBlockLoweringSoundWhenFreshNamesAtExact_of_hiddenCtx_compat

abbrev checkedBlockLoweringSoundWhenFreshNamesAtCompileFuelHiddenScopeOfHiddenCtxCompat :=
  @Yul.Reference.SourceBridgeFacts.checkedBlockLoweringSoundWhenFreshNamesAtCompileFuelHiddenScope_of_hiddenCtx_compat

abbrev checkedBlockLoweringSoundWhenFreshNamesAtExactOfSeqCompileFuelParamHiddenCtxCompat :=
  @Yul.Reference.SourceBridgeFacts.checkedBlockLoweringSoundWhenFreshNamesAtExact_of_seqCompileFuelParamHiddenCtx_compat

abbrev sourceRegularStmtRunHiddenExactIfFalseOfEvalDomain :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularStmtRunHiddenExact_if_false_of_eval_domain

abbrev sourceRegularStmtRunHiddenExactIfTrueRegularOfEvalDomain :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularStmtRunHiddenExact_if_true_regular_of_eval_domain

abbrev sourceRegularStmtRunHiddenExactIfTrueRegularExistsOfEvalDomain :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularStmtRunHiddenExact_if_true_regular_exists_of_eval_domain

abbrev sourceRegularStmtRunHiddenExactIfTrueRegularOfBlockSoundOkDomain :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularStmtRunHiddenExact_if_true_regular_of_blockSound_ok_domain

abbrev sourceResultSeqSoundWhenAtExactHiddenCtxSingleIfOfEvalDomain :=
  @Yul.Reference.SourceBridgeFacts.sourceResultSeqSoundWhenAtExactHiddenCtx_single_if_of_eval_domain

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactIfOfConditionBody :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_if_of_condition_body

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactIfOfProgramAcceptedCondition :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_if_of_programAcceptedCondition

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactIfOfProgramAcceptedConditionFrontier :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_if_of_programAcceptedCondition_frontier

abbrev switchSelectedLoweringWithCover :=
  @Yul.Reference.SourceBridgeFacts.SwitchSelectedLoweringWithCover

abbrev switchSelectedLoweringWithCoverOfCaseListSelectSomeNone :=
  @Yul.Reference.SourceBridgeFacts.switchSelectedLoweringWithCover_of_caseList_select_some_none

abbrev switchSelectedLoweringWithCoverOfCaseListSelectSomeSome :=
  @Yul.Reference.SourceBridgeFacts.switchSelectedLoweringWithCover_of_caseList_select_some_some

abbrev sourceResultSeqSoundWhenAtExactHiddenCtxSingleSwitchOfEvalDomain :=
  @Yul.Reference.SourceBridgeFacts.sourceResultSeqSoundWhenAtExactHiddenCtx_single_switch_of_eval_domain

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactSwitchOfScrutineeBody :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_switch_of_scrutinee_body

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactSwitchOfProgramAcceptedScrutinee :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_switch_of_programAcceptedScrutinee

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactSwitchOfProgramAcceptedScrutineeFrontier :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_switch_of_programAcceptedScrutinee_frontier

abbrev sourceResultBlockSoundWhenAtExactOfHiddenScope :=
  @Yul.Reference.SourceBridgeFacts.SourceResultBlockSoundWhenAtExact.of_hiddenScope

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactBlockOfHiddenBlock :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_block_of_hiddenBlock

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactBlockOfProgramAcceptedBody :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_block_of_programAcceptedBody

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactBlockOfProgramAcceptedBodyFrontier :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_block_of_programAcceptedBody_frontier

abbrev sourceForGuardBreakRunScoped :=
  @Yul.Reference.SourceBridgeFacts.sourceForGuardBreakRunScoped

abbrev sourceGeneratedIszeroConditionTrueOfExactZero :=
  @Yul.Reference.SourceBridgeFacts.sourceGeneratedIszeroCondition_true_of_exact_zero

abbrev uint256IsZeroEqZeroOfNe :=
  @Yul.Reference.SourceBridgeFacts.uint256_isZero_eq_zero_of_ne

abbrev sourceGeneratedIszeroConditionFalseOfExactNonzero :=
  @Yul.Reference.SourceBridgeFacts.sourceGeneratedIszeroCondition_false_of_exact_nonzero

abbrev sourceForGeneratedGuardSkipRunOpenOfExactNonzero :=
  @Yul.Reference.SourceBridgeFacts.sourceForGeneratedGuardSkipRunOpen_of_exact_nonzero

abbrev sourceForGeneratedGuardSkipRunOpenOfEvalDomainNonzero :=
  @Yul.Reference.SourceBridgeFacts.sourceForGeneratedGuardSkipRunOpen_of_eval_domain_nonzero

abbrev sourceForGeneratedGuardBodyBreakRunScopedOfEvalDomainNonzero :=
  @Yul.Reference.SourceBridgeFacts.sourceForGeneratedGuardBodyBreakRunScoped_of_eval_domain_nonzero

abbrev sourceForGeneratedBodyBreakStmtRunOfEvalDomainNonzero :=
  @Yul.Reference.SourceBridgeFacts.sourceForGeneratedBodyBreakStmtRun_of_eval_domain_nonzero

abbrev sourceRegularStmtRunHiddenExactForGeneratedBodyBreakOfEvalDomainNonzero :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularStmtRunHiddenExact_for_generated_body_break_of_eval_domain_nonzero

abbrev sourceRegularStmtRunHiddenExactForGeneratedBodyBreakOfBlockSound :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularStmtRunHiddenExact_for_generated_body_break_of_blockSound

abbrev sourceForGeneratedGuardBodyLeaveRunScopedOfEvalDomainNonzero :=
  @Yul.Reference.SourceBridgeFacts.sourceForGeneratedGuardBodyLeaveRunScoped_of_eval_domain_nonzero

abbrev sourceForGeneratedBodyLeaveStmtRunOfEvalDomainNonzero :=
  @Yul.Reference.SourceBridgeFacts.sourceForGeneratedBodyLeaveStmtRun_of_eval_domain_nonzero

abbrev sourceNonregularStmtRunHiddenExactForGeneratedBodyLeaveOfEvalDomainNonzero :=
  @Yul.Reference.SourceBridgeFacts.sourceNonregularStmtRunHiddenExact_for_generated_body_leave_of_eval_domain_nonzero

abbrev sourceNonregularStmtRunHiddenExactForGeneratedBodyLeaveOfBlockSound :=
  @Yul.Reference.SourceBridgeFacts.sourceNonregularStmtRunHiddenExact_for_generated_body_leave_of_blockSound

abbrev sourceForGeneratedGuardBodyHaltRunScopedOfEvalDomainNonzero :=
  @Yul.Reference.SourceBridgeFacts.sourceForGeneratedGuardBodyHaltRunScoped_of_eval_domain_nonzero

abbrev sourceForGeneratedBodyHaltStmtRunOfEvalDomainNonzero :=
  @Yul.Reference.SourceBridgeFacts.sourceForGeneratedBodyHaltStmtRun_of_eval_domain_nonzero

abbrev sourceNonregularStmtRunHiddenExactForGeneratedBodyHaltOfEvalDomainNonzero :=
  @Yul.Reference.SourceBridgeFacts.sourceNonregularStmtRunHiddenExact_for_generated_body_halt_of_eval_domain_nonzero

abbrev sourceNonregularStmtRunHiddenExactForGeneratedBodyHaltOfBlockSound :=
  @Yul.Reference.SourceBridgeFacts.sourceNonregularStmtRunHiddenExact_for_generated_body_halt_of_blockSound

abbrev sourceForGeneratedGuardBodyContinueRunScopedOfEvalDomainNonzero :=
  @Yul.Reference.SourceBridgeFacts.sourceForGeneratedGuardBodyContinueRunScoped_of_eval_domain_nonzero

abbrev sourceForGeneratedBodyContinuePostHaltStmtRunOfEvalDomainNonzero :=
  @Yul.Reference.SourceBridgeFacts.sourceForGeneratedBodyContinuePostHaltStmtRun_of_eval_domain_nonzero

abbrev sourceNonregularStmtRunHiddenExactForGeneratedBodyContinuePostHaltOfEvalDomainNonzero :=
  @Yul.Reference.SourceBridgeFacts.sourceNonregularStmtRunHiddenExact_for_generated_body_continue_post_halt_of_eval_domain_nonzero

abbrev sourceNonregularStmtRunHiddenExactForGeneratedBodyContinuePostHaltOfBlockSound :=
  @Yul.Reference.SourceBridgeFacts.sourceNonregularStmtRunHiddenExact_for_generated_body_continue_post_halt_of_blockSound

abbrev sourceNonregularStmtRunHiddenExactForGeneratedBodyContinuePostLeaveOfBlockSound :=
  @Yul.Reference.SourceBridgeFacts.sourceNonregularStmtRunHiddenExact_for_generated_body_continue_post_leave_of_blockSound

abbrev sourceForGeneratedGuardBodyRegularRunScopedOfEvalDomainNonzero :=
  @Yul.Reference.SourceBridgeFacts.sourceForGeneratedGuardBodyRegularRunScoped_of_eval_domain_nonzero

abbrev sourceForGeneratedBodyRegularPostHaltStmtRunOfEvalDomainNonzero :=
  @Yul.Reference.SourceBridgeFacts.sourceForGeneratedBodyRegularPostHaltStmtRun_of_eval_domain_nonzero

abbrev sourceNonregularStmtRunHiddenExactForGeneratedBodyRegularPostHaltOfEvalDomainNonzero :=
  @Yul.Reference.SourceBridgeFacts.sourceNonregularStmtRunHiddenExact_for_generated_body_regular_post_halt_of_eval_domain_nonzero

abbrev sourceNonregularStmtRunHiddenExactForGeneratedBodyRegularPostHaltOfBlockSound :=
  @Yul.Reference.SourceBridgeFacts.sourceNonregularStmtRunHiddenExact_for_generated_body_regular_post_halt_of_blockSound

abbrev sourceNonregularStmtRunHiddenExactForGeneratedBodyRegularPostLeaveOfBlockSound :=
  @Yul.Reference.SourceBridgeFacts.sourceNonregularStmtRunHiddenExact_for_generated_body_regular_post_leave_of_blockSound

abbrev sourceRegularStmtRunHiddenExactForGeneratedBodyRegularPostRegularOfEvalDomainNonzero :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularStmtRunHiddenExact_for_generated_body_regular_post_regular_of_eval_domain_nonzero

abbrev sourceRegularStmtRunHiddenExactForGeneratedBodyRegularPostRegularOfBlockSound :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularStmtRunHiddenExact_for_generated_body_regular_post_regular_of_blockSound

abbrev sourceNonregularStmtRunHiddenExactForGeneratedBodyRegularPostRegularOfEvalDomainNonzero :=
  @Yul.Reference.SourceBridgeFacts.sourceNonregularStmtRunHiddenExact_for_generated_body_regular_post_regular_of_eval_domain_nonzero

abbrev sourceNonregularStmtRunHiddenExactForGeneratedBodyRegularPostRegularOfBlockSound :=
  @Yul.Reference.SourceBridgeFacts.sourceNonregularStmtRunHiddenExact_for_generated_body_regular_post_regular_of_blockSound

abbrev sourceRegularStmtRunHiddenExactForGeneratedBodyContinuePostRegularOfEvalDomainNonzero :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularStmtRunHiddenExact_for_generated_body_continue_post_regular_of_eval_domain_nonzero

abbrev sourceRegularStmtRunHiddenExactForGeneratedBodyContinuePostRegularOfBlockSound :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularStmtRunHiddenExact_for_generated_body_continue_post_regular_of_blockSound

abbrev sourceNonregularStmtRunHiddenExactForGeneratedBodyContinuePostRegularOfEvalDomainNonzero :=
  @Yul.Reference.SourceBridgeFacts.sourceNonregularStmtRunHiddenExact_for_generated_body_continue_post_regular_of_eval_domain_nonzero

abbrev sourceNonregularStmtRunHiddenExactForGeneratedBodyContinuePostRegularOfBlockSound :=
  @Yul.Reference.SourceBridgeFacts.sourceNonregularStmtRunHiddenExact_for_generated_body_continue_post_regular_of_blockSound

abbrev sourceForGeneratedGuardBreakRunScopedOfExactZero :=
  @Yul.Reference.SourceBridgeFacts.sourceForGeneratedGuardBreakRunScoped_of_exact_zero

abbrev sourceForGeneratedGuardBreakRunScopedOfEvalDomainZero :=
  @Yul.Reference.SourceBridgeFacts.sourceForGeneratedGuardBreakRunScoped_of_eval_domain_zero

abbrev sourceForGeneratedFalseStmtRunOfEvalDomainZero :=
  @Yul.Reference.SourceBridgeFacts.sourceForGeneratedFalseStmtRun_of_eval_domain_zero

abbrev sourceRegularStmtRunHiddenExactForGeneratedFalseOfEvalDomainZero :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularStmtRunHiddenExact_for_generated_false_of_eval_domain_zero

abbrev sourceNonregularStmtRunHiddenExactForGeneratedConditionTerminal :=
  @Yul.Reference.SourceBridgeFacts.sourceNonregularStmtRunHiddenExact_for_generated_condition_terminal

abbrev sourceResultSeqSoundWhenAtExactHiddenCtxSingleForOfImportedLoopBranches :=
  @Yul.Reference.SourceBridgeFacts.sourceResultSeqSoundWhenAtExactHiddenCtx_single_for_of_imported_loop_branches

abbrev postBreakFalseOfCheckpointAllowedFalseFalseTrue :=
  @Yul.Reference.SourceBridgeFacts.post_break_false_of_checkpointAllowed_false_false_true

abbrev postContinueFalseOfCheckpointAllowedFalseFalseTrue :=
  @Yul.Reference.SourceBridgeFacts.post_continue_false_of_checkpointAllowed_false_false_true

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactForOfSingletonHiddenCtx :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_for_of_singleton_hiddenCtx

abbrev generatedForLowerBlock :=
  @Yul.Reference.SourceBridgeFacts.generatedForLowerBlock

abbrev generatedForCompiled :=
  @Yul.Reference.SourceBridgeFacts.GeneratedForCompiled

abbrev generatedForLoopBranchContracts :=
  @Yul.Reference.SourceBridgeFacts.GeneratedForLoopBranchContracts

abbrev generatedForLoopNonrecursiveBranchContracts :=
  @Yul.Reference.SourceBridgeFacts.GeneratedForLoopNonrecursiveBranchContracts

abbrev generatedForLoopPostRegularBranchContract :=
  @Yul.Reference.SourceBridgeFacts.GeneratedForLoopPostRegularBranchContract

abbrev hiddenBlockModeSound :=
  @Yul.Reference.SourceBridgeFacts.HiddenBlockModeSound

abbrev checkedHiddenBlockModeSoundWhenFreshNamesAtCompileFuelHiddenScope :=
  @Yul.Reference.SourceBridgeFacts.CheckedHiddenBlockModeSoundWhenFreshNamesAtCompileFuelHiddenScope

abbrev generatedForBodyModeSound :=
  @Yul.Reference.SourceBridgeFacts.GeneratedForBodyModeSound

abbrev generatedForPostModeSound :=
  @Yul.Reference.SourceBridgeFacts.GeneratedForPostModeSound

abbrev generatedForLoopPostRegularOkBranchContract :=
  @Yul.Reference.SourceBridgeFacts.GeneratedForLoopPostRegularOkBranchContract

abbrev generatedForLoopBranchContractsOfProgramAcceptedHiddenMode :=
  @Yul.Reference.SourceBridgeFacts.generatedForLoopBranchContracts_of_programAccepted_hiddenMode

abbrev generatedForLoopPostRegularOkBranchContractOfProgramAcceptedHiddenMode :=
  @Yul.Reference.SourceBridgeFacts.generatedForLoopPostRegularOkBranchContract_of_programAccepted_hiddenMode

abbrev checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtxConsForOfProgramAcceptedLoopReserved :=
  @Yul.Reference.SourceBridgeFacts.checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_for_of_programAcceptedLoop_reserved

abbrev execBlockStateDomainExactOfExecSeqContains :=
  @Yul.Reference.SourceBridgeFacts.exec_block_state_domain_exact_of_execSeq_contains

abbrev execBlockOkDomainExactOfExecSeqContains :=
  @Yul.Reference.SourceBridgeFacts.exec_block_ok_domain_exact_of_execSeq_contains

abbrev execBlockBreakDomainExactOfExecSeqContains :=
  @Yul.Reference.SourceBridgeFacts.exec_block_break_domain_exact_of_execSeq_contains

abbrev execBlockContinueDomainExactOfExecSeqContains :=
  @Yul.Reference.SourceBridgeFacts.exec_block_continue_domain_exact_of_execSeq_contains

abbrev execBlockLeaveDomainExactOfExecSeqContains :=
  @Yul.Reference.SourceBridgeFacts.exec_block_leave_domain_exact_of_execSeq_contains

abbrev exprOkDomainExactContract :=
  @Yul.Reference.SourceBridgeFacts.ExprOkDomainExactContract

abbrev exprOkDomainExactContractToOkOrOutOfFuel :=
  @Yul.Reference.SourceBridgeFacts.ExprOkDomainExactContract.to_okOrOutOfFuel

abbrev exprOkOrOutOfFuelDomainExactContract :=
  @Yul.Reference.SourceBridgeFacts.ExprOkOrOutOfFuelDomainExactContract

abbrev exprOkOrOutOfFuelDomainExactContractOfSafePrimitiveFamilies :=
  @Yul.Reference.SourceBridgeFacts.ExprOkOrOutOfFuelDomainExactContract.of_safe_primitiveFamilies

abbrev blockDomainExactContract :=
  @Yul.Reference.SourceBridgeFacts.BlockDomainExactContract

abbrev blockDomainExactContractOfExecSeqContains :=
  @Yul.Reference.SourceBridgeFacts.BlockDomainExactContract.of_execSeq_contains

abbrev execForOkFalseOfConditionOutOfFuel :=
  @Yul.Reference.SourceBridgeFacts.exec_for_ok_false_of_condition_outOfFuel

abbrev sourceResultStoreContainsLoopSuccSuccOfOkOrOutOfFuelParts :=
  @Yul.Reference.SourceBridgeFacts.SourceResultStoreContains.loop_succ_succ_of_ok_or_outOfFuel_parts

abbrev sourceResultStoreContainsExecExecSeqOkOfSafePrimitiveFamilies :=
  @Yul.Reference.SourceBridgeFacts.SourceResultStoreContains.exec_execSeq_ok_of_safe_primitiveFamilies

abbrev sourceResultStoreContainsExecOkOfSafePrimitiveFamilies :=
  @Yul.Reference.SourceBridgeFacts.SourceResultStoreContains.exec_ok_of_safe_primitiveFamilies

abbrev sourceResultStoreContainsExecSeqOkOfSafePrimitiveFamilies :=
  @Yul.Reference.SourceBridgeFacts.SourceResultStoreContains.execSeq_ok_of_safe_primitiveFamilies

abbrev forOkDomainExactContracts :=
  @Yul.Reference.SourceBridgeFacts.ForOkDomainExactContracts

abbrev forOkDomainExactContractsOfContracts :=
  @Yul.Reference.SourceBridgeFacts.ForOkDomainExactContracts.of_contracts

abbrev forOkDomainExactContractsOfExecSeqContains :=
  @Yul.Reference.SourceBridgeFacts.ForOkDomainExactContracts.of_execSeq_contains

abbrev forOkDomainExactContractsOfSafeScopedPrimitiveFamilies :=
  @Yul.Reference.SourceBridgeFacts.ForOkDomainExactContracts.of_safe_scoped_primitiveFamilies

abbrev execForOkDomainExactOfAllFuelParts :=
  @Yul.Reference.SourceBridgeFacts.exec_for_ok_domain_exact_of_all_fuel_parts

abbrev forOkDomainExactContractsExecForOk :=
  @Yul.Reference.SourceBridgeFacts.ForOkDomainExactContracts.exec_for_ok

abbrev generatedForLoopNonrecursiveBranchContractsOfHiddenScopeBlockSound :=
  @Yul.Reference.SourceBridgeFacts.generatedForLoopNonrecursiveBranchContracts_of_hiddenScope_blockSound

abbrev generatedForLoopBranchContractsOfNonrecursiveAndPostRegular :=
  @Yul.Reference.SourceBridgeFacts.generatedForLoopBranchContracts_of_nonrecursive_and_postRegular

abbrev generatedForLoopPostRegularBranchContractOfHiddenScopeBlockSoundAndLoop :=
  @Yul.Reference.SourceBridgeFacts.generatedForLoopPostRegularBranchContract_of_hiddenScope_blockSound_and_loop

abbrev generatedForLoopPostRegularBranchContractOfHiddenScopeBlockSoundAndCheckedLoop :=
  @Yul.Reference.SourceBridgeFacts.generatedForLoopPostRegularBranchContract_of_hiddenScope_blockSound_and_checked_loop

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactForOfImportedLoopBranches :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_for_of_imported_loop_branches

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactForOfBranchContracts :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_for_of_branch_contracts

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactForOfHiddenScopeAndPostRegular :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_for_of_hiddenScope_and_postRegular

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactForOfHiddenScopeAndCheckedLoop :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_for_of_hiddenScope_and_checked_loop

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactForOfHiddenScopeAndProgramAcceptedLoop :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_for_of_hiddenScope_and_programAcceptedLoop

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactForOfProgramAcceptedLoopAndCheckedCondition :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_for_of_programAcceptedLoop_and_checked_condition

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactForOfProgramAcceptedLoopAndCheckedConditionFrontier :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_for_of_programAcceptedLoop_and_checked_condition_frontier

abbrev sourceNonregularStmtRunHiddenExactIfTrueOfEvalDomain :=
  @Yul.Reference.SourceBridgeFacts.sourceNonregularStmtRunHiddenExact_if_true_of_eval_domain

abbrev sourceRegularStmtRunHiddenExactLetExprPreludeOfEvalDomain :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularStmtRunHiddenExact_let_expr_prelude_of_eval_domain

abbrev sourceRegularStmtRunHiddenExactAssignExprPreludeOfEvalDomain :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularStmtRunHiddenExact_assign_expr_prelude_of_eval_domain

abbrev sourceRegularStmtRunHiddenExactExprPreludeOfEvalDomain :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularStmtRunHiddenExact_expr_prelude_of_eval_domain

abbrev sourceResultSeqSoundWhenAtExactHiddenCtxConsLetPrimPreludeGeneralOfEvalDomain :=
  @Yul.Reference.SourceBridgeFacts.sourceResultSeqSoundWhenAtExactHiddenCtx_cons_let_prim_of_lower_preludeRegular_general_of_eval_domain

abbrev sourceResultSeqSoundWhenAtExactHiddenCtxConsAssignPrimPreludeGeneralOfEvalDomain :=
  @Yul.Reference.SourceBridgeFacts.sourceResultSeqSoundWhenAtExactHiddenCtx_cons_assign_prim_of_lower_preludeRegular_general_of_eval_domain

abbrev sourceResultSeqSoundWhenAtExactHiddenCtxConsExprPrimPreludeGeneralOfEvalDomain :=
  @Yul.Reference.SourceBridgeFacts.sourceResultSeqSoundWhenAtExactHiddenCtx_cons_expr_prim_of_lower_preludeRegular_general_of_eval_domain

abbrev checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtxConsLetPrimPreludeSuccess :=
  @Yul.Reference.SourceBridgeFacts.checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_let_prim_of_preludeRegular_success

abbrev checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtxConsAssignPrimPreludeSuccess :=
  @Yul.Reference.SourceBridgeFacts.checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_assign_prim_of_preludeRegular_success

abbrev checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtxConsExprPrimPreludeSuccess :=
  @Yul.Reference.SourceBridgeFacts.checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_expr_prim_of_preludeRegular_success

abbrev sourceResultBlockSoundWhenAtExactBlockSameOfInner :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSoundWhenAtExact_block_same_of_inner

abbrev sourceResultBlockSoundWhenAtExactOfSeqFuelExactSame :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSoundWhenAtExact_of_seqFuelExact_same

abbrev checkedBlockLoweringSoundWhenFreshAtExactOfSeqCompileFuelExactSame :=
  @Yul.Reference.SourceBridgeFacts.checkedBlockLoweringSoundWhenFreshAtExact_of_seqCompileFuelExact_same

abbrev sourceResultBlockSoundWhenAtExactOfSeqFuelExactCompat :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSoundWhenAtExact_of_seqFuelExact_compat

abbrev checkedBlockLoweringSoundWhenFreshAtExactOfSeqCompileFuelExactCompat :=
  @Yul.Reference.SourceBridgeFacts.checkedBlockLoweringSoundWhenFreshAtExact_of_seqCompileFuelExact_compat

abbrev checkedBlockLoweringSoundWhenFreshAtExactOfSeqCompileFuelParamExactSame :=
  @Yul.Reference.SourceBridgeFacts.checkedBlockLoweringSoundWhenFreshAtExact_of_seqCompileFuelParamExact_same

abbrev checkedBlockLoweringSoundWhenFreshAtExactOfSeqCompileFuelParamExactCompat :=
  @Yul.Reference.SourceBridgeFacts.checkedBlockLoweringSoundWhenFreshAtExact_of_seqCompileFuelParamExact_compat

abbrev sourceResultBlockSoundWhenAtExactBlockSameOfInnerWhen :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSoundWhenAtExact_block_same_of_inner_when

abbrev sourceResultBlockSoundWhenAtExactBlockCompatOfInnerWhen :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSoundWhenAtExact_block_compat_of_inner_when

abbrev checkedStmtBlockLoweringSoundWhenFreshAtExactBlockSameOfSeqCompileFuelExact :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshAtExact_block_same_of_seqCompileFuelExact

abbrev checkedStmtBlockLoweringSoundWhenFreshAtExactBlockCompatOfSeqCompileFuelExact :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshAtExact_block_compat_of_seqCompileFuelExact

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactBlockCompatOfSeqCompileFuelExact :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_block_compat_of_seqCompileFuelExact

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactBlockCompatOfSeqCompileFuelParamExact :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_block_compat_of_seqCompileFuelParamExact

abbrev sourceResultBlockSoundWhenAtExactBlockCompatOfRegularSeqExactDomain :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSoundWhenAtExact_block_compat_of_regularSeqExactDomain

abbrev checkedStmtBlockLoweringSoundWhenFreshAtExactBlockCompatOfRegularSeqCompileFuelExactDomain :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshAtExact_block_compat_of_regularSeqCompileFuelExactDomain

abbrev checkedStmtBlockLoweringSoundWhenFreshAtExactBlockCompatOfRegularSeqCompileFuelParamExactDomain :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshAtExact_block_compat_of_regularSeqCompileFuelParamExactDomain

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactBlockCompatOfRegularSeqCompileFuelExactDomain :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_block_compat_of_regularSeqCompileFuelExactDomain

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactBlockCompatOfRegularSeqCompileFuelParamExactDomain :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_block_compat_of_regularSeqCompileFuelParamExactDomain

abbrev checkAssignmentErrorNotRelatable :=
  @Yul.Reference.SourceBridgeFacts.checkAssignment_error_not_relatable

abbrev checkDeclarationErrorNotRelatable :=
  @Yul.Reference.SourceBridgeFacts.checkDeclaration_error_not_relatable

abbrev restrictVarStoreInsertPairsFreshToSelf :=
  @Yul.Reference.SourceBridgeFacts.restrictVarStore_insertPairs_fresh_to_self

abbrev zeroFillRestrictStoreToOfFresh :=
  @Yul.Reference.SourceBridgeFacts.zeroFill_restrictStoreTo_of_fresh

abbrev checkDeclarationOkLookupNone :=
  @Yul.Reference.SourceBridgeFacts.checkDeclaration_ok_lookup_none

abbrev execBlockLetNoneSuccSuccSuccCleanOfCheck :=
  @Yul.Reference.SourceBridgeFacts.exec_block_let_none_succ_succ_succ_clean_of_check

abbrev functionsSourceInitNamesRunOpenRegular :=
  @Yul.Reference.SourceBridgeFacts.functions_source_initNames_runOpen_regular

abbrev functionsSourceInitNamesRunOpenRegularWithContains :=
  @Yul.Reference.SourceBridgeFacts.functions_source_initNames_runOpen_regular_with_contains

abbrev functionsSourceInitNamesContainsOfRunOpenRegular :=
  @Yul.Reference.SourceBridgeFacts.functions_source_initNames_contains_of_runOpen_regular

abbrev functionsSourceInitNamesArgListContainsOfRunOpenRegular :=
  @Yul.Reference.SourceBridgeFacts.functions_source_initNames_argList_contains_of_runOpen_regular

abbrev functionsSourceEmptyPreludeArgListContainsOfRunOpenRegular :=
  @Yul.Reference.SourceBridgeFacts.functions_source_empty_prelude_argList_contains_of_runOpen_regular

abbrev sourceResultBlockSoundWhenAtLetNone :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSoundWhenAt_let_none

abbrev checkedStmtBlockLoweringSoundWhenFreshAtLetNone :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshAt_let_none

abbrev exprArgPreludeSoundOfSourceArgPreludeRegular :=
  @Yul.Reference.SourceBridgeFacts.exprArgPreludeSound_of_sourceArgPreludeRegular

abbrev exprArgStackPreludeSoundOfSourceArgStackPreludeRegular :=
  @Yul.Reference.SourceBridgeFacts.exprArgStackPreludeSound_of_sourceArgStackPreludeRegular

abbrev exprSeqEvalSeqCast :=
  @Yul.Reference.SourceBridgeFacts.exprSeq_eval_seqCast

abbrev exprSeqEvalOfToSeqArgListEval :=
  @Yul.Reference.SourceBridgeFacts.exprSeq_eval_of_toSeq?_argList_eval

abbrev sourceArgStackPreludeRegularOfArgListRegularAtVarMapToStackSeq :=
  @Yul.Reference.SourceBridgeFacts.sourceArgStackPreludeRegular_of_argListRegularAt_varMap_toStackSeq

abbrev sourceArgStackPreludeRegularAtOfArgListRegularAtVarMapToStackSeq :=
  @Yul.Reference.SourceBridgeFacts.sourceArgStackPreludeRegularAt_of_argListRegularAt_varMap_toStackSeq

abbrev exprValuePreludeSoundPrimOfArgStackPreludeRegular :=
  @Yul.Reference.SourceBridgeFacts.exprValuePreludeSound_prim_of_arg_stack_preludeRegular

abbrev exprValuePreludeSoundPrimOfArgStackPreludeRegularAt :=
  @Yul.Reference.SourceBridgeFacts.exprValuePreludeSound_prim_of_arg_stack_preludeRegularAt

abbrev exprValuePreludeSoundPrimOfArgStackPreludeRegularAtArity :=
  @Yul.Reference.SourceBridgeFacts.exprValuePreludeSound_prim_of_arg_stack_preludeRegularAt_arity

abbrev exprListToSeqLengthEq :=
  @Yul.Reference.SourceBridgeFacts.exprList_toSeq?_length_eq

abbrev exprListToStackSeqLengthEq :=
  @Yul.Reference.SourceBridgeFacts.exprList_toStackSeq?_length_eq

abbrev lower1PrimExprValuePreludeSoundOfLowerBound1PreludeRegularAt :=
  @Yul.Reference.SourceBridgeFacts.lower1?_prim_exprValuePreludeSound_of_lowerBound1?_preludeRegularAt

abbrev lower1PrimExprValuePreludeSoundOfLowerBound1PreludeRegularAtArity :=
  @Yul.Reference.SourceBridgeFacts.lower1?_prim_exprValuePreludeSound_of_lowerBound1?_preludeRegularAt_arity

abbrev lower1PrimExprEvalPreludeSoundOfLowerBound1RegularAt :=
  @Yul.Reference.SourceBridgeFacts.lower1?_prim_exprEvalPreludeSound_of_lowerBound1?_regularAt

abbrev lower1PrimExprEvalPreludeSoundOfLowerBound1RegularAtArity :=
  @Yul.Reference.SourceBridgeFacts.lower1?_prim_exprEvalPreludeSound_of_lowerBound1?_regularAt_arity

abbrev lower1PrimExprEvalPreludeSoundOfLowerBound1RegularAtNoScope :=
  @Yul.Reference.SourceBridgeFacts.lower1?_prim_exprEvalPreludeSound_of_lowerBound1?_regularAt_noScope

abbrev lower1PrimExprEvalPreludeSoundOfLowerBound1RegularAtNoScopeArity :=
  @Yul.Reference.SourceBridgeFacts.lower1?_prim_exprEvalPreludeSound_of_lowerBound1?_regularAt_noScope_arity

abbrev lower1ExprEvalPreludeSoundOfArgRegularAllScopedAtArity :=
  @Yul.Reference.SourceBridgeFacts.lower1?_exprEvalPreludeSound_of_argRegularAllScopedAt_arity

abbrev pureAliasPrimCallOkSingle :=
  @Yul.Reference.SourceBridgeFacts.pureAliasPrim_primCall_ok_single

abbrev yulPrimCallMloadOkSingle :=
  @Yul.Reference.SourceBridgeFacts.yul_primCall_mload_ok_single

abbrev safeBasicOneOutputPrimCallOkSingle :=
  @Yul.Reference.SourceBridgeFacts.safeBasicOneOutputPrimCall_ok_single

abbrev evalValuesPrimCallSingleOfEvalPrimCallSingle :=
  @Yul.Reference.SourceBridgeFacts.evalValues_prim_call_single_of_eval_primCall_single

abbrev exprValuePreludeSoundRunPreContainsOfDomain :=
  @Yul.Reference.SourceBridgeFacts.ExprValuePreludeSound.run_preContains_of_domain

abbrev exprValuePreludeSoundRunExactOfDomain :=
  @Yul.Reference.SourceBridgeFacts.ExprValuePreludeSound.run_exact_of_domain

abbrev exprValuePreludeSoundRunPreContainsOfEvalDomain :=
  @Yul.Reference.SourceBridgeFacts.ExprValuePreludeSound.run_preContains_of_eval_domain

abbrev exprValuePreludeSoundRunExactOfEvalDomain :=
  @Yul.Reference.SourceBridgeFacts.ExprValuePreludeSound.run_exact_of_eval_domain

abbrev exprEvalPreludeSound :=
  @Yul.Reference.SourceBridgeFacts.ExprEvalPreludeSound

abbrev exprEvalPreludeSoundRunExactOfDomain :=
  @Yul.Reference.SourceBridgeFacts.ExprEvalPreludeSound.run_exact_of_domain

abbrev exprEvalPreludeSoundRunExactOfEvalDomain :=
  @Yul.Reference.SourceBridgeFacts.ExprEvalPreludeSound.run_exact_of_eval_domain

abbrev exprEvalPreludeSoundOkBoundary :=
  @Yul.Reference.SourceBridgeFacts.ExprEvalPreludeSoundOk

abbrev exprEvalResultOkAt :=
  @Yul.Reference.SourceBridgeFacts.ExprEvalResultOkAt

abbrev exprEvalPreludeSoundOkToSound :=
  @Yul.Reference.SourceBridgeFacts.ExprEvalPreludeSoundOk.toSound

abbrev exprEvalPreludeSoundZero :=
  @Yul.Reference.SourceBridgeFacts.exprEvalPreludeSound_zero

abbrev exprValuePreludeSoundToEvalOneOfEvalValuesSingle :=
  @Yul.Reference.SourceBridgeFacts.ExprValuePreludeSound.to_evalOne_of_evalValues_single

abbrev sourceExprScoped :=
  @Yul.Reference.SourceBridgeFacts.SourceExprScoped

abbrev sourceExprsScoped :=
  @Yul.Reference.SourceBridgeFacts.SourceExprsScoped

abbrev sourceExprsScopedMem :=
  @Yul.Reference.SourceBridgeFacts.SourceExprsScoped.mem

abbrev exprEvalPreludeSoundLit :=
  @Yul.Reference.SourceBridgeFacts.exprEvalPreludeSound_lit

abbrev exprEvalPreludeSoundVar :=
  @Yul.Reference.SourceBridgeFacts.exprEvalPreludeSound_var

abbrev sourceWritesDisjoint :=
  @Yul.Reference.SourceBridgeFacts.SourceWritesDisjoint

abbrev sourceVarsAgree :=
  @Yul.Reference.SourceBridgeFacts.SourceVarsAgree

abbrev sourceWritesDisjointAppend :=
  @Yul.Reference.SourceBridgeFacts.SourceWritesDisjoint.append

abbrev sourceWritesDisjointAppendLet :=
  @Yul.Reference.SourceBridgeFacts.SourceWritesDisjoint.append_let

abbrev sourceWritesDisjointAppendLetCall :=
  @Yul.Reference.SourceBridgeFacts.SourceWritesDisjoint.append_let_call

abbrev lower1SourceWritesDisjoint :=
  @Yul.Reference.SourceBridgeFacts.lower1?_sourceWritesDisjoint

abbrev lowerBound1SourceWritesDisjoint :=
  @Yul.Reference.SourceBridgeFacts.lowerBound1?_sourceWritesDisjoint

abbrev sourceWritesDisjointRunOpenRegularAgree :=
  @Yul.Reference.SourceBridgeFacts.sourceWritesDisjoint_runOpen_regular_agree

abbrev sourceArgListPreludeRegularAtConsOfTailHead :=
  @Yul.Reference.SourceBridgeFacts.sourceArgListPreludeRegularAt_cons_of_tail_head

abbrev sourceArgListPreludeRegularAtConsOfTailHeadBounded :=
  @Yul.Reference.SourceBridgeFacts.sourceArgListPreludeRegularAt_cons_of_tail_head_bounded

abbrev sourceArgListPreludeRegularAtOfLowerBound1ExprEvalSoundCovers :=
  @Yul.Reference.SourceBridgeFacts.sourceArgListPreludeRegularAt_of_lowerBound1?_exprEvalSound_covers

abbrev sourceArgListPreludeRegularAtOfLowerBound1ExprEvalSoundScopedCovers :=
  @Yul.Reference.SourceBridgeFacts.sourceArgListPreludeRegularAt_of_lowerBound1?_exprEvalSound_scoped_covers

abbrev sourceArgListPreludeRegularAtOfLowerBound1ExprEvalSoundScopedCoversBounded :=
  @Yul.Reference.SourceBridgeFacts.sourceArgListPreludeRegularAt_of_lowerBound1?_exprEvalSound_scoped_covers_bounded

abbrev sourceArgListPreludeRegularAtOfLowerBound1ExprEvalSoundCheckedCoversBounded :=
  @Yul.Reference.SourceBridgeFacts.sourceArgListPreludeRegularAt_of_lowerBound1?_exprEvalSound_checked_covers_bounded

abbrev sourceArgListPreludeRegularAtOfDirectCallArgsSafe :=
  @Yul.Reference.SourceBridgeFacts.sourceArgListPreludeRegularAt_of_directCallArgsSafe

abbrev sourceArgListPreludeRegularAllAtOfDirectLowerBound1ExprEvalSoundCovers :=
  @Yul.Reference.SourceBridgeFacts.sourceArgListPreludeRegularAllAt_of_direct_lowerBound1?_exprEvalSound_covers

abbrev sourceArgListPreludeRegularAllAtOfLowerBound1ExprEvalSoundCovers :=
  @Yul.Reference.SourceBridgeFacts.sourceArgListPreludeRegularAllAt_of_lowerBound1?_exprEvalSound_covers

abbrev sourceArgListPreludeRegularAllScopedAtOfLowerBound1ExprEvalSoundScopedCovers :=
  @Yul.Reference.SourceBridgeFacts.sourceArgListPreludeRegularAllScopedAt_of_lowerBound1?_exprEvalSound_scoped_covers

abbrev sourceArgListPreludeRegularAllScopedAtOfLowerBound1ExprEvalSoundScopedCoversBounded :=
  @Yul.Reference.SourceBridgeFacts.sourceArgListPreludeRegularAllScopedAt_of_lowerBound1?_exprEvalSound_scoped_covers_bounded

abbrev sourceArgListPreludeRegularAllCheckedAtOfLowerBound1ExprEvalSoundCheckedCoversBounded :=
  @Yul.Reference.SourceBridgeFacts.sourceArgListPreludeRegularAllCheckedAt_of_lowerBound1?_exprEvalSound_checked_covers_bounded

abbrev sourceArgListPreludeRegularAllCheckedAtOfRecursiveExprDispatcher :=
  @Yul.Reference.SourceBridgeFacts.sourceArgListPreludeRegularAllCheckedAt_of_recursiveExprDispatcher

abbrev programAcceptedRecursiveSourceBridgeArgsSucc :=
  @Yul.Reference.SourceBridgeFacts.ProgramAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNames.args_succ

abbrev sourceVarsAgreeInsertOfNotMem :=
  @Yul.Reference.SourceBridgeFacts.SourceVarsAgree.insert_of_not_mem

abbrev sourceVarsAgreeAssignManyOfNotMem :=
  @Yul.Reference.SourceBridgeFacts.SourceVarsAgree.assignMany_of_not_mem

abbrev sourceArgListEvalVarMapOfAgree :=
  @Yul.Reference.SourceBridgeFacts.sourceArgList_eval_var_map_of_agree

abbrev sourceArgListEvalAppend :=
  @Yul.Reference.SourceBridgeFacts.sourceArgList_eval_append

abbrev sourceArgListEvalVarMapReverse :=
  @Yul.Reference.SourceBridgeFacts.sourceArgList_eval_var_map_reverse

abbrev sourceArgPreludeRegularRunPreContainsOfDomain :=
  @Yul.Reference.SourceBridgeFacts.SourceArgPreludeRegular.run_preContains_of_domain

abbrev sourceArgPreludeRegularRunExactOfDomain :=
  @Yul.Reference.SourceBridgeFacts.SourceArgPreludeRegular.run_exact_of_domain

abbrev sourceArgPreludeRegularRunPreContainsOfEvalOkDomain :=
  @Yul.Reference.SourceBridgeFacts.SourceArgPreludeRegular.run_preContains_of_eval_ok_domain

abbrev sourceArgPreludeRegularRunExactOfEvalOkDomain :=
  @Yul.Reference.SourceBridgeFacts.SourceArgPreludeRegular.run_exact_of_eval_ok_domain

abbrev sourceArgListPreludeRegular :=
  @Yul.Reference.SourceBridgeFacts.SourceArgListPreludeRegular

abbrev sourceArgListPreludeRegularAt :=
  @Yul.Reference.SourceBridgeFacts.SourceArgListPreludeRegularAt

abbrev sourceArgListPreludeRegularAllAt :=
  @Yul.Reference.SourceBridgeFacts.SourceArgListPreludeRegularAllAt

abbrev sourceArgListPreludeRegularAllAtMono :=
  @Yul.Reference.SourceBridgeFacts.SourceArgListPreludeRegularAllAt.mono

abbrev sourceArgListPreludeRegularAllScopedAt :=
  @Yul.Reference.SourceBridgeFacts.SourceArgListPreludeRegularAllScopedAt

abbrev sourceArgListPreludeRegularAllScopedAtMono :=
  @Yul.Reference.SourceBridgeFacts.SourceArgListPreludeRegularAllScopedAt.mono

abbrev sourceArgListPreludeRegularAllCheckedAt :=
  @Yul.Reference.SourceBridgeFacts.SourceArgListPreludeRegularAllCheckedAt

abbrev sourceArgListPreludeRegularAllCheckedAtMono :=
  @Yul.Reference.SourceBridgeFacts.SourceArgListPreludeRegularAllCheckedAt.mono

abbrev sourceArgListPreludeRegularAllCheckedAtZero :=
  @Yul.Reference.SourceBridgeFacts.SourceArgListPreludeRegularAllCheckedAt.zero

abbrev sourceArgListPreludeTerminalAt :=
  @Yul.Reference.SourceBridgeFacts.SourceArgListPreludeTerminalAt

abbrev sourceExprPreludeTerminalAt :=
  @Yul.Reference.SourceBridgeFacts.SourceExprPreludeTerminalAt

abbrev sourceExprPreludeTerminalAtAppendSuffix :=
  @Yul.Reference.SourceBridgeFacts.SourceExprPreludeTerminalAt.append_suffix

abbrev sourceExprPreludeTerminalAtOfNoRelatableEvalError :=
  @Yul.Reference.SourceBridgeFacts.SourceExprPreludeTerminalAt.of_no_relatable_eval_error

abbrev sourceArgListPreludeTerminalAtOfNoRelatableEvalArgsError :=
  @Yul.Reference.SourceBridgeFacts.SourceArgListPreludeTerminalAt.of_no_relatable_evalArgs_error

abbrev sourceArgListPreludeTerminalAtAppendSuffix :=
  @Yul.Reference.SourceBridgeFacts.SourceArgListPreludeTerminalAt.append_suffix

abbrev evalArgsNilErrorNotRelatable :=
  @Yul.Reference.SourceBridgeFacts.evalArgs_nil_error_not_relatable

abbrev evalArgsConsErrorRelatableSplit :=
  @Yul.Reference.SourceBridgeFacts.evalArgs_cons_error_relatable_split

abbrev evalArgsAppendSingletonErrorRelatableSplit :=
  @Yul.Reference.SourceBridgeFacts.evalArgs_append_singleton_error_relatable_split

abbrev evalArgsAppendSingletonErrorRelatableSplitLt :=
  @Yul.Reference.SourceBridgeFacts.evalArgs_append_singleton_error_relatable_split_lt

abbrev evalArgsAppendSingletonOkSplitLt :=
  @Yul.Reference.SourceBridgeFacts.evalArgs_append_singleton_ok_split_lt

abbrev evalArgsReverseConsOkSplitLt :=
  @Yul.Reference.SourceBridgeFacts.evalArgs_reverse_cons_ok_split_lt

abbrev sourceArgListPreludeTerminalAtNil :=
  @Yul.Reference.SourceBridgeFacts.sourceArgListPreludeTerminalAt_nil

abbrev sourceArgListEvalVarMapStateEq :=
  @Yul.Reference.SourceBridgeFacts.sourceArgList_eval_var_map_state_eq

abbrev sourceArgListEvalVarMapInsertOfNotMem :=
  @Yul.Reference.SourceBridgeFacts.sourceArgList_eval_var_map_insert_of_not_mem

abbrev lowerBoundArgsLowerArgNamesMemFinalUsed :=
  @Yul.Reference.SourceBridgeFacts.lowerBound1?_lowerArg_names_mem_final_used

abbrev sourceArgListPreludeRegularPreExactAt :=
  @Yul.Reference.SourceBridgeFacts.SourceArgListPreludeRegularPreExactAt

abbrev sourceArgListPreludeRegularAtRunPreExactOfVarArgsDomain :=
  @Yul.Reference.SourceBridgeFacts.SourceArgListPreludeRegularAt.run_pre_exact_of_var_args_domain

abbrev sourceArgListPreludeRegularRunPreExactOfVarArgsDomain :=
  @Yul.Reference.SourceBridgeFacts.SourceArgListPreludeRegular.run_pre_exact_of_var_args_domain

abbrev sourceArgListPreludeRegularAtRunPreExactOfLowerBoundEvalDomain :=
  @Yul.Reference.SourceBridgeFacts.SourceArgListPreludeRegularAt.run_pre_exact_of_lowerBound1?_eval_domain

abbrev sourceArgListPreludeRegularRunPreExactOfLowerBoundEvalDomain :=
  @Yul.Reference.SourceBridgeFacts.SourceArgListPreludeRegular.run_pre_exact_of_lowerBound1?_eval_domain

abbrev sourceArgListPreludeRegularAtRunPreExactOfLowerBoundSafe :=
  @Yul.Reference.SourceBridgeFacts.SourceArgListPreludeRegularAt.run_pre_exact_of_lowerBound1?_safe

abbrev sourceArgListPreludeRegularRunPreExactOfLowerBoundSafe :=
  @Yul.Reference.SourceBridgeFacts.SourceArgListPreludeRegular.run_pre_exact_of_lowerBound1?_safe

abbrev sourceArgListPreludeTerminalAtConsOfTailPreExact :=
  @Yul.Reference.SourceBridgeFacts.sourceArgListPreludeTerminalAt_cons_of_tail_pre_exact

abbrev sourceArgListPreludeTerminalAtConsOfTailPreExactBounded :=
  @Yul.Reference.SourceBridgeFacts.sourceArgListPreludeTerminalAt_cons_of_tail_pre_exact_bounded

abbrev sourceArgListPreludeTerminalAtOfLowerBound1? :=
  @Yul.Reference.SourceBridgeFacts.sourceArgListPreludeTerminalAt_of_lowerBound1?

abbrev sourceArgListPreludeTerminalAtOfLowerBound1?Bounded :=
  @Yul.Reference.SourceBridgeFacts.sourceArgListPreludeTerminalAt_of_lowerBound1?_bounded

abbrev sourceArgListPreludeTerminalAtOfLowerBound1?BoundedSafeCovers :=
  @Yul.Reference.SourceBridgeFacts.sourceArgListPreludeTerminalAt_of_lowerBound1?_bounded_safe_covers

abbrev sourceArgListPreludeTerminalAtOfLowerBound1?BoundedSafeCoversRegularAt :=
  @Yul.Reference.SourceBridgeFacts.sourceArgListPreludeTerminalAt_of_lowerBound1?_bounded_safe_covers_regularAt

abbrev sourceArgListPreludeTerminalAtOfLowerBound1?BoundedSafeOkCoversRegularAt :=
  @Yul.Reference.SourceBridgeFacts.sourceArgListPreludeTerminalAt_of_lowerBound1?_bounded_safe_ok_covers_regularAt

abbrev sourceArgListPreludeTerminalAtOfLowerBound1?BoundedSafeOkScopedCoversRegularAt :=
  @Yul.Reference.SourceBridgeFacts.sourceArgListPreludeTerminalAt_of_lowerBound1?_bounded_safe_ok_scoped_covers_regularAt

abbrev sourceExprPreludeTerminalAtPrimOfLower1?BoundedSafeOkCoversRegularAt :=
  @Yul.Reference.SourceBridgeFacts.sourceExprPreludeTerminalAt_prim_of_lower1?_bounded_safe_ok_covers_regularAt

abbrev sourceExprPreludeTerminalAtPrimOfLower1?BoundedSafeOkScopedCoversRegularAt :=
  @Yul.Reference.SourceBridgeFacts.sourceExprPreludeTerminalAt_prim_of_lower1?_bounded_safe_ok_scoped_covers_regularAt

abbrev sourceArgListPreludeTerminalAtOfLowerBound1?BoundedSafeCoversRegular :=
  @Yul.Reference.SourceBridgeFacts.sourceArgListPreludeTerminalAt_of_lowerBound1?_bounded_safe_covers_regular

abbrev directCallArgsSafeAppendOfTrue :=
  @Yul.Reference.SourceBridgeFacts.directCallArgsSafe_append_of_true

abbrev directCallArgsSafeReverseOfTrue :=
  @Yul.Reference.SourceBridgeFacts.directCallArgsSafe_reverse_of_true

abbrev yulExecUnOpErrorNotRelatable :=
  @Yul.Reference.SourceBridgeFacts.wrapped_yul_execUnOp_error_not_relatable

abbrev yulExecBinOpErrorNotRelatable :=
  @Yul.Reference.SourceBridgeFacts.wrapped_yul_execBinOp_error_not_relatable

abbrev yulExecTriOpErrorNotRelatable :=
  @Yul.Reference.SourceBridgeFacts.wrapped_yul_execTriOp_error_not_relatable

abbrev yulBinaryMachineStateOpErrorNotRelatable :=
  @Yul.Reference.SourceBridgeFacts.wrapped_yul_binaryMachineStateOp_error_not_relatable

abbrev yulTernaryMachineStateOpErrorNotRelatable :=
  @Yul.Reference.SourceBridgeFacts.wrapped_yul_ternaryMachineStateOp_error_not_relatable

abbrev yulBinaryStateOpErrorNotRelatable :=
  @Yul.Reference.SourceBridgeFacts.wrapped_yul_binaryStateOp_error_not_relatable

abbrev yulTernaryCopyOpErrorNotRelatable :=
  @Yul.Reference.SourceBridgeFacts.wrapped_yul_ternaryCopyOp_error_not_relatable

abbrev pureAliasPrimPrimCallErrorNotRelatable :=
  @Yul.Reference.SourceBridgeFacts.pureAliasPrim_primCall_error_not_relatable

abbrev safeBasicOneOutputPrimCallErrorNotRelatable :=
  @Yul.Reference.SourceBridgeFacts.safeBasicOneOutputPrimCall_error_not_relatable

abbrev safeBasicZeroOutputPrimCallErrorNotRelatable :=
  @Yul.Reference.SourceBridgeFacts.safeBasicZeroOutputPrimCall_error_not_relatable

abbrev directCallArgSafeEvalErrorNotRelatable :=
  @Yul.Reference.SourceBridgeFacts.directCallArgSafe_eval_error_not_relatable

abbrev directCallArgsSafeEvalArgsErrorNotRelatable :=
  @Yul.Reference.SourceBridgeFacts.directCallArgsSafe_evalArgs_error_not_relatable

abbrev sourceArgListPreludeTerminalAtDirect :=
  @Yul.Reference.SourceBridgeFacts.sourceArgListPreludeTerminalAt_direct

abbrev sourceExprPreludeTerminalAtDirect :=
  @Yul.Reference.SourceBridgeFacts.sourceExprPreludeTerminalAt_direct

abbrev sourceExprPreludeTerminalAtPrimOfArgsTerminal :=
  @Yul.Reference.SourceBridgeFacts.sourceExprPreludeTerminalAt_prim_of_args_terminal

abbrev sourceExprPreludeTerminalAtOfLower1?ProgramAcceptedRecursiveOk :=
  @Yul.Reference.SourceBridgeFacts.sourceExprPreludeTerminalAt_of_lower1?_program_accepted_recursive_ok

abbrev sourceExprPreludeTerminalAtOfLower1?ProgramAcceptedRecursive :=
  @Yul.Reference.SourceBridgeFacts.sourceExprPreludeTerminalAt_of_lower1?_program_accepted_recursive

abbrev sourceExprPreludeTerminalAtOfLower1?ProgramAcceptedRecursiveOfArgRegularAllAt :=
  @Yul.Reference.SourceBridgeFacts.sourceExprPreludeTerminalAt_of_lower1?_program_accepted_recursive_of_argRegularAllAt

abbrev sourceExprPreludeTerminalAtOfLower1?ProgramAcceptedRecursiveOkChecked :=
  @Yul.Reference.SourceBridgeFacts.sourceExprPreludeTerminalAt_of_lower1?_program_accepted_recursive_ok_checked

abbrev sourceExprPreludeTerminalAtOfLower1?ProgramAcceptedRecursiveChecked :=
  @Yul.Reference.SourceBridgeFacts.sourceExprPreludeTerminalAt_of_lower1?_program_accepted_recursive_checked

abbrev sourceExprPreludeTerminalAtOfLower1?ProgramAcceptedRecursiveOfArgRegularAllCheckedAt :=
  @Yul.Reference.SourceBridgeFacts.sourceExprPreludeTerminalAt_of_lower1?_program_accepted_recursive_of_argRegularAllCheckedAt

abbrev evalUserCallErrorSplitOfRelatable :=
  @Yul.Reference.SourceBridgeFacts.eval_user_call_error_split_of_relatable

abbrev evalUserCallOkSplit :=
  @Yul.Reference.SourceBridgeFacts.eval_user_call_ok_split

abbrev sourceExprPreludeTerminalAtUserCallGeneratedOfProgramRecursiveError :=
  @Yul.Reference.SourceBridgeFacts.sourceExprPreludeTerminalAt_user_call_generated_of_program_recursive_error

abbrev sourceExprPreludeTerminalAtUserCallDirectOfProgramRecursiveError :=
  @Yul.Reference.SourceBridgeFacts.sourceExprPreludeTerminalAt_user_call_direct_of_program_recursive_error

abbrev sourceArgListPreludeRegularToAt :=
  @Yul.Reference.SourceBridgeFacts.SourceArgListPreludeRegular.toAt

abbrev sourceArgListPreludeRegularAtRunExactOfDomain :=
  @Yul.Reference.SourceBridgeFacts.SourceArgListPreludeRegularAt.run_exact_of_domain

abbrev sourceArgListPreludeRegularRunExactOfDomain :=
  @Yul.Reference.SourceBridgeFacts.SourceArgListPreludeRegular.run_exact_of_domain

abbrev sourceArgStackPreludeRegularRunPreContainsOfDomain :=
  @Yul.Reference.SourceBridgeFacts.SourceArgStackPreludeRegular.run_preContains_of_domain

abbrev sourceArgStackPreludeRegularRunExactOfDomain :=
  @Yul.Reference.SourceBridgeFacts.SourceArgStackPreludeRegular.run_exact_of_domain

abbrev sourceArgStackPreludeRegularRunPreContainsOfEvalOkDomain :=
  @Yul.Reference.SourceBridgeFacts.SourceArgStackPreludeRegular.run_preContains_of_eval_ok_domain

abbrev sourceArgStackPreludeRegularRunExactOfEvalOkDomain :=
  @Yul.Reference.SourceBridgeFacts.SourceArgStackPreludeRegular.run_exact_of_eval_ok_domain

abbrev lower1PrimExprValuePreludeSoundOfLowerBound1PreludeRegular :=
  @Yul.Reference.SourceBridgeFacts.lower1?_prim_exprValuePreludeSound_of_lowerBound1?_preludeRegular

abbrev lower0PrimExprValuePreludeSoundOfLowerBound1PreludeRegular :=
  @Yul.Reference.SourceBridgeFacts.lower0?_prim_exprValuePreludeSound_of_lowerBound1?_preludeRegular

abbrev sourceRegularSeqRunBridgeHiddenConsLetPrimOfLowerPreludeRegular :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularSeqRunBridgeHidden_cons_let_prim_of_lower_preludeRegular

abbrev sourceRegularSeqRunBridgeHiddenConsAssignPrimOfLowerPreludeRegular :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularSeqRunBridgeHidden_cons_assign_prim_of_lower_preludeRegular

abbrev sourceRegularSeqRunBridgeHiddenConsExprPrimOfLowerPreludeRegular :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularSeqRunBridgeHidden_cons_expr_prim_of_lower_preludeRegular

abbrev sourceRegularSeqRunBridgeHiddenConsLetExprPreludeGeneral :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularSeqRunBridgeHidden_cons_let_expr_prelude_general

abbrev sourceRegularSeqRunBridgeHiddenConsAssignExprPreludeGeneral :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularSeqRunBridgeHidden_cons_assign_expr_prelude_general

abbrev sourceRegularSeqRunBridgeHiddenConsAssignExprPreludeGeneralOfDomainAfter :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularSeqRunBridgeHidden_cons_assign_expr_prelude_general_of_domainAfter

abbrev sourceRegularSeqRunBridgeHiddenConsAssignExprPreludeGeneralOfEvalDomain :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularSeqRunBridgeHidden_cons_assign_expr_prelude_general_of_eval_domain

abbrev sourceRegularSeqRunBridgeHiddenConsExprPrimPreludeGeneral :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularSeqRunBridgeHidden_cons_expr_prim_prelude_general

abbrev sourceCallSingletonRunOpenRegularOfRunBody :=
  @Yul.Reference.SourceBridgeFacts.sourceCallSingletonRunOpen_regular_of_runBody

abbrev sourceCallSingletonRunOpenHaltedOfRunBody :=
  @Yul.Reference.SourceBridgeFacts.sourceCallSingletonRunOpen_halted_of_runBody

abbrev sourceCallNoTargetsSingletonRunOpenRegularOfRunBodyNilReturns :=
  @Yul.Reference.SourceBridgeFacts.sourceCallNoTargetsSingletonRunOpen_regular_of_runBody_nil_returns

abbrev sourceCallNoTargetsSingletonRunOpenRegularOfRunBodyNilReturnsShared :=
  @Yul.Reference.SourceBridgeFacts.sourceCallNoTargetsSingletonRunOpen_regular_of_runBody_nil_returns_shared

abbrev sourceNoTargetUserCallRegularOfRunBodyRevive :=
  @Yul.Reference.SourceBridgeFacts.sourceNoTargetUserCall_regular_of_runBody_revive

abbrev sourceNoTargetUserCallRegularOfExecCallBodySound :=
  @Yul.Reference.SourceBridgeFacts.sourceNoTargetUserCall_regular_of_execCall_bodySound

abbrev sourceAssignUserCallRegularOfExecCallBodySound :=
  @Yul.Reference.SourceBridgeFacts.sourceAssignUserCall_regular_of_execCall_bodySound

abbrev sourceLetUserCallRegularOfExecCallBodySound :=
  @Yul.Reference.SourceBridgeFacts.sourceLetUserCall_regular_of_execCall_bodySound

abbrev sourceUserCallTerminalOfBodySoundError :=
  @Yul.Reference.SourceBridgeFacts.sourceUserCall_terminal_of_bodySound_error

abbrev execAssignUserCallErrorExecCallOfEvalArgsRelatable :=
  @Yul.Reference.SourceBridgeFacts.exec_assign_user_call_error_execCall_of_evalArgs_relatable

abbrev execAssignUserCallOkExecCallOfEvalArgs :=
  @Yul.Reference.SourceBridgeFacts.exec_assign_user_call_ok_execCall_of_evalArgs

abbrev execAssignUserCallOkCheckAssignmentOfEvalArgs :=
  @Yul.Reference.SourceBridgeFacts.exec_assign_user_call_ok_checkAssignment_of_evalArgs

abbrev execAssignUserCallErrorCheckAssignmentOfEvalArgsRelatable :=
  @Yul.Reference.SourceBridgeFacts.exec_assign_user_call_error_checkAssignment_of_evalArgs_relatable

abbrev execLetUserCallErrorExecCallOfEvalArgsRelatable :=
  @Yul.Reference.SourceBridgeFacts.exec_let_user_call_error_execCall_of_evalArgs_relatable

abbrev execLetUserCallOkExecCallOfEvalArgs :=
  @Yul.Reference.SourceBridgeFacts.exec_let_user_call_ok_execCall_of_evalArgs

abbrev checkedAssignUserCallBodySoundSuccess :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_assign_user_call_of_bodySound_success

abbrev checkedAssignUserCallRecursiveSuccess :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_assign_user_call_of_recursive_success

abbrev sourceCallSingletonRunOpenRegularOfBody :=
  @Yul.Reference.SourceBridgeFacts.sourceCallSingletonRunOpen_regular_of_body

abbrev sourceRegularSeqRunBridgeHiddenConsExprUserCallPreludeRegular :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularSeqRunBridgeHidden_cons_expr_user_call_prelude_regular

abbrev sourceRegularSeqRunBridgeHiddenConsLetUserCallPreludeRegular :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularSeqRunBridgeHidden_cons_let_user_call_prelude_regular

abbrev sourceRegularSeqRunBridgeHiddenConsAssignUserCallPreludeRegular :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularSeqRunBridgeHidden_cons_assign_user_call_prelude_regular

abbrev sourceRegularSeqRunBridgeHiddenNil :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularSeqRunBridgeHidden_nil

abbrev sourceRegularSeqRunBridgeHiddenConsLetPrimOfLowerPreludeRegularGeneral :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularSeqRunBridgeHidden_cons_let_prim_of_lower_preludeRegular_general

abbrev sourceRegularSeqRunBridgeHiddenConsAssignPrimOfLowerPreludeRegularGeneral :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularSeqRunBridgeHidden_cons_assign_prim_of_lower_preludeRegular_general

abbrev sourceRegularSeqRunBridgeHiddenConsAssignPrimOfLowerPreludeRegularGeneralOfDomainAfter :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularSeqRunBridgeHidden_cons_assign_prim_of_lower_preludeRegular_general_of_domainAfter

abbrev sourceRegularSeqRunBridgeHiddenConsAssignPrimOfLowerPreludeRegularGeneralOfEvalDomain :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularSeqRunBridgeHidden_cons_assign_prim_of_lower_preludeRegular_general_of_eval_domain

abbrev sourceRegularSeqRunBridgeHiddenConsExprPrimOfLowerPreludeRegularGeneral :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularSeqRunBridgeHidden_cons_expr_prim_of_lower_preludeRegular_general

abbrev sourceRegularSeqRunBridgeHiddenSingleExprPrimOfLowerPreludeRegularGeneral :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularSeqRunBridgeHidden_single_expr_prim_of_lower_preludeRegular_general

abbrev sourceResultBlockSoundWhenAtExactOfRegularSeqRunBridgeHiddenExact :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSoundWhenAtExact_of_regularSeqRunBridgeHidden_exact

abbrev sourceResultBlockSoundWhenAtExactOfRegularSeqRunBridgeHiddenExactCompat :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSoundWhenAtExact_of_regularSeqRunBridgeHidden_exact_compat

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactOfRegularSeqRunBridgeHiddenExactCompat :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_of_regularSeqRunBridgeHidden_exact_compat

abbrev sourceArgPreludeRegularRunTerminalArgsGeneral :=
  @Yul.Reference.SourceBridgeFacts.SourceArgPreludeRegular.run_terminalArgs_general

abbrev sourceArgStackPreludeRegularRunTerminalArgsGeneral :=
  @Yul.Reference.SourceBridgeFacts.SourceArgStackPreludeRegular.run_terminalArgs_general

abbrev sourceArgPreludeRegularRunScopedTerminalArgsGeneral :=
  @Yul.Reference.SourceBridgeFacts.SourceArgPreludeRegular.runScoped_terminalArgs_general

abbrev sourceArgStackPreludeRegularRunScopedTerminalArgsGeneral :=
  @Yul.Reference.SourceBridgeFacts.SourceArgStackPreludeRegular.runScoped_terminalArgs_general

abbrev sourceResultBlockSoundWhenAtTerminalStackPreludeOfPreludeRegularGeneral :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSoundWhenAt_terminalStackPrelude_of_preludeRegular_general

abbrev sourceResultBlockSoundWhenAtTerminalStackPreludeOfExprArgSoundGeneral :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSoundWhenAt_terminalStackPrelude_of_exprArgSound_general

abbrev sourceResultBlockSoundWhenAtExactConsTerminalStackPreludeOfPreludeRegularGeneral :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSoundWhenAtExact_cons_terminalStackPrelude_of_preludeRegular_general

abbrev sourceResultBlockSoundWhenAtCallUserTerminalPreludeRegular :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSoundWhenAt_call_user_terminal_prelude_regular

abbrev sourceResultBlockSoundWhenAtCallUserActualPreludeRegular :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSoundWhenAt_call_user_actual_prelude_regular

abbrev sourceResultBlockSoundWhenAtExactCallUserArgTerminalPrelude :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSoundWhenAtExact_call_user_arg_terminal_prelude

abbrev sourceResultBlockSoundWhenAtExactArgTerminalPreludeSuffix :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSoundWhenAtExact_arg_terminal_prelude_suffix

abbrev sourceResultBlockSoundWhenAtExactCallUserActualOrArgTerminalPrelude :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSoundWhenAtExact_call_user_actual_or_arg_terminal_prelude

abbrev sourceResultBlockSoundWhenAtExactCallUserActualPreludeRegular :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSoundWhenAtExact_call_user_actual_prelude_regular

abbrev sourceResultBlockSoundWhenAtExactExprUserCallActualPreludeRegular :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSoundWhenAtExact_expr_user_call_actual_prelude_regular

abbrev sourceResultBlockSoundWhenAtExactExprUserCallActualOrArgTerminalPrelude :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSoundWhenAtExact_expr_user_call_actual_or_arg_terminal_prelude

abbrev sourceResultBlockSoundWhenAtExactExprUserCallActualOrArgTerminalPreludeAccepted :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSoundWhenAtExact_expr_user_call_actual_or_arg_terminal_prelude_accepted

abbrev sourceResultBlockSoundWhenAtExactAssignUserCallActualPreludeRegular :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSoundWhenAtExact_assign_user_call_actual_prelude_regular

abbrev sourceResultBlockSoundWhenAtExactAssignUserCallActualOrArgTerminalPrelude :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSoundWhenAtExact_assign_user_call_actual_or_arg_terminal_prelude

abbrev sourceResultBlockSoundWhenAtExactAssignUserCallActualOrArgTerminalPreludeAccepted :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSoundWhenAtExact_assign_user_call_actual_or_arg_terminal_prelude_accepted

abbrev sourceResultBlockSoundWhenAtLetUserTerminalPreludeRegular :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSoundWhenAt_let_user_terminal_prelude_regular

abbrev sourceResultBlockSoundWhenAtExactLetUserCallActualPreludeRegular :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSoundWhenAtExact_let_user_call_actual_prelude_regular

abbrev sourceResultBlockSoundWhenAtExactLetUserCallActualOrArgTerminalPrelude :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSoundWhenAtExact_let_user_call_actual_or_arg_terminal_prelude

abbrev checkedStmtBlockLoweringSoundWhenFreshAtTerminalStackPreludeOfPreludeRegular :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshAt_terminalStackPrelude_of_preludeRegular

abbrev checkedStmtBlockLoweringSoundWhenFreshAtExactTerminalStackPreludeOfPreludeRegular :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshAtExact_terminalStackPrelude_of_preludeRegular

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactTerminalStackPreludeOfPreludeRegular :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_terminalStackPrelude_of_preludeRegular

abbrev checkedStmtBlockLoweringSoundWhenFreshAtTerminalStackPreludeOfExprArgSound :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshAt_terminalStackPrelude_of_exprArgSound

abbrev checkedStmtBlockLoweringSoundWhenFreshAtExactTerminalStackPreludeOfExprArgSound :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshAtExact_terminalStackPrelude_of_exprArgSound

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactTerminalStackPreludeOfExprArgSound :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_terminalStackPrelude_of_exprArgSound

abbrev checkedStmtBlockLoweringSoundWhenFreshAtTerminalStackPreludeOfPreludeRegularGeneral :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshAt_terminalStackPrelude_of_preludeRegular_general

abbrev checkedStmtBlockLoweringSoundWhenFreshAtExactTerminalStackPreludeOfPreludeRegularGeneral :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshAtExact_terminalStackPrelude_of_preludeRegular_general

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactTerminalStackPreludeOfPreludeRegularGeneral :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_terminalStackPrelude_of_preludeRegular_general

abbrev checkedStmtBlockLoweringSoundWhenFreshAtTerminalStackPreludeOfExprArgSoundGeneral :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshAt_terminalStackPrelude_of_exprArgSound_general

abbrev checkedStmtBlockLoweringSoundWhenFreshAtExactTerminalStackPreludeOfExprArgSoundGeneral :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshAtExact_terminalStackPrelude_of_exprArgSound_general

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactTerminalStackPreludeOfExprArgSoundGeneral :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_terminalStackPrelude_of_exprArgSound_general

abbrev checkedBlockLoweringSoundWhenFreshAtExactConsTerminalStackPreludeOfPreludeRegularGeneral :=
  @Yul.Reference.SourceBridgeFacts.checkedBlockLoweringSoundWhenFreshAtExact_cons_terminalStackPrelude_of_preludeRegular_general

abbrev checkedBlockLoweringSoundWhenFreshNamesAtExactConsTerminalStackPreludeOfPreludeRegularGeneral :=
  @Yul.Reference.SourceBridgeFacts.checkedBlockLoweringSoundWhenFreshNamesAtExact_cons_terminalStackPrelude_of_preludeRegular_general

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactStopCall :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_stop_call

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactExprPrimOfPreludeRegularSuccess :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_expr_prim_of_preludeRegular_success

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactExprPrimOfArgTerminal :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_expr_prim_of_arg_terminal

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactExprPrimActualOrArgTerminal :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_expr_prim_actual_or_arg_terminal

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactLetPrimOfPreludeRegularSuccess :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_let_prim_of_preludeRegular_success

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactLetPrimOfArgTerminal :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_let_prim_of_arg_terminal

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactLetPrimActualOrArgTerminal :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_let_prim_actual_or_arg_terminal

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactAssignPrimOfPreludeRegularSuccess :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_assign_prim_of_preludeRegular_success

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactAssignPrimOfArgTerminal :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_assign_prim_of_arg_terminal

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactAssignPrimActualOrArgTerminal :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_assign_prim_actual_or_arg_terminal

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactExprUserCallOfPreludeRegularSuccess :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_expr_user_call_of_preludeRegular_success

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactExprUserCallOfBodySoundSuccess :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_expr_user_call_of_bodySound_success

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactExprUserCallOfRecursiveSuccess :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_expr_user_call_of_recursive_success

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactExprUserCallOfProgramRecursiveSuccess :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_expr_user_call_of_program_recursive_success

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactExprUserCallOfProgramRecursiveSuccessScoped :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_expr_user_call_of_program_recursive_success_scoped

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactExprUserCallTerminalOfPreludeRegular :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_expr_user_call_terminal_of_preludeRegular

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactExprUserCallTerminalOfBodySoundError :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_expr_user_call_terminal_of_bodySound_error

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactExprUserCallTerminalOfRecursiveError :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_expr_user_call_terminal_of_recursive_error

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactExprUserCallTerminalOfProgramRecursiveError :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_expr_user_call_terminal_of_program_recursive_error

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactExprUserCallOfProgramRecursiveActual :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_expr_user_call_of_program_recursive_actual

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactExprUserCallOfProgramRecursiveActualOrArgTerminal :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_expr_user_call_of_program_recursive_actual_or_arg_terminal

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactExprUserCallOfProgramRecursiveActualSucc :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_expr_user_call_of_program_recursive_actual_succ

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactExprUserCallOfProgramRecursiveActualOrArgTerminalSucc :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_expr_user_call_of_program_recursive_actual_or_arg_terminal_succ

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactExprUserCallOfProgramRecursiveActualOrArgTerminalSuccOfExprTerminal :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_expr_user_call_of_program_recursive_actual_or_arg_terminal_succ_of_exprTerminal

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactExprUserCallOfProgramAcceptedRecursiveActualOrArgTerminal :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_expr_user_call_of_program_accepted_recursive_actual_or_arg_terminal

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactExprUserCallOfProgramAcceptedRecursiveActualOrArgTerminalSucc :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_expr_user_call_of_program_accepted_recursive_actual_or_arg_terminal_succ

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactExprUserCallOfProgramAcceptedRecursiveActualOrArgTerminalSuccOfExprTerminal :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_expr_user_call_of_program_accepted_recursive_actual_or_arg_terminal_succ_of_exprTerminal

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactExprUserCallOfProgramAcceptedRecursiveActualOrArgTerminalSuccOfExprOkTerminal :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_expr_user_call_of_program_accepted_recursive_actual_or_arg_terminal_succ_of_exprOkTerminal

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactExprUserCallOfProgramAcceptedRecursiveActualOrArgTerminalSuccOfExprOkTerminalChecked :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_expr_user_call_of_program_accepted_recursive_actual_or_arg_terminal_succ_of_exprOkTerminalChecked

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactExprUserCallOfProgramAcceptedRecursiveActualOrArgTerminalSuccOfRecursiveExprTerminal :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_expr_user_call_of_program_accepted_recursive_actual_or_arg_terminal_succ_of_recursiveExprTerminal

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactExprUserCallOfProgramAcceptedRecursiveActualOrArgTerminalSuccOfRecursiveExprTerminalChecked :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_expr_user_call_of_program_accepted_recursive_actual_or_arg_terminal_succ_of_recursiveExprTerminalChecked

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactExprUserCallOfProgramAcceptedRecursiveActualOrArgTerminalSuccOfArgRegularAllAt :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_expr_user_call_of_program_accepted_recursive_actual_or_arg_terminal_succ_of_argRegularAllAt

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactExprUserCallOfProgramAcceptedRecursiveActualOrArgTerminalSuccOfArgRegularAllCheckedAt :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_expr_user_call_of_program_accepted_recursive_actual_or_arg_terminal_succ_of_argRegularAllCheckedAt

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactExprUserCallOfProgramAcceptedRecursiveActualOrArgTerminalSuccOfArgRegularAllCheckedAtSourceScoped :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_expr_user_call_of_program_accepted_recursive_actual_or_arg_terminal_succ_of_argRegularAllCheckedAt_sourceScoped

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactExprUserCallOfProgramAcceptedRecursiveActualOrArgTerminalFrontier :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_expr_user_call_of_program_accepted_recursive_actual_or_arg_terminal_frontier

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactAssignUserCallOfPreludeRegularSuccess :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_assign_user_call_of_preludeRegular_success

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactAssignUserCallOfBodySoundSuccess :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_assign_user_call_of_bodySound_success

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactAssignUserCallOfRecursiveSuccess :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_assign_user_call_of_recursive_success

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactAssignUserCallOfProgramRecursiveSuccess :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_assign_user_call_of_program_recursive_success

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactAssignUserCallOfProgramRecursiveSuccessScoped :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_assign_user_call_of_program_recursive_success_scoped

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactAssignUserCallOfProgramRecursiveActual :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_assign_user_call_of_program_recursive_actual

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactAssignUserCallOfProgramRecursiveActualOrArgTerminal :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_assign_user_call_of_program_recursive_actual_or_arg_terminal

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactAssignUserCallOfProgramRecursiveActualSucc :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_assign_user_call_of_program_recursive_actual_succ

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactAssignUserCallOfProgramRecursiveActualOrArgTerminalSucc :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_assign_user_call_of_program_recursive_actual_or_arg_terminal_succ

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactAssignUserCallOfProgramRecursiveActualOrArgTerminalSuccOfExprTerminal :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_assign_user_call_of_program_recursive_actual_or_arg_terminal_succ_of_exprTerminal

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactAssignUserCallOfProgramAcceptedRecursiveActualOrArgTerminal :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_assign_user_call_of_program_accepted_recursive_actual_or_arg_terminal

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactAssignUserCallOfProgramAcceptedRecursiveActualOrArgTerminalSucc :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_assign_user_call_of_program_accepted_recursive_actual_or_arg_terminal_succ

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactAssignUserCallOfProgramAcceptedRecursiveActualOrArgTerminalSuccOfExprTerminal :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_assign_user_call_of_program_accepted_recursive_actual_or_arg_terminal_succ_of_exprTerminal

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactAssignUserCallOfProgramAcceptedRecursiveActualOrArgTerminalSuccOfExprOkTerminal :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_assign_user_call_of_program_accepted_recursive_actual_or_arg_terminal_succ_of_exprOkTerminal

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactAssignUserCallOfProgramAcceptedRecursiveActualOrArgTerminalSuccOfExprOkTerminalChecked :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_assign_user_call_of_program_accepted_recursive_actual_or_arg_terminal_succ_of_exprOkTerminalChecked

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactAssignUserCallOfProgramAcceptedRecursiveActualOrArgTerminalSuccOfRecursiveExprTerminal :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_assign_user_call_of_program_accepted_recursive_actual_or_arg_terminal_succ_of_recursiveExprTerminal

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactAssignUserCallOfProgramAcceptedRecursiveActualOrArgTerminalSuccOfRecursiveExprTerminalChecked :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_assign_user_call_of_program_accepted_recursive_actual_or_arg_terminal_succ_of_recursiveExprTerminalChecked

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactAssignUserCallOfProgramAcceptedRecursiveActualOrArgTerminalSuccOfArgRegularAllAt :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_assign_user_call_of_program_accepted_recursive_actual_or_arg_terminal_succ_of_argRegularAllAt

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactAssignUserCallOfProgramAcceptedRecursiveActualOrArgTerminalSuccOfArgRegularAllCheckedAt :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_assign_user_call_of_program_accepted_recursive_actual_or_arg_terminal_succ_of_argRegularAllCheckedAt

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactAssignUserCallOfProgramAcceptedRecursiveActualOrArgTerminalSuccOfArgRegularAllCheckedAtSourceScoped :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_assign_user_call_of_program_accepted_recursive_actual_or_arg_terminal_succ_of_argRegularAllCheckedAt_sourceScoped

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactAssignUserCallOfProgramAcceptedRecursiveActualOrArgTerminalSuccOfArgRegularAllCheckedAtSourceScopedAutoTargets :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_assign_user_call_of_program_accepted_recursive_actual_or_arg_terminal_succ_of_argRegularAllCheckedAt_sourceScoped_autoTargets

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactAssignUserCallOfProgramAcceptedRecursiveActualOrArgTerminalFrontier :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_assign_user_call_of_program_accepted_recursive_actual_or_arg_terminal_frontier

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactAssignUserCallTerminalOfPreludeRegular :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_assign_user_call_terminal_of_preludeRegular

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactAssignUserCallTerminalOfPreludeRegularAt :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_assign_user_call_terminal_of_preludeRegular_at

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactAssignUserCallTerminalOfBodySoundError :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_assign_user_call_terminal_of_bodySound_error

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactAssignUserCallTerminalOfRecursiveError :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_assign_user_call_terminal_of_recursive_error

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactAssignUserCallTerminalOfRecursiveErrorAt :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_assign_user_call_terminal_of_recursive_error_at

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactAssignUserCallTerminalOfProgramRecursiveErrorAt :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_assign_user_call_terminal_of_program_recursive_error_at

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactLetUserCallOfPreludeRegularSuccess :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_let_user_call_of_preludeRegular_success

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactLetUserCallOfBodySoundSuccess :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_let_user_call_of_bodySound_success

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactLetUserCallOfRecursiveSuccess :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_let_user_call_of_recursive_success

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactLetUserCallOfProgramRecursiveSuccess :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_let_user_call_of_program_recursive_success

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactLetUserCallOfProgramRecursiveSuccessScoped :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_let_user_call_of_program_recursive_success_scoped

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactLetUserCallOfProgramRecursiveActual :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_let_user_call_of_program_recursive_actual

abbrev letUserCallSuccessContinuationOfProgramRecursive :=
  @Yul.Reference.SourceBridgeFacts.let_user_call_success_continuation_of_program_recursive

abbrev letUserCallSuccessContinuationOfProgramAcceptedRecursive :=
  @Yul.Reference.SourceBridgeFacts.let_user_call_success_continuation_of_program_accepted_recursive

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactLetUserCallOfProgramRecursiveActualOrArgTerminal :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_let_user_call_of_program_recursive_actual_or_arg_terminal

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactLetUserCallOfProgramAcceptedRecursiveActualOrArgTerminal :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_let_user_call_of_program_accepted_recursive_actual_or_arg_terminal

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactLetUserCallOfProgramRecursiveActualOrArgTerminalSucc :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_let_user_call_of_program_recursive_actual_or_arg_terminal_succ

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactLetUserCallOfProgramAcceptedRecursiveActualOrArgTerminalSucc :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_let_user_call_of_program_accepted_recursive_actual_or_arg_terminal_succ

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactLetUserCallOfProgramRecursiveActualOrArgTerminalSuccOfExprTerminal :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_let_user_call_of_program_recursive_actual_or_arg_terminal_succ_of_exprTerminal

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactLetUserCallOfProgramAcceptedRecursiveActualOrArgTerminalSuccOfExprTerminal :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_let_user_call_of_program_accepted_recursive_actual_or_arg_terminal_succ_of_exprTerminal

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactLetUserCallOfProgramAcceptedRecursiveActualOrArgTerminalSuccOfExprOkTerminal :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_let_user_call_of_program_accepted_recursive_actual_or_arg_terminal_succ_of_exprOkTerminal

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactLetUserCallOfProgramAcceptedRecursiveActualOrArgTerminalSuccOfExprOkTerminalChecked :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_let_user_call_of_program_accepted_recursive_actual_or_arg_terminal_succ_of_exprOkTerminalChecked

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactLetUserCallOfProgramAcceptedRecursiveActualOrArgTerminalSuccOfRecursiveExprTerminal :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_let_user_call_of_program_accepted_recursive_actual_or_arg_terminal_succ_of_recursiveExprTerminal

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactLetUserCallOfProgramAcceptedRecursiveActualOrArgTerminalSuccOfRecursiveExprTerminalChecked :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_let_user_call_of_program_accepted_recursive_actual_or_arg_terminal_succ_of_recursiveExprTerminalChecked

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactLetUserCallOfProgramAcceptedRecursiveActualOrArgTerminalSuccOfArgRegularAllAt :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_let_user_call_of_program_accepted_recursive_actual_or_arg_terminal_succ_of_argRegularAllAt

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactLetUserCallOfProgramAcceptedRecursiveActualOrArgTerminalSuccOfArgRegularAllCheckedAt :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_let_user_call_of_program_accepted_recursive_actual_or_arg_terminal_succ_of_argRegularAllCheckedAt

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactLetUserCallOfProgramAcceptedRecursiveActualOrArgTerminalSuccOfArgRegularAllCheckedAtSourceScoped :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_let_user_call_of_program_accepted_recursive_actual_or_arg_terminal_succ_of_argRegularAllCheckedAt_sourceScoped

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactLetUserCallOfProgramAcceptedRecursiveActualOrArgTerminalSuccOfArgRegularAllCheckedAtSourceScopedAutoDecl :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_let_user_call_of_program_accepted_recursive_actual_or_arg_terminal_succ_of_argRegularAllCheckedAt_sourceScoped_autoDecl

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactLetUserCallOfProgramAcceptedRecursiveActualOrArgTerminalFrontier :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_let_user_call_of_program_accepted_recursive_actual_or_arg_terminal_frontier

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactOfNoLowering :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_of_no_lowering

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactOfProgramAcceptedFrontierExceptPrimitives :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_of_programAccepted_frontier_except_primitives

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactLetUserCallOfProgramRecursiveActualSucc :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_let_user_call_of_program_recursive_actual_succ

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactLetUserCallTerminalOfPreludeRegular :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_let_user_call_terminal_of_preludeRegular

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactLetUserCallTerminalOfPreludeRegularAt :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_let_user_call_terminal_of_preludeRegular_at

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactLetUserCallTerminalOfBodySoundError :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_let_user_call_terminal_of_bodySound_error

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactLetUserCallTerminalOfRecursiveError :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_let_user_call_terminal_of_recursive_error

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactLetUserCallTerminalOfRecursiveErrorAt :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_let_user_call_terminal_of_recursive_error_at

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactLetUserCallTerminalOfProgramRecursiveErrorAt :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_let_user_call_terminal_of_program_recursive_error_at

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactMstoreOfPreludeRegularSuccess :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_mstore_of_preludeRegular_success

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactMstore8OfPreludeRegularSuccess :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_mstore8_of_preludeRegular_success

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactMcopyOfPreludeRegularSuccess :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_mcopy_of_preludeRegular_success

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactCalldatacopyOfPreludeRegularSuccess :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_calldatacopy_of_preludeRegular_success

abbrev checkedStmtBlockLoweringSoundWhenFreshNamesAtExactReturndatacopyOfPreludeRegularSuccess :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_returndatacopy_of_preludeRegular_success

abbrev sourceResultBlockSoundWhenAtBreak :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSoundWhenAt_break

abbrev sourceResultBlockSoundWhenAtContinue :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSoundWhenAt_continue

abbrev sourceResultBlockSoundWhenAtLeave :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSoundWhenAt_leave

abbrev recursiveSourceBridgeUpTo :=
  @Yul.Reference.SourceBridgeFacts.RecursiveSourceBridgeUpTo

abbrev recursiveSourceBridgeWhenUpTo :=
  @Yul.Reference.SourceBridgeFacts.RecursiveSourceBridgeWhenUpTo

abbrev recursiveSourceBridgeWhenUpToAt :=
  @Yul.Reference.SourceBridgeFacts.RecursiveSourceBridgeWhenUpToAt

abbrev sourceArgEvalRegularSnocLiteralEmptyPrelude :=
  @Yul.Reference.SourceBridgeFacts.sourceArgEvalRegular_snoc_lit_empty_prelude

abbrev sourceArgEvalRegularSnocVariableEmptyPrelude :=
  @Yul.Reference.SourceBridgeFacts.sourceArgEvalRegular_snoc_var_empty_prelude

abbrev sourceArgEvalRegularPairLiteralVariable :=
  @Yul.Reference.SourceBridgeFacts.sourceArgEvalRegular_pair_lit_var

abbrev sourceArgEvalRegularPairVariableLiteral :=
  @Yul.Reference.SourceBridgeFacts.sourceArgEvalRegular_pair_var_lit

abbrev sourceArgSimple :=
  @Yul.Reference.SourceBridgeFacts.SourceArgSimple

abbrev sourceArgSimpleFuel :=
  @Yul.Reference.SourceBridgeFacts.sourceArgSimpleFuel

abbrev sourceArgEvalRegularSimpleEmptyPrelude :=
  @Yul.Reference.SourceBridgeFacts.sourceArgEvalRegular_simple_empty_prelude

abbrev checkedStmtBlockLoweringSoundFreshOfRecursiveSourceBridgeUpTo :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundFresh_of_recursiveSourceBridgeUpTo

abbrev checkedBlockLoweringSoundFreshOfRecursiveSourceBridgeUpTo :=
  @Yul.Reference.SourceBridgeFacts.checkedBlockLoweringSoundFresh_of_recursiveSourceBridgeUpTo

abbrev checkedStmtBlockLoweringSoundWhenFreshOfRecursiveSourceBridgeWhenUpTo :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFresh_of_recursiveSourceBridgeWhenUpTo

abbrev checkedBlockLoweringSoundWhenFreshOfRecursiveSourceBridgeWhenUpTo :=
  @Yul.Reference.SourceBridgeFacts.checkedBlockLoweringSoundWhenFresh_of_recursiveSourceBridgeWhenUpTo

abbrev checkedStmtBlockLoweringSoundWhenFreshAtOfRecursiveSourceBridgeWhenUpToAt :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshAt_of_recursiveSourceBridgeWhenUpToAt

abbrev checkedBlockLoweringSoundWhenFreshAtOfRecursiveSourceBridgeWhenUpToAt :=
  @Yul.Reference.SourceBridgeFacts.checkedBlockLoweringSoundWhenFreshAt_of_recursiveSourceBridgeWhenUpToAt

abbrev recursiveSourceBridgeWhenUpToOfRecursiveSourceBridgeWhenUpToAt :=
  @Yul.Reference.SourceBridgeFacts.recursiveSourceBridgeWhenUpTo_of_recursiveSourceBridgeWhenUpToAt

abbrev recursiveSourceBridgeWhenUpToOfRecursiveSourceBridgeUpTo :=
  @Yul.Reference.SourceBridgeFacts.recursiveSourceBridgeWhenUpTo_of_recursiveSourceBridgeUpTo

abbrev checkedStmtBlockLoweringSoundFreshOfChecked :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundFresh_of_checked

abbrev checkedBlockLoweringSoundWhenOfChecked :=
  @Yul.Reference.SourceBridgeFacts.checkedBlockLoweringSoundWhen_of_checked

abbrev checkedBlockLoweringSoundWhenFreshOfCheckedFresh :=
  @Yul.Reference.SourceBridgeFacts.checkedBlockLoweringSoundWhenFresh_of_checkedFresh

abbrev checkedBlockLoweringSoundWhenFreshOfWhen :=
  @Yul.Reference.SourceBridgeFacts.checkedBlockLoweringSoundWhenFresh_of_when

abbrev checkedBlockLoweringSoundWhenFreshAtOfWhen :=
  @Yul.Reference.SourceBridgeFacts.checkedBlockLoweringSoundWhenFreshAt_of_when

abbrev checkedBlockLoweringSoundWhenFreshNil :=
  @Yul.Reference.SourceBridgeFacts.checkedBlockLoweringSoundWhenFresh_nil

abbrev checkedBlockLoweringSoundWhenFreshAtNil :=
  @Yul.Reference.SourceBridgeFacts.checkedBlockLoweringSoundWhenFreshAt_nil

abbrev checkedSeqLoweringSoundWhenFreshAtNil :=
  @Yul.Reference.SourceBridgeFacts.checkedSeqLoweringSoundWhenFreshAt_nil

abbrev checkedSeqLoweringSoundWhenFreshAtOfCompileFuel :=
  @Yul.Reference.SourceBridgeFacts.checkedSeqLoweringSoundWhenFreshAt_of_compileFuel

abbrev checkedSeqLoweringSoundWhenFreshAtCompileFuelNil :=
  @Yul.Reference.SourceBridgeFacts.checkedSeqLoweringSoundWhenFreshAtCompileFuel_nil

abbrev checkedSeqLoweringSoundWhenFreshAtCompileFuelExactNil :=
  @Yul.Reference.SourceBridgeFacts.checkedSeqLoweringSoundWhenFreshAtCompileFuelExact_nil

abbrev checkedSeqLoweringSoundWhenFreshAtCompileFuelConsRegularStmtSingle :=
  @Yul.Reference.BridgeFacts.checkedSeqLoweringSoundWhenFreshAtCompileFuel_cons_regular_stmt_single

abbrev checkedSeqLoweringSoundWhenFreshAtCompileFuelExactConsRegularStmtSingle :=
  @Yul.Reference.BridgeFacts.checkedSeqLoweringSoundWhenFreshAtCompileFuelExact_cons_regular_stmt_single

abbrev checkedSeqLoweringSoundWhenFreshAtCompileFuelParamExactConsRegularStmtSingle :=
  @Yul.Reference.SourceBridgeFacts.checkedSeqLoweringSoundWhenFreshAtCompileFuelParamExact_cons_regular_stmt_single

abbrev checkedSeqLoweringSoundWhenFreshAtCompileFuelParamExactConsAssignLitSingle :=
  @Yul.Reference.SourceBridgeFacts.checkedSeqLoweringSoundWhenFreshAtCompileFuelParamExact_cons_assign_lit_single

abbrev checkedSeqLoweringSoundWhenFreshAtCompileFuelParamExactConsAssignVarSingle :=
  @Yul.Reference.SourceBridgeFacts.checkedSeqLoweringSoundWhenFreshAtCompileFuelParamExact_cons_assign_var_single

abbrev checkedSeqLoweringSoundWhenFreshAtCompileFuelParamExactConsLetNoneSingle :=
  @Yul.Reference.SourceBridgeFacts.checkedSeqLoweringSoundWhenFreshAtCompileFuelParamExact_cons_let_none_single

abbrev checkedSeqLoweringSoundWhenFreshAtCompileFuelParamExactConsLetLitSingle :=
  @Yul.Reference.SourceBridgeFacts.checkedSeqLoweringSoundWhenFreshAtCompileFuelParamExact_cons_let_lit_single

abbrev checkedSeqLoweringSoundWhenFreshAtCompileFuelParamExactConsLetVarSingle :=
  @Yul.Reference.SourceBridgeFacts.checkedSeqLoweringSoundWhenFreshAtCompileFuelParamExact_cons_let_var_single

abbrev checkedSeqLoweringSoundWhenFreshAtCompileFuelExactConsAssignLitSingle :=
  @Yul.Reference.BridgeFacts.checkedSeqLoweringSoundWhenFreshAtCompileFuelExact_cons_assign_lit_single

abbrev checkedSeqLoweringSoundWhenFreshAtCompileFuelExactConsAssignVarSingle :=
  @Yul.Reference.BridgeFacts.checkedSeqLoweringSoundWhenFreshAtCompileFuelExact_cons_assign_var_single

abbrev checkedSeqLoweringSoundWhenFreshAtCompileFuelExactConsLetNoneSingle :=
  @Yul.Reference.BridgeFacts.checkedSeqLoweringSoundWhenFreshAtCompileFuelExact_cons_let_none_single

abbrev checkedSeqLoweringSoundWhenFreshAtCompileFuelExactConsLetLitSingle :=
  @Yul.Reference.BridgeFacts.checkedSeqLoweringSoundWhenFreshAtCompileFuelExact_cons_let_lit_single

abbrev checkedSeqLoweringSoundWhenFreshAtCompileFuelExactConsLetVarSingle :=
  @Yul.Reference.BridgeFacts.checkedSeqLoweringSoundWhenFreshAtCompileFuelExact_cons_let_var_single

abbrev checkedRegularStmtSingletonSoundAtExactAssignLitSingle :=
  @Yul.Reference.BridgeFacts.checkedRegularStmtSingletonSoundAtExact_assign_lit_single

abbrev checkedRegularStmtSingletonSoundAtExactAssignVarSingle :=
  @Yul.Reference.BridgeFacts.checkedRegularStmtSingletonSoundAtExact_assign_var_single

abbrev checkedRegularStmtSingletonSoundAtExactLetNoneSingle :=
  @Yul.Reference.BridgeFacts.checkedRegularStmtSingletonSoundAtExact_let_none_single

abbrev checkedRegularStmtSingletonSoundAtExactLetLitSingle :=
  @Yul.Reference.BridgeFacts.checkedRegularStmtSingletonSoundAtExact_let_lit_single

abbrev checkedRegularStmtSingletonSoundAtExactLetVarSingle :=
  @Yul.Reference.BridgeFacts.checkedRegularStmtSingletonSoundAtExact_let_var_single

abbrev checkedSeqLoweringSoundWhenFreshAtConsBreak :=
  @Yul.Reference.SourceBridgeFacts.checkedSeqLoweringSoundWhenFreshAt_cons_break

abbrev checkedSeqLoweringSoundWhenFreshAtConsContinue :=
  @Yul.Reference.SourceBridgeFacts.checkedSeqLoweringSoundWhenFreshAt_cons_continue

abbrev checkedSeqLoweringSoundWhenFreshAtConsLeave :=
  @Yul.Reference.SourceBridgeFacts.checkedSeqLoweringSoundWhenFreshAt_cons_leave

abbrev checkedStmtBlockLoweringSoundWhenFreshAtBreak :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshAt_break

abbrev checkedStmtBlockLoweringSoundWhenFreshAtContinue :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshAt_continue

abbrev checkedStmtBlockLoweringSoundWhenFreshAtLeave :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshAt_leave

abbrev checkedStmtBlockLoweringSoundWhenOfChecked :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhen_of_checked

abbrev checkedStmtBlockLoweringSoundWhenFreshOfCheckedFresh :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFresh_of_checkedFresh

abbrev checkedStmtBlockLoweringSoundWhenFreshOfWhen :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFresh_of_when

abbrev checkedStmtBlockLoweringSoundWhenFreshAtOfWhen :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshAt_of_when

abbrev checkedDispatcherLoweringSound :=
  @Yul.Reference.SourceBridgeFacts.CheckedDispatcherLoweringSound

abbrev checkedDispatcherLoweringSoundWhen :=
  @Yul.Reference.SourceBridgeFacts.CheckedDispatcherLoweringSoundWhen

abbrev checkedDispatcherLoweringSoundOfStmtBlockLoweringSound :=
  @Yul.Reference.SourceBridgeFacts.checkedDispatcherLoweringSound_of_stmtBlockLoweringSound

abbrev checkedDispatcherLoweringSoundOfStmtBlockLoweringSoundFresh :=
  @Yul.Reference.SourceBridgeFacts.checkedDispatcherLoweringSound_of_stmtBlockLoweringSoundFresh

abbrev checkedDispatcherLoweringSoundWhenOfSound :=
  @Yul.Reference.SourceBridgeFacts.checkedDispatcherLoweringSoundWhen_of_sound

abbrev checkedDispatcherLoweringSoundWhenOfStmtBlockLoweringSoundWhen :=
  @Yul.Reference.SourceBridgeFacts.checkedDispatcherLoweringSoundWhen_of_stmtBlockLoweringSoundWhen

abbrev checkedDispatcherLoweringSoundWhenOfStmtBlockLoweringSoundWhenFresh :=
  @Yul.Reference.SourceBridgeFacts.checkedDispatcherLoweringSoundWhen_of_stmtBlockLoweringSoundWhenFresh

abbrev checkedStmtBlockLoweringSoundFreshSelfdestructLitCall :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundFresh_selfdestruct_lit_call

abbrev checkedStmtBlockLoweringSoundFreshReturnLitLitCall :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundFresh_return_lit_lit_call

abbrev checkedStmtBlockLoweringSoundFreshRevertLitLitCall :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundFresh_revert_lit_lit_call

abbrev checkedDispatcherLoweringSoundSelfdestructLitCall :=
  @Yul.Reference.SourceBridgeFacts.checkedDispatcherLoweringSound_selfdestruct_lit_call

abbrev checkedDispatcherLoweringSoundReturnLitLitCall :=
  @Yul.Reference.SourceBridgeFacts.checkedDispatcherLoweringSound_return_lit_lit_call

abbrev checkedDispatcherLoweringSoundRevertLitLitCall :=
  @Yul.Reference.SourceBridgeFacts.checkedDispatcherLoweringSound_revert_lit_lit_call

abbrev yulPrimitiveBinaryZeroSound :=
  @Yul.Reference.SourceBridgeFacts.YulPrimitiveBinaryZeroSound

abbrev sourcePrimitiveBinaryZeroSound :=
  @Yul.Reference.SourceBridgeFacts.SourcePrimitiveBinaryZeroSound

abbrev yulPrimitiveTernaryZeroSound :=
  @Yul.Reference.SourceBridgeFacts.YulPrimitiveTernaryZeroSound

abbrev sourcePrimitiveTernaryZeroSound :=
  @Yul.Reference.SourceBridgeFacts.SourcePrimitiveTernaryZeroSound

abbrev primitiveStackSoundAtOfBinaryZero :=
  @Yul.Reference.SourceBridgeFacts.primitiveStackSoundAt_of_binary_zero

abbrev primitiveStackSoundAtOfTernaryZero :=
  @Yul.Reference.SourceBridgeFacts.primitiveStackSoundAt_of_ternary_zero

abbrev primitiveStackSoundAtMstore :=
  @Yul.Reference.SourceBridgeFacts.primitiveStackSoundAt_mstore

abbrev primitiveStackSoundAtMstore8 :=
  @Yul.Reference.SourceBridgeFacts.primitiveStackSoundAt_mstore8

abbrev primitiveStackSoundAtMcopy :=
  @Yul.Reference.SourceBridgeFacts.primitiveStackSoundAt_mcopy

abbrev primitiveStackSoundAtCalldatacopy :=
  @Yul.Reference.SourceBridgeFacts.primitiveStackSoundAt_calldatacopy

abbrev primitiveStackSoundAtReturndatacopy :=
  @Yul.Reference.SourceBridgeFacts.primitiveStackSoundAt_returndatacopy

abbrev exprValuePreludeSoundPrimitiveOfArgPrelude :=
  @Yul.Reference.SourceBridgeFacts.exprValuePreludeSound_prim_of_arg_prelude

abbrev exprValuePreludeSoundPrimitiveOfArgStackPrelude :=
  @Yul.Reference.SourceBridgeFacts.exprValuePreludeSound_prim_of_arg_stack_prelude

abbrev exprValuePreludeSoundCast :=
  @Yul.Reference.SourceBridgeFacts.exprValuePreludeSound_cast

abbrev lowerPrimitiveExprValuePreludeSoundOfLowerBound :=
  @Yul.Reference.SourceBridgeFacts.lower1?_prim_exprValuePreludeSound_of_lowerBound1?

abbrev dispatcherResultSound :=
  @Yul.Program.DispatcherResultSound

abbrev dispatcherRunResultSound :=
  @Yul.Program.DispatcherRunResultSound

abbrev dispatcherObservationSound :=
  @Yul.Program.DispatcherObservationSound

abbrev dispatcherRunResultSoundOfObservation :=
  @Yul.Program.dispatcherRunResultSound_of_observation

abbrev dispatcherResultSoundRegular :=
  @Yul.Program.dispatcherResultSound_regular

abbrev dispatcherResultSoundYulHalt :=
  @Yul.Program.dispatcherResultSound_yulHalt

abbrev dispatcherResultSoundRevert :=
  @Yul.Program.dispatcherResultSound_revert

abbrev sourceRegularBlockRunBridgeOfSeq :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularBlockRunBridge_of_seq

abbrev sourceRegularBlockRunAtOfSeq :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularBlockRunAt_of_seq

abbrev sourceRegularSeqRunAtConsBlock :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularSeqRunAt_cons_block

abbrev sourceResultSeqRunAtConsBlockRegularBody :=
  @Yul.Reference.SourceBridgeFacts.sourceResultSeqRunAt_cons_block_regular_body

abbrev sourceResultSeqRunAtConsBlockNonregularBody :=
  @Yul.Reference.SourceBridgeFacts.sourceResultSeqRunAt_cons_block_nonregular_body

abbrev sourceRegularSeqRunAtConsIfTrue :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularSeqRunAt_cons_if_true

abbrev sourceRegularSeqRunAtConsIfFalse :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularSeqRunAt_cons_if_false

abbrev sourceResultSeqRunAtConsIfFalse :=
  @Yul.Reference.SourceBridgeFacts.sourceResultSeqRunAt_cons_if_false

abbrev sourceResultSeqRunAtConsIfTrueRegularBody :=
  @Yul.Reference.SourceBridgeFacts.sourceResultSeqRunAt_cons_if_true_regular_body

abbrev sourceResultSeqRunAtConsIfTrueNonregularBody :=
  @Yul.Reference.SourceBridgeFacts.sourceResultSeqRunAt_cons_if_true_nonregular_body

abbrev sourceRegularSeqRunAtConsSwitchSome :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularSeqRunAt_cons_switch_some

abbrev sourceResultSeqRunAtConsSwitchSomeRegularBody :=
  @Yul.Reference.SourceBridgeFacts.sourceResultSeqRunAt_cons_switch_some_regular_body

abbrev sourceResultSeqRunAtConsSwitchSomeNonregularBody :=
  @Yul.Reference.SourceBridgeFacts.sourceResultSeqRunAt_cons_switch_some_nonregular_body

abbrev sourceRegularSeqRunAtConsSwitchNone :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularSeqRunAt_cons_switch_none

abbrev sourceResultSeqRunAtConsSwitchNone :=
  @Yul.Reference.SourceBridgeFacts.sourceResultSeqRunAt_cons_switch_none

abbrev sourceResultSeqRunAtConsForFalseEmptyInit :=
  @Yul.Reference.SourceBridgeFacts.sourceResultSeqRunAt_cons_for_false_empty_init

abbrev sourceResultSeqRunAtConsForGuardFalseEmptyInit :=
  @Yul.Reference.SourceBridgeFacts.sourceResultSeqRunAt_cons_for_guard_false_empty_init

abbrev sourceBlockRunOpenOfRunScopedNonregular :=
  @Yul.Reference.SourceBridgeFacts.sourceBlock_runOpen_of_runScoped_nonregular

abbrev sourceResultSeqRunAtConsForGuardBodyBreakEmptyInit :=
  @Yul.Reference.SourceBridgeFacts.sourceResultSeqRunAt_cons_for_guard_body_break_empty_init

abbrev sourceResultSeqRunAtConsForGuardBodyLeaveEmptyInit :=
  @Yul.Reference.SourceBridgeFacts.sourceResultSeqRunAt_cons_for_guard_body_leave_empty_init

abbrev sourceResultSeqRunAtConsForGuardBodyHaltEmptyInit :=
  @Yul.Reference.SourceBridgeFacts.sourceResultSeqRunAt_cons_for_guard_body_halt_empty_init

abbrev sourceResultSeqRunAtConsForGuardBodyRegularPostHaltEmptyInit :=
  @Yul.Reference.SourceBridgeFacts.sourceResultSeqRunAt_cons_for_guard_body_regular_post_halt_empty_init

abbrev sourceResultSeqRunAtConsForGuardBodyContinuePostHaltEmptyInit :=
  @Yul.Reference.SourceBridgeFacts.sourceResultSeqRunAt_cons_for_guard_body_continue_post_halt_empty_init

abbrev sourceRegularStmtRunAtForGuardBodyRegularPostRegularEmptyInit :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularStmtRunAt_for_guard_body_regular_post_regular_empty_init

abbrev sourceResultSeqRunAtConsForGuardBodyRegularPostRegularEmptyInit :=
  @Yul.Reference.SourceBridgeFacts.sourceResultSeqRunAt_cons_for_guard_body_regular_post_regular_empty_init

abbrev sourceRegularStmtRunAtForGuardBodyContinuePostRegularEmptyInit :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularStmtRunAt_for_guard_body_continue_post_regular_empty_init

abbrev sourceResultSeqRunAtConsForGuardBodyContinuePostRegularEmptyInit :=
  @Yul.Reference.SourceBridgeFacts.sourceResultSeqRunAt_cons_for_guard_body_continue_post_regular_empty_init

abbrev sourceResultSeqRunAtConsForBodyBreakEmptyInit :=
  @Yul.Reference.SourceBridgeFacts.sourceResultSeqRunAt_cons_for_body_break_empty_init

abbrev sourceResultSeqRunAtConsForBodyLeaveEmptyInit :=
  @Yul.Reference.SourceBridgeFacts.sourceResultSeqRunAt_cons_for_body_leave_empty_init

abbrev sourceResultSeqRunAtConsForBodyHaltEmptyInit :=
  @Yul.Reference.SourceBridgeFacts.sourceResultSeqRunAt_cons_for_body_halt_empty_init

abbrev sourceResultSeqRunAtConsForBodyContinuePostHaltEmptyInit :=
  @Yul.Reference.SourceBridgeFacts.sourceResultSeqRunAt_cons_for_body_continue_post_halt_empty_init

abbrev sourceResultSeqRunAtConsForBodyRegularPostHaltEmptyInit :=
  @Yul.Reference.SourceBridgeFacts.sourceResultSeqRunAt_cons_for_body_regular_post_halt_empty_init

abbrev sourceRegularStmtRunAtForBodyRegularPostRegularEmptyInit :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularStmtRunAt_for_body_regular_post_regular_empty_init

abbrev sourceResultSeqRunAtConsForBodyRegularPostRegularEmptyInit :=
  @Yul.Reference.SourceBridgeFacts.sourceResultSeqRunAt_cons_for_body_regular_post_regular_empty_init

abbrev sourceRegularStmtRunAtForBodyContinuePostRegularEmptyInit :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularStmtRunAt_for_body_continue_post_regular_empty_init

abbrev sourceResultSeqRunAtConsForBodyContinuePostRegularEmptyInit :=
  @Yul.Reference.SourceBridgeFacts.sourceResultSeqRunAt_cons_for_body_continue_post_regular_empty_init

abbrev sourceBlockRunBridgeOfRegular :=
  @Yul.Reference.SourceBridgeFacts.sourceBlockRunBridge_of_regular

abbrev sourceResultBlockRunBridgeOfRegular :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockRunBridge_of_regular

abbrev sourceBlockRunBridgeOfRuns :=
  @Yul.Reference.SourceBridgeFacts.sourceBlockRunBridge_of_runs

abbrev sourceResultBlockRunBridgeOfRuns :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockRunBridge_of_runs

abbrev sourceResultBlockRunBridgeOfSound :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockRunBridge_of_sound

abbrev sourceBlockRunBridgeOfSourceResult :=
  @Yul.Reference.SourceBridgeFacts.sourceBlockRunBridge_of_source_result

abbrev sourceBlockRunBridgeStopOfExec :=
  @Yul.Reference.SourceBridgeFacts.sourceBlockRunBridge_stop_of_exec

abbrev sourceResultBlockRunBridgeStopOfExec :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockRunBridge_stop_of_exec

abbrev sourceBlockRunBridgeTerminalArgsOfExec :=
  @Yul.Reference.SourceBridgeFacts.sourceBlockRunBridge_terminalArgs_of_exec

abbrev sourceResultBlockRunBridgeTerminalArgsOfExec :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockRunBridge_terminalArgs_of_exec

abbrev sourceResultBlockRunBridgeTerminalStackPreludeOfExec :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockRunBridge_terminalStackPrelude_of_exec

abbrev sourceResultBlockRunBridgeTerminalStackPreludeOfArgSound :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockRunBridge_terminalStackPrelude_of_arg_sound

abbrev sourceResultBlockSoundTerminalStackPreludeOfArgSound :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSound_terminalStackPrelude_of_arg_sound

abbrev importedExecBlockStop :=
  @Yul.Reference.Imported.exec_block_stop_succ_succ_succ_succ

abbrev importedExecBlockReturnLitLit :=
  @Yul.Reference.Imported.exec_block_return_lit_lit_succ8

abbrev importedExecBlockRevertLitLit :=
  @Yul.Reference.Imported.exec_block_revert_lit_lit_succ8

abbrev importedExecBlockSelfdestructZero :=
  @Yul.Reference.Imported.exec_block_selfdestruct_zero_succ6

abbrev importedExecBlockSelfdestructLit :=
  @Yul.Reference.Imported.exec_block_selfdestruct_lit_succ6

abbrev sourceBlockRunBridgeStopCall :=
  @Yul.Reference.SourceBridgeFacts.sourceBlockRunBridge_stop_call

abbrev sourceResultBlockRunBridgeStopCall :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockRunBridge_stop_call

abbrev sourceResultBlockSoundStopCall :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSound_stop_call

abbrev checkedStmtBlockLoweringSoundStopCall :=
  @Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSound_stop_call

abbrev sourceResultBlockSoundSelfdestructZeroPreludeCall :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSound_selfdestruct_zero_prelude_call

abbrev sourceResultBlockSoundSelfdestructLitPreludeCall :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSound_selfdestruct_lit_prelude_call

abbrev sourceResultBlockSoundSelfdestructLitPreludeCallCompositional :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSound_selfdestruct_lit_prelude_call_compositional

abbrev sourceResultBlockSoundReturnLitLitPreludeCall :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSound_return_lit_lit_prelude_call

abbrev sourceResultBlockSoundReturnLitLitPreludeCallCompositional :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSound_return_lit_lit_prelude_call_compositional

abbrev sourceResultBlockSoundRevertLitLitPreludeCall :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSound_revert_lit_lit_prelude_call

abbrev sourceResultBlockSoundRevertLitLitPreludeCallCompositional :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSound_revert_lit_lit_prelude_call_compositional

abbrev sourceResultBlockSoundReturnZeroZeroPreludeCall :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSound_return_zero_zero_prelude_call

abbrev sourceResultBlockSoundRevertZeroZeroPreludeCall :=
  @Yul.Reference.SourceBridgeFacts.sourceResultBlockSound_revert_zero_zero_prelude_call

abbrev sourceRegularRootBlockBridgeToSourceLowered :=
  @Yul.Program.sourceLowered_runState_of_regular_root_block_source_bridge

abbrev sourceRegularRootScopedBridgeToSourceLowered :=
  @Yul.Program.sourceLowered_runState_of_regular_root_scoped_source_bridge

abbrev rootSourceBlockBridgeToSourceLowered :=
  @Yul.Program.sourceLowered_runState_of_root_source_block_bridge

abbrev rootSourceResultBlockBridgeToSourceLowered :=
  @Yul.Program.sourceLowered_runState_of_root_source_result_block_bridge

abbrev sourceBridgeToAssemblyCompileAccepted :=
  @Yul.Program.compile_preserves_of_source_bridge_compileAccepted

abbrev sourceBridgeNonemptyToAssemblyCompileAccepted :=
  @Yul.Program.compile_preserves_of_source_bridge_nonempty_compileAccepted

abbrev referenceSourceRunsToAssemblyRawFrameBound :=
  @Yul.Program.compile_preserves_of_reference_source_runs

abbrev referenceSourceRunsToAssemblyCompileAccepted :=
  @Yul.Program.compile_preserves_of_reference_source_runs_compileAccepted

abbrev sourceBridgeToBytecodeCompileAccepted :=
  @Yul.Program.compile_whole_program_result_sound_of_source_bridge_compileAccepted

abbrev assemblyPreservationToBytecode :=
  @Yul.Program.compile_whole_program_result_sound_of_assembly_preservation

abbrev sourceBridgeNonemptyToBytecodeCompileAccepted :=
  @Yul.Program.compile_whole_program_result_sound_of_source_bridge_nonempty_compileAccepted

abbrev referenceSourceRunsToBytecodeRawFrameBound :=
  @Yul.Program.compile_whole_program_result_sound_of_reference_source_runs

abbrev referenceSourceRunsToBytecodeCompileAccepted :=
  @Yul.Program.compile_whole_program_result_sound_of_reference_source_runs_compileAccepted

abbrev referencePreservationToBytecode :=
  @Yul.Program.compile_preserves_result_to_bytecode

abbrev referencePreservationWithSourceExistentialToBytecode :=
  @Yul.Program.compile_preserves_source_exists_to_bytecode

abbrev regularDispatcherScopedSourceBridgeConstructor :=
  @Yul.Program.sourceBridge_of_regular_dispatcher_scoped_source_bridge

abbrev dispatcherSourceBlockBridgeConstructor :=
  @Yul.Program.sourceBridge_of_dispatcher_source_block_bridge

abbrev dispatcherSourceResultBlockBridgeConstructor :=
  @Yul.Program.sourceBridge_of_dispatcher_source_result_block_bridge

abbrev dispatcherSourceResultBlockSoundConstructor :=
  @Yul.Program.sourceBridge_of_dispatcher_source_result_block_sound

abbrev dispatcherSourceSound :=
  @Yul.Program.DispatcherSourceSound

abbrev dispatcherObservationSoundOfHandlers :=
  @Yul.Program.dispatcherObservationSound_of_handlers

abbrev checkedRecursiveDispatcherRunBridge :=
  @Yul.Program.CheckedRecursiveDispatcherRunBridge

abbrev dispatcherBodyNoCheckpoint :=
  @Yul.Program.DispatcherBodyNoCheckpoint

abbrev dispatcherBodyNoCheckpointOfCheckpointAllowed :=
  @Yul.Program.DispatcherBodyNoCheckpoint.of_checkpointAllowed

abbrev dispatcherBodyNoCheckpointOfScopedSafe :=
  @Yul.Program.DispatcherBodyNoCheckpoint.of_scoped_safe

abbrev dispatcherBodyNoCheckpointOfScopedSafeCallSound :=
  @Yul.Program.DispatcherBodyNoCheckpoint.of_scoped_safe_callSound

abbrev dispatcherBodyNoCheckpointOfScopedSafePrimitiveCallCheckpoint :=
  @Yul.Program.DispatcherBodyNoCheckpoint.of_scoped_safe_primitiveCallCheckpoint

abbrev dispatcherBodyNoCheckpointOfScopedSafePrimitiveCallCheckpointSplit :=
  @Yul.Program.DispatcherBodyNoCheckpoint.of_scoped_safe_primitiveCallCheckpoint_split

abbrev dispatcherBodyNoCheckpointOfScopedSafePrimitiveFamilies :=
  @Yul.Program.DispatcherBodyNoCheckpoint.of_scoped_safe_primitiveFamilies

abbrev checkedRecursiveDispatcherRunBridgeOfRunBridgeObservation :=
  @Yul.Program.checkedRecursiveDispatcherRunBridge_of_run_bridge_observation

abbrev checkedRecursiveDispatcherSuccessfulSound :=
  @Yul.Program.CheckedRecursiveDispatcherSuccessfulSound

abbrev checkedRecursiveDispatcherSuccessfulSoundExact :=
  @Yul.Program.CheckedRecursiveDispatcherSuccessfulSoundExact

abbrev checkedRecursiveDispatcherRunBridgeOfSuccessfulSound :=
  @Yul.Program.checkedRecursiveDispatcherRunBridge_of_successful_sound

abbrev checkedRecursiveDispatcherRunBridgeOfSuccessfulSoundExact :=
  @Yul.Program.checkedRecursiveDispatcherRunBridge_of_successful_sound_exact

abbrev checkedRecursiveDispatcherRunBridgeOfRecursiveSourceBridgeWhenUpToAtExactCompatActual :=
  @Yul.Program.checkedRecursiveDispatcherRunBridge_of_recursiveSourceBridgeWhenUpToAtExactCompat_actual

abbrev checkedRecursiveDispatcherRunBridgeOfRecursiveSourceBridgeWhenUpToAtExactCompatNamesActual :=
  @Yul.Program.checkedRecursiveDispatcherRunBridge_of_recursiveSourceBridgeWhenUpToAtExactCompatNames_actual

abbrev checkedRecursiveDispatcherRunBridgeOfRecursiveSourceBridgeWhenUpToAtExactCompatNamesActualSelf :=
  @Yul.Program.checkedRecursiveDispatcherRunBridge_of_recursiveSourceBridgeWhenUpToAtExactCompatNames_actual_self

abbrev checkedRecursiveDispatcherRunBridgeOfProgramRecursiveSourceBridgeWhenUpToAtExactCompatNamesActual :=
  @Yul.Program.checkedRecursiveDispatcherRunBridge_of_programRecursiveSourceBridgeWhenUpToAtExactCompatNames_actual

abbrev checkedRecursiveDispatcherRunBridgeOfProgramRecursiveSourceBridgeWhenUpToAtExactCompatNamesActualSelf :=
  @Yul.Program.checkedRecursiveDispatcherRunBridge_of_programRecursiveSourceBridgeWhenUpToAtExactCompatNames_actual_self

abbrev checkedRecursiveDispatcherRunBridgeOfProgramRecursiveSourceBridgeWhenUpToAtExactCompatNamesScopedPrimitiveFamiliesActual :=
  @Yul.Program.checkedRecursiveDispatcherRunBridge_of_programRecursiveSourceBridgeWhenUpToAtExactCompatNames_scoped_primitiveFamilies_actual

abbrev checkedRecursiveDispatcherRunBridgeOfProgramRecursiveSourceBridgeWhenUpToAtExactCompatNamesScopedPrimitiveFamiliesActualSelf :=
  @Yul.Program.checkedRecursiveDispatcherRunBridge_of_programRecursiveSourceBridgeWhenUpToAtExactCompatNames_scoped_primitiveFamilies_actual_self

abbrev checkedRecursiveDispatcherRunBridgeOfProgramAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNamesActual :=
  @Yul.Program.checkedRecursiveDispatcherRunBridge_of_programAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNames_actual

abbrev checkedRecursiveDispatcherRunBridgeOfProgramAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNamesActualSelf :=
  @Yul.Program.checkedRecursiveDispatcherRunBridge_of_programAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNames_actual_self

abbrev checkedRecursiveDispatcherSuccessfulSoundOfCheckedDispatcherLoweringSoundWhen :=
  @Yul.Program.checkedRecursiveDispatcherSuccessfulSound_of_checked_dispatcher_lowering_sound_when

abbrev checkedRecursiveDispatcherSuccessfulSoundExactOfCheckedDispatcherLoweringSoundWhenExact :=
  @Yul.Program.checkedRecursiveDispatcherSuccessfulSoundExact_of_checked_dispatcher_lowering_sound_when_exact

abbrev checkedRecursiveDispatcherSuccessfulSoundExactOfRecursiveSourceBridgeWhenUpToAtExact :=
  @Yul.Program.checkedRecursiveDispatcherSuccessfulSoundExact_of_recursiveSourceBridgeWhenUpToAtExact

abbrev checkedRecursiveDispatcherSuccessfulSoundExactOfRecursiveSourceBridgeWhenUpToAtExactCompat :=
  @Yul.Program.checkedRecursiveDispatcherSuccessfulSoundExact_of_recursiveSourceBridgeWhenUpToAtExactCompat

abbrev checkedRecursiveDispatcherSuccessfulSoundOfStmtBlockLoweringSoundWhenFresh :=
  @Yul.Program.checkedRecursiveDispatcherSuccessfulSound_of_stmtBlockLoweringSoundWhenFresh

abbrev checkedRecursiveDispatcherSuccessfulSoundOfInitialStmtBlockLoweringSoundWhenFresh :=
  @Yul.Program.checkedRecursiveDispatcherSuccessfulSound_of_initial_stmtBlockLoweringSoundWhenFresh

abbrev checkedRecursiveDispatcherSound :=
  @Yul.Program.CheckedRecursiveDispatcherSound

abbrev checkedRecursiveDispatcherSoundOfCheckedObservation :=
  @Yul.Program.checkedRecursiveDispatcherSound_of_checked_observation

abbrev checkedRecursiveDispatcherSoundOfStmtBlockLoweringSoundFresh :=
  @Yul.Program.checkedRecursiveDispatcherSound_of_stmtBlockLoweringSoundFresh

abbrev checkedRecursiveDispatcherSoundOfInitialStmtBlockLoweringSoundFresh :=
  @Yul.Program.checkedRecursiveDispatcherSound_of_initial_stmtBlockLoweringSoundFresh

abbrev recursiveDispatcherBridgeUpTo :=
  @Yul.Program.RecursiveDispatcherBridgeUpTo

abbrev recursiveDispatcherSuccessfulBridgeUpTo :=
  @Yul.Program.RecursiveDispatcherSuccessfulBridgeUpTo

abbrev recursiveDispatcherBridgeUpToOfDispatcher :=
  @Yul.Program.recursiveDispatcherBridgeUpTo_of_dispatcher

abbrev recursiveDispatcherBridgeUpToOfRecursiveSourceBridgeUpTo :=
  @Yul.Program.recursiveDispatcherBridgeUpTo_of_recursiveSourceBridgeUpTo

abbrev recursiveDispatcherSuccessfulBridgeUpToOfDispatcher :=
  @Yul.Program.recursiveDispatcherSuccessfulBridgeUpTo_of_dispatcher

abbrev recursiveDispatcherSuccessfulBridgeUpToOfRecursiveSourceBridgeWhenUpTo :=
  @Yul.Program.recursiveDispatcherSuccessfulBridgeUpTo_of_recursiveSourceBridgeWhenUpTo

abbrev recursiveDispatcherSuccessfulBridgeUpToOfRecursiveSourceBridgeWhenUpToAt :=
  @Yul.Program.recursiveDispatcherSuccessfulBridgeUpTo_of_recursiveSourceBridgeWhenUpToAt

abbrev recursiveDispatcherSuccessfulBridgeUpToOfRecursiveDispatcherBridgeUpTo :=
  @Yul.Program.recursiveDispatcherSuccessfulBridgeUpTo_of_recursiveDispatcherBridgeUpTo

abbrev checkedRecursiveDispatcherSuccessfulSoundOfRecursiveDispatcherSuccessfulBridgeUpTo :=
  @Yul.Program.checkedRecursiveDispatcherSuccessfulSound_of_recursiveDispatcherSuccessfulBridgeUpTo

abbrev checkedRecursiveDispatcherSoundOfRecursiveDispatcherBridgeUpTo :=
  @Yul.Program.checkedRecursiveDispatcherSound_of_recursiveDispatcherBridgeUpTo

abbrev checkedRecursiveDispatcherSoundOfRecursiveDispatcherBridge :=
  @Yul.Program.checkedRecursiveDispatcherSound_of_recursiveDispatcherBridge

abbrev checkedRecursiveDispatcherSoundOfRecursiveSourceBridgeUpTo :=
  @Yul.Program.checkedRecursiveDispatcherSound_of_recursiveSourceBridgeUpTo

abbrev checkedRecursiveDispatcherSuccessfulSoundOfCheckedRecursiveDispatcherSound :=
  @Yul.Program.checkedRecursiveDispatcherSuccessfulSound_of_checked_recursive_dispatcher_sound

abbrev checkedRecursiveDispatcherRunBridgeOfCheckedRecursiveDispatcherSound :=
  @Yul.Program.checkedRecursiveDispatcherRunBridge_of_checked_recursive_dispatcher_sound

abbrev dispatcherSourceSoundOfCheckedDispatcherLowering :=
  @Yul.Program.dispatcherSourceSound_of_checked_dispatcher_lowering

abbrev dispatcherSourceSoundConstructor :=
  @Yul.Program.sourceBridge_of_dispatcher_source_sound

abbrev checkedDispatcherLoweringSoundConstructor :=
  @Yul.Program.sourceBridge_of_checked_dispatcher_lowering_sound

abbrev checkedDispatcherRunSoundConstructor :=
  @Yul.Program.sourceBridge_of_checked_dispatcher_run_sound

abbrev checkedDispatcherRunObservationConstructor :=
  @Yul.Program.sourceBridge_of_checked_dispatcher_run_observation

abbrev checkedRecursiveDispatcherSoundConstructor :=
  @Yul.Program.sourceBridge_of_checked_recursive_dispatcher_sound

abbrev initialStmtBlockLoweringFreshObservationConstructor :=
  @Yul.Program.sourceBridge_of_initial_stmt_block_lowering_fresh_observation

abbrev recursiveDispatcherBridgeUpToConstructor :=
  @Yul.Program.sourceBridge_of_recursiveDispatcherBridgeUpTo

abbrev recursiveDispatcherBridgeConstructor :=
  @Yul.Program.sourceBridge_of_recursiveDispatcherBridge

abbrev rootBodyOfDispatcherStop :=
  @Yul.Program.root_body_of_dispatcher_stop

abbrev rootBodyTerminalComponentsOfDispatcher :=
  @Yul.Program.root_body_terminal_components_of_dispatcher

abbrev rootBodyReturnLitLitPreludeOfDispatcher :=
  @Yul.Program.root_body_return_lit_lit_prelude_of_dispatcher

abbrev rootBodyRevertLitLitPreludeOfDispatcher :=
  @Yul.Program.root_body_revert_lit_lit_prelude_of_dispatcher

abbrev rootBodySelfdestructLitPreludeOfDispatcher :=
  @Yul.Program.root_body_selfdestruct_lit_prelude_of_dispatcher

abbrev dispatcherStopSourceBridgeConstructor :=
  @Yul.Program.sourceBridge_of_dispatcher_stop_call

abbrev dispatcherStopCallToAssemblyCompileAccepted :=
  @Yul.Program.compile_preserves_of_dispatcher_stop_call_compileAccepted

abbrev dispatcherStopCallToBytecodeCompileAccepted :=
  @Yul.Program.compile_whole_program_result_sound_of_dispatcher_stop_call_compileAccepted

abbrev dispatcherReturnZeroZeroSourceBridgeConstructor :=
  @Yul.Program.sourceBridge_of_dispatcher_return_zero_zero_call

abbrev dispatcherReturnZeroZeroCallToAssemblyCompileAccepted :=
  @Yul.Program.compile_preserves_of_dispatcher_return_zero_zero_call_compileAccepted

abbrev dispatcherReturnZeroZeroCallToBytecodeCompileAccepted :=
  @Yul.Program.compile_whole_program_result_sound_of_dispatcher_return_zero_zero_call_compileAccepted

abbrev dispatcherRevertZeroZeroSourceBridgeConstructor :=
  @Yul.Program.sourceBridge_of_dispatcher_revert_zero_zero_call

abbrev dispatcherRevertZeroZeroCallToAssemblyCompileAccepted :=
  @Yul.Program.compile_preserves_of_dispatcher_revert_zero_zero_call_compileAccepted

abbrev dispatcherRevertZeroZeroCallToBytecodeCompileAccepted :=
  @Yul.Program.compile_whole_program_result_sound_of_dispatcher_revert_zero_zero_call_compileAccepted

abbrev dispatcherReturnLitLitSourceBridgeConstructor :=
  @Yul.Program.sourceBridge_of_dispatcher_return_lit_lit_call

abbrev dispatcherReturnLitLitCallToAssemblyCompileAccepted :=
  @Yul.Program.compile_preserves_of_dispatcher_return_lit_lit_call_compileAccepted

abbrev dispatcherReturnLitLitCallToBytecodeCompileAccepted :=
  @Yul.Program.compile_whole_program_result_sound_of_dispatcher_return_lit_lit_call_compileAccepted

abbrev dispatcherRevertLitLitSourceBridgeConstructor :=
  @Yul.Program.sourceBridge_of_dispatcher_revert_lit_lit_call

abbrev dispatcherRevertLitLitCallToAssemblyCompileAccepted :=
  @Yul.Program.compile_preserves_of_dispatcher_revert_lit_lit_call_compileAccepted

abbrev dispatcherRevertLitLitCallToBytecodeCompileAccepted :=
  @Yul.Program.compile_whole_program_result_sound_of_dispatcher_revert_lit_lit_call_compileAccepted

abbrev dispatcherSelfdestructZeroSourceBridgeConstructor :=
  @Yul.Program.sourceBridge_of_dispatcher_selfdestruct_zero_call

abbrev dispatcherSelfdestructZeroCallToAssemblyCompileAccepted :=
  @Yul.Program.compile_preserves_of_dispatcher_selfdestruct_zero_call_compileAccepted

abbrev dispatcherSelfdestructZeroCallToBytecodeCompileAccepted :=
  @Yul.Program.compile_whole_program_result_sound_of_dispatcher_selfdestruct_zero_call_compileAccepted

abbrev dispatcherReturnLitLitPreludeSourceBridgeConstructor :=
  @Yul.Program.sourceBridge_of_dispatcher_return_lit_lit_prelude_call

abbrev dispatcherReturnLitLitPreludeSourceBridgeConstructorCompositional :=
  @Yul.Program.sourceBridge_of_dispatcher_return_lit_lit_prelude_call_compositional

abbrev dispatcherReturnLitLitPreludeToAssemblyCompileAccepted :=
  @Yul.Program.compile_preserves_of_dispatcher_return_lit_lit_prelude_call_checked_compileAccepted

abbrev dispatcherReturnLitLitPreludeToAssemblyCompileAcceptedRawGeneratedEvidence :=
  @Yul.Program.compile_preserves_of_dispatcher_return_lit_lit_prelude_call_compileAccepted

abbrev dispatcherReturnLitLitPreludeToAssemblyCompileAcceptedCompositional :=
  @Yul.Program.compile_preserves_of_dispatcher_return_lit_lit_prelude_call_checked_compileAccepted

abbrev dispatcherReturnLitLitPreludeToAssemblyCompileAcceptedCompositionalRawGeneratedEvidence :=
  @Yul.Program.compile_preserves_of_dispatcher_return_lit_lit_prelude_call_compositional_compileAccepted

abbrev dispatcherReturnLitLitPreludeToAssemblyCompileAcceptedCompositionalAuto :=
  @Yul.Program.compile_preserves_of_dispatcher_return_lit_lit_prelude_call_compositional_compileAccepted_auto

abbrev dispatcherReturnLitLitPreludeToAssemblyCompileAcceptedChecked :=
  @Yul.Program.compile_preserves_of_dispatcher_return_lit_lit_prelude_call_checked_compileAccepted

abbrev dispatcherReturnLitLitPreludeToBytecodeCompileAccepted :=
  @Yul.Program.compile_whole_program_result_sound_of_dispatcher_return_lit_lit_prelude_call_checked_compileAccepted

abbrev dispatcherReturnLitLitPreludeToBytecodeCompileAcceptedRawGeneratedEvidence :=
  @Yul.Program.compile_whole_program_result_sound_of_dispatcher_return_lit_lit_prelude_call_compileAccepted

abbrev dispatcherReturnLitLitPreludeToBytecodeCompileAcceptedCompositional :=
  @Yul.Program.compile_whole_program_result_sound_of_dispatcher_return_lit_lit_prelude_call_checked_compileAccepted

abbrev dispatcherReturnLitLitPreludeToBytecodeCompileAcceptedCompositionalRawGeneratedEvidence :=
  @Yul.Program.compile_whole_program_result_sound_of_dispatcher_return_lit_lit_prelude_call_compositional_compileAccepted

abbrev dispatcherReturnLitLitPreludeToBytecodeCompileAcceptedCompositionalAuto :=
  @Yul.Program.compile_whole_program_result_sound_of_dispatcher_return_lit_lit_prelude_call_compositional_compileAccepted_auto

abbrev dispatcherReturnLitLitPreludeToBytecodeCompileAcceptedChecked :=
  @Yul.Program.compile_whole_program_result_sound_of_dispatcher_return_lit_lit_prelude_call_checked_compileAccepted

abbrev dispatcherRevertLitLitPreludeSourceBridgeConstructor :=
  @Yul.Program.sourceBridge_of_dispatcher_revert_lit_lit_prelude_call

abbrev dispatcherRevertLitLitPreludeSourceBridgeConstructorCompositional :=
  @Yul.Program.sourceBridge_of_dispatcher_revert_lit_lit_prelude_call_compositional

abbrev dispatcherRevertLitLitPreludeToAssemblyCompileAccepted :=
  @Yul.Program.compile_preserves_of_dispatcher_revert_lit_lit_prelude_call_checked_compileAccepted

abbrev dispatcherRevertLitLitPreludeToAssemblyCompileAcceptedRawGeneratedEvidence :=
  @Yul.Program.compile_preserves_of_dispatcher_revert_lit_lit_prelude_call_compileAccepted

abbrev dispatcherRevertLitLitPreludeToAssemblyCompileAcceptedCompositional :=
  @Yul.Program.compile_preserves_of_dispatcher_revert_lit_lit_prelude_call_checked_compileAccepted

abbrev dispatcherRevertLitLitPreludeToAssemblyCompileAcceptedCompositionalRawGeneratedEvidence :=
  @Yul.Program.compile_preserves_of_dispatcher_revert_lit_lit_prelude_call_compositional_compileAccepted

abbrev dispatcherRevertLitLitPreludeToAssemblyCompileAcceptedCompositionalAuto :=
  @Yul.Program.compile_preserves_of_dispatcher_revert_lit_lit_prelude_call_compositional_compileAccepted_auto

abbrev dispatcherRevertLitLitPreludeToAssemblyCompileAcceptedChecked :=
  @Yul.Program.compile_preserves_of_dispatcher_revert_lit_lit_prelude_call_checked_compileAccepted

abbrev dispatcherRevertLitLitPreludeToBytecodeCompileAccepted :=
  @Yul.Program.compile_whole_program_result_sound_of_dispatcher_revert_lit_lit_prelude_call_checked_compileAccepted

abbrev dispatcherRevertLitLitPreludeToBytecodeCompileAcceptedRawGeneratedEvidence :=
  @Yul.Program.compile_whole_program_result_sound_of_dispatcher_revert_lit_lit_prelude_call_compileAccepted

abbrev dispatcherRevertLitLitPreludeToBytecodeCompileAcceptedCompositional :=
  @Yul.Program.compile_whole_program_result_sound_of_dispatcher_revert_lit_lit_prelude_call_checked_compileAccepted

abbrev dispatcherRevertLitLitPreludeToBytecodeCompileAcceptedCompositionalRawGeneratedEvidence :=
  @Yul.Program.compile_whole_program_result_sound_of_dispatcher_revert_lit_lit_prelude_call_compositional_compileAccepted

abbrev dispatcherRevertLitLitPreludeToBytecodeCompileAcceptedCompositionalAuto :=
  @Yul.Program.compile_whole_program_result_sound_of_dispatcher_revert_lit_lit_prelude_call_compositional_compileAccepted_auto

abbrev dispatcherRevertLitLitPreludeToBytecodeCompileAcceptedChecked :=
  @Yul.Program.compile_whole_program_result_sound_of_dispatcher_revert_lit_lit_prelude_call_checked_compileAccepted

abbrev dispatcherSelfdestructLitPreludeSourceBridgeConstructor :=
  @Yul.Program.sourceBridge_of_dispatcher_selfdestruct_lit_prelude_call

abbrev dispatcherSelfdestructLitPreludeSourceBridgeConstructorCompositional :=
  @Yul.Program.sourceBridge_of_dispatcher_selfdestruct_lit_prelude_call_compositional

abbrev dispatcherSelfdestructLitPreludeToAssemblyCompileAccepted :=
  @Yul.Program.compile_preserves_of_dispatcher_selfdestruct_lit_prelude_call_checked_compileAccepted

abbrev dispatcherSelfdestructLitPreludeToAssemblyCompileAcceptedRawGeneratedEvidence :=
  @Yul.Program.compile_preserves_of_dispatcher_selfdestruct_lit_prelude_call_compileAccepted

abbrev dispatcherSelfdestructLitPreludeToAssemblyCompileAcceptedCompositional :=
  @Yul.Program.compile_preserves_of_dispatcher_selfdestruct_lit_prelude_call_checked_compileAccepted

abbrev dispatcherSelfdestructLitPreludeToAssemblyCompileAcceptedCompositionalRawGeneratedEvidence :=
  @Yul.Program.compile_preserves_of_dispatcher_selfdestruct_lit_prelude_call_compositional_compileAccepted

abbrev dispatcherSelfdestructLitPreludeToAssemblyCompileAcceptedCompositionalAuto :=
  @Yul.Program.compile_preserves_of_dispatcher_selfdestruct_lit_prelude_call_compositional_compileAccepted_auto

abbrev dispatcherSelfdestructLitPreludeToAssemblyCompileAcceptedChecked :=
  @Yul.Program.compile_preserves_of_dispatcher_selfdestruct_lit_prelude_call_checked_compileAccepted

abbrev dispatcherSelfdestructLitPreludeToBytecodeCompileAccepted :=
  @Yul.Program.compile_whole_program_result_sound_of_dispatcher_selfdestruct_lit_prelude_call_checked_compileAccepted

abbrev dispatcherSelfdestructLitPreludeToBytecodeCompileAcceptedRawGeneratedEvidence :=
  @Yul.Program.compile_whole_program_result_sound_of_dispatcher_selfdestruct_lit_prelude_call_compileAccepted

abbrev dispatcherSelfdestructLitPreludeToBytecodeCompileAcceptedCompositional :=
  @Yul.Program.compile_whole_program_result_sound_of_dispatcher_selfdestruct_lit_prelude_call_checked_compileAccepted

abbrev dispatcherSelfdestructLitPreludeToBytecodeCompileAcceptedCompositionalRawGeneratedEvidence :=
  @Yul.Program.compile_whole_program_result_sound_of_dispatcher_selfdestruct_lit_prelude_call_compositional_compileAccepted

abbrev dispatcherSelfdestructLitPreludeToBytecodeCompileAcceptedCompositionalAuto :=
  @Yul.Program.compile_whole_program_result_sound_of_dispatcher_selfdestruct_lit_prelude_call_compositional_compileAccepted_auto

abbrev dispatcherSelfdestructLitPreludeToBytecodeCompileAcceptedChecked :=
  @Yul.Program.compile_whole_program_result_sound_of_dispatcher_selfdestruct_lit_prelude_call_checked_compileAccepted

abbrev sourceBridgeToAssembly :=
  @Yul.Program.compile_preserves_of_source_bridge_compileAccepted

abbrev sourceBridgeToAssemblyRawFrameBound :=
  @Yul.Program.compile_preserves_of_source_bridge

abbrev regularDispatcherScopedSourceBridgeToAssembly :=
  @Yul.Program.compile_preserves_of_regular_dispatcher_scoped_source_bridge_compileAccepted

abbrev regularDispatcherScopedSourceBridgeToAssemblyRawFrameBound :=
  @Yul.Program.compile_preserves_of_regular_dispatcher_scoped_source_bridge

abbrev regularDispatcherScopedSourceBridgeToAssemblyCompileAccepted :=
  @Yul.Program.compile_preserves_of_regular_dispatcher_scoped_source_bridge_compileAccepted

abbrev dispatcherSourceBlockBridgeToAssembly :=
  @Yul.Program.compile_preserves_of_dispatcher_source_block_bridge_compileAccepted

abbrev dispatcherSourceBlockBridgeToAssemblyRawFrameBound :=
  @Yul.Program.compile_preserves_of_dispatcher_source_block_bridge

abbrev dispatcherSourceBlockBridgeToAssemblyCompileAccepted :=
  @Yul.Program.compile_preserves_of_dispatcher_source_block_bridge_compileAccepted

abbrev dispatcherSourceResultBlockBridgeToAssembly :=
  @Yul.Program.compile_preserves_of_dispatcher_source_result_block_bridge_compileAccepted

abbrev dispatcherSourceResultBlockBridgeToAssemblyRawFrameBound :=
  @Yul.Program.compile_preserves_of_dispatcher_source_result_block_bridge

abbrev dispatcherSourceResultBlockSoundToAssembly :=
  @Yul.Program.compile_preserves_of_dispatcher_source_result_block_sound_compileAccepted

abbrev dispatcherSourceResultBlockSoundToAssemblyRawFrameBound :=
  @Yul.Program.compile_preserves_of_dispatcher_source_result_block_sound

abbrev dispatcherSourceResultBlockBridgeToAssemblyCompileAccepted :=
  @Yul.Program.compile_preserves_of_dispatcher_source_result_block_bridge_compileAccepted

abbrev dispatcherSourceResultBlockSoundToAssemblyCompileAccepted :=
  @Yul.Program.compile_preserves_of_dispatcher_source_result_block_sound_compileAccepted

abbrev dispatcherSourceSoundToAssemblyCompileAccepted :=
  @Yul.Program.compile_preserves_of_dispatcher_source_sound_compileAccepted

abbrev checkedDispatcherLoweringSoundToAssemblyCompileAccepted :=
  @Yul.Program.compile_preserves_of_checked_dispatcher_lowering_sound_compileAccepted

abbrev checkedDispatcherRunSoundToAssemblyCompileAccepted :=
  @Yul.Program.compile_preserves_of_checked_dispatcher_run_sound_compileAccepted

abbrev checkedDispatcherRunObservationToAssemblyCompileAccepted :=
  @Yul.Program.compile_preserves_of_checked_dispatcher_run_observation_compileAccepted

abbrev checkedRecursiveDispatcherSoundToAssemblyCompileAccepted :=
  @Yul.Program.compile_preserves_of_checked_recursive_dispatcher_sound_compileAccepted

abbrev initialStmtBlockLoweringFreshObservationToAssemblyCompileAccepted :=
  @Yul.Program.compile_preserves_of_initial_stmt_block_lowering_fresh_observation_compileAccepted

abbrev sourceBridgeToBytecode :=
  @Yul.Program.compile_whole_program_result_sound_of_source_bridge_compileAccepted

abbrev sourceBridgeToBytecodeRawFrameBound :=
  @Yul.Program.compile_whole_program_result_sound_of_source_bridge

abbrev regularDispatcherScopedSourceBridgeToBytecode :=
  @Yul.Program.compile_whole_program_result_sound_of_regular_dispatcher_scoped_source_bridge_compileAccepted

abbrev regularDispatcherScopedSourceBridgeToBytecodeRawFrameBound :=
  @Yul.Program.compile_whole_program_result_sound_of_regular_dispatcher_scoped_source_bridge

abbrev regularDispatcherScopedSourceBridgeToBytecodeCompileAccepted :=
  @Yul.Program.compile_whole_program_result_sound_of_regular_dispatcher_scoped_source_bridge_compileAccepted

abbrev dispatcherSourceBlockBridgeToBytecode :=
  @Yul.Program.compile_whole_program_result_sound_of_dispatcher_source_block_bridge_compileAccepted

abbrev dispatcherSourceBlockBridgeToBytecodeRawFrameBound :=
  @Yul.Program.compile_whole_program_result_sound_of_dispatcher_source_block_bridge

abbrev dispatcherSourceBlockBridgeToBytecodeCompileAccepted :=
  @Yul.Program.compile_whole_program_result_sound_of_dispatcher_source_block_bridge_compileAccepted

abbrev dispatcherSourceResultBlockBridgeToBytecode :=
  @Yul.Program.compile_whole_program_result_sound_of_dispatcher_source_result_block_bridge_compileAccepted

abbrev dispatcherSourceResultBlockBridgeToBytecodeRawFrameBound :=
  @Yul.Program.compile_whole_program_result_sound_of_dispatcher_source_result_block_bridge

abbrev dispatcherSourceResultBlockSoundToBytecode :=
  @Yul.Program.compile_whole_program_result_sound_of_dispatcher_source_result_block_sound_compileAccepted

abbrev dispatcherSourceResultBlockSoundToBytecodeRawFrameBound :=
  @Yul.Program.compile_whole_program_result_sound_of_dispatcher_source_result_block_sound

abbrev dispatcherSourceResultBlockBridgeToBytecodeCompileAccepted :=
  @Yul.Program.compile_whole_program_result_sound_of_dispatcher_source_result_block_bridge_compileAccepted

abbrev dispatcherSourceResultBlockSoundToBytecodeCompileAccepted :=
  @Yul.Program.compile_whole_program_result_sound_of_dispatcher_source_result_block_sound_compileAccepted

abbrev dispatcherSourceSoundToBytecodeCompileAccepted :=
  @Yul.Program.compile_whole_program_result_sound_of_dispatcher_source_sound_compileAccepted

abbrev checkedDispatcherLoweringSoundToBytecodeCompileAccepted :=
  @Yul.Program.compile_whole_program_result_sound_of_checked_dispatcher_lowering_sound_compileAccepted

abbrev checkedDispatcherRunSoundToBytecodeCompileAccepted :=
  @Yul.Program.compile_whole_program_result_sound_of_checked_dispatcher_run_sound_compileAccepted

abbrev checkedDispatcherRunObservationToBytecodeCompileAccepted :=
  @Yul.Program.compile_whole_program_result_sound_of_checked_dispatcher_run_observation_compileAccepted

abbrev checkedRecursiveDispatcherSoundToBytecodeCompileAccepted :=
  @Yul.Program.compile_whole_program_result_sound_of_checked_recursive_dispatcher_sound_compileAccepted

abbrev initialStmtBlockLoweringFreshObservationToBytecodeCompileAccepted :=
  @Yul.Program.compile_whole_program_result_sound_of_initial_stmt_block_lowering_fresh_observation_compileAccepted

abbrev recursiveDispatcherBridgeUpToToBytecodeCompileAccepted :=
  @Yul.Program.compile_whole_program_result_sound_of_recursiveDispatcherBridgeUpTo_compileAccepted

abbrev recursiveDispatcherBridgeToBytecodeCompileAccepted :=
  @Yul.Program.compile_whole_program_result_sound_of_recursiveDispatcherBridge_compileAccepted

abbrev recursiveSourceBridgeUpToToBytecodeCompileAccepted :=
  @Yul.Program.compile_whole_program_result_sound_of_recursiveSourceBridgeUpTo_compileAccepted

abbrev checkedRecursiveDispatcherRunBridgeToBytecodeCompileAccepted :=
  @Yul.Program.compile_whole_program_result_sound_of_checked_recursive_dispatcher_run_bridge_compileAccepted

abbrev checkedRecursiveDispatcherSuccessfulSoundToBytecodeCompileAccepted :=
  @Yul.Program.compile_whole_program_result_sound_of_checked_recursive_dispatcher_successful_sound_compileAccepted

abbrev checkedRecursiveDispatcherSuccessfulSoundExactToBytecodeCompileAccepted :=
  @Yul.Program.compile_whole_program_result_sound_of_checked_recursive_dispatcher_successful_sound_exact_compileAccepted

abbrev checkedDispatcherLoweringSoundWhenToBytecodeCompileAccepted :=
  @Yul.Program.compile_whole_program_result_sound_of_checked_dispatcher_lowering_sound_when_compileAccepted

abbrev initialStmtBlockLoweringSoundWhenFreshToBytecodeCompileAccepted :=
  @Yul.Program.compile_whole_program_result_sound_of_initial_stmtBlockLoweringSoundWhenFresh_compileAccepted

abbrev recursiveDispatcherSuccessfulBridgeUpToToBytecodeCompileAccepted :=
  @Yul.Program.compile_whole_program_result_sound_of_recursiveDispatcherSuccessfulBridgeUpTo_compileAccepted

abbrev recursiveSourceBridgeWhenUpToToBytecodeCompileAccepted :=
  @Yul.Program.compile_whole_program_result_sound_of_recursiveSourceBridgeWhenUpTo_compileAccepted

abbrev recursiveSourceBridgeWhenUpToAtToBytecodeCompileAccepted :=
  @Yul.Program.compile_whole_program_result_sound_of_recursiveSourceBridgeWhenUpToAt_compileAccepted

abbrev recursiveSourceBridgeWhenUpToAtExactToBytecodeCompileAccepted :=
  @Yul.Program.compile_whole_program_result_sound_of_recursiveSourceBridgeWhenUpToAtExact_compileAccepted

abbrev recursiveSourceBridgeWhenUpToAtExactCompatActualToBytecodeCompileAccepted :=
  @Yul.Program.compile_whole_program_result_sound_of_recursiveSourceBridgeWhenUpToAtExactCompat_actual_compileAccepted

abbrev recursiveSourceBridgeWhenUpToAtExactCompatNamesActualToBytecodeCompileAccepted :=
  @Yul.Program.compile_whole_program_result_sound_of_recursiveSourceBridgeWhenUpToAtExactCompatNames_actual_compileAccepted

abbrev recursiveSourceBridgeWhenUpToAtExactCompatNamesActualSelfToBytecodeCompileAccepted :=
  @Yul.Program.compile_whole_program_result_sound_of_recursiveSourceBridgeWhenUpToAtExactCompatNames_actual_self_compileAccepted

abbrev programRecursiveSourceBridgeWhenUpToAtExactCompatNamesActualToBytecodeCompileAccepted :=
  @Yul.Program.compile_whole_program_result_sound_of_programRecursiveSourceBridgeWhenUpToAtExactCompatNames_actual_compileAccepted

abbrev programRecursiveSourceBridgeWhenUpToAtExactCompatNamesActualSelfToBytecodeCompileAccepted :=
  @Yul.Program.compile_whole_program_result_sound_of_programRecursiveSourceBridgeWhenUpToAtExactCompatNames_actual_self_compileAccepted

abbrev programRecursiveSourceBridgeWhenUpToAtExactCompatNamesScopedPrimitiveFamiliesToBytecodeCompileAccepted :=
  @Yul.Program.compile_whole_program_result_sound_of_programRecursiveSourceBridgeWhenUpToAtExactCompatNames_scoped_primitiveFamilies_compileAccepted

abbrev programRecursiveSourceBridgeWhenUpToAtExactCompatNamesScopedPrimitiveFamiliesSelfToBytecodeCompileAccepted :=
  @Yul.Program.compile_whole_program_result_sound_of_programRecursiveSourceBridgeWhenUpToAtExactCompatNames_scoped_primitiveFamilies_self_compileAccepted

abbrev programAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNamesToBytecodeCompileAccepted :=
  @Yul.Program.compile_whole_program_result_sound_of_programAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNames_compileAccepted

abbrev programAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNamesSelfToBytecodeCompileAccepted :=
  @Yul.Program.compile_whole_program_result_sound_of_programAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNames_self_compileAccepted

abbrev recursiveSourceBridgeWhenUpToAtExactCompatNamesScopedPrimitiveFamiliesToBytecodeCompileAccepted :=
  @Yul.Program.compile_whole_program_result_sound_of_recursiveSourceBridgeWhenUpToAtExactCompatNames_scoped_primitiveFamilies_compileAccepted

abbrev recursiveSourceBridgeWhenUpToAtExactCompatNamesScopedPrimitiveFamiliesSelfToBytecodeCompileAccepted :=
  @Yul.Program.compile_whole_program_result_sound_of_recursiveSourceBridgeWhenUpToAtExactCompatNames_scoped_primitiveFamilies_self_compileAccepted

abbrev recursiveSourceBridgeWhenUpToAtExactCompatScopedToBytecodeCompileAccepted :=
  @Yul.Program.compile_whole_program_result_sound_of_recursiveSourceBridgeWhenUpToAtExactCompat_scoped_compileAccepted

abbrev recursiveSourceBridgeWhenUpToAtExactCompatScopedCallSoundToBytecodeCompileAccepted :=
  @Yul.Program.compile_whole_program_result_sound_of_recursiveSourceBridgeWhenUpToAtExactCompat_scoped_callSound_compileAccepted

abbrev recursiveSourceBridgeWhenUpToAtExactCompatScopedPrimitiveCallCheckpointToBytecodeCompileAccepted :=
  @Yul.Program.compile_whole_program_result_sound_of_recursiveSourceBridgeWhenUpToAtExactCompat_scoped_primitiveCallCheckpoint_compileAccepted

abbrev recursiveSourceBridgeWhenUpToAtExactCompatScopedPrimitiveCallCheckpointSplitToBytecodeCompileAccepted :=
  @Yul.Program.compile_whole_program_result_sound_of_recursiveSourceBridgeWhenUpToAtExactCompat_scoped_primitiveCallCheckpoint_split_compileAccepted

abbrev recursiveSourceBridgeWhenUpToAtExactCompatScopedPrimitiveFamiliesToBytecodeCompileAccepted :=
  @Yul.Program.compile_whole_program_result_sound_of_recursiveSourceBridgeWhenUpToAtExactCompat_scoped_primitiveFamilies_compileAccepted

abbrev recursiveSourceBridgeWhenUpToAtScopedPrimitiveFamiliesToBytecodeCompileAccepted :=
  @Yul.Program.compile_whole_program_result_sound_of_recursiveSourceBridgeWhenUpToAt_scoped_primitiveFamilies_compileAccepted

abbrev recursiveSourceBridgeWhenUpToAtExactCompatToBytecodeCompileAccepted :=
  @Yul.Program.compile_whole_program_result_sound_of_recursiveSourceBridgeWhenUpToAtExactCompat_compileAccepted

/--
Legacy backend bridge from imported Nethermind Yul runs directly to the lowered
compiler path.  This is intentionally separated from `sourceBridge`.
-/
abbrev loweredBridge :=
  @Yul.Reference.LoweredBridge

abbrev dispatcherBody :=
  @Yul.Reference.Imported.dispatcherBody

abbrev dispatcherCallState :=
  @Yul.Reference.Imported.dispatcherCallState

abbrev dispatcherBodyOk :=
  @Yul.Reference.Imported.dispatcherBody_ok

abbrev dispatcherCallStateOk :=
  @Yul.Reference.Imported.dispatcherCallState_ok

abbrev dispatcherBodyInstallContractOk :=
  @Yul.Reference.Imported.dispatcherBody_installContract_ok

abbrev dispatcherCallStateInstallContractOk :=
  @Yul.Reference.Imported.dispatcherCallState_installContract_ok

abbrev dispatcherRunResultOfBody :=
  @Yul.Reference.Imported.dispatcherRunResultOfBody

abbrev callDispatcherSuccRegularOfExecDispatcher :=
  @Yul.Reference.Imported.callDispatcher_succ_regular_of_exec_dispatcher

abbrev runResultSuccRegularOfExecDispatcher :=
  @Yul.Reference.Imported.runResult_succ_regular_of_exec_dispatcher

abbrev callDispatcherSuccYulHaltOfExecDispatcher :=
  @Yul.Reference.Imported.callDispatcher_succ_yulHalt_of_exec_dispatcher

abbrev runResultSuccYulHaltOfExecDispatcher :=
  @Yul.Reference.Imported.runResult_succ_yulHalt_of_exec_dispatcher

abbrev callDispatcherSuccErrorOfExecDispatcher :=
  @Yul.Reference.Imported.callDispatcher_succ_error_of_exec_dispatcher

abbrev runResultSuccErrorOfExecDispatcher :=
  @Yul.Reference.Imported.runResult_succ_error_of_exec_dispatcher

abbrev callDispatcherSuccRevertOfExecDispatcher :=
  @Yul.Reference.Imported.callDispatcher_succ_revert_of_exec_dispatcher

abbrev runResultSuccRevertOfExecDispatcher :=
  @Yul.Reference.Imported.runResult_succ_revert_of_exec_dispatcher

abbrev runResultSuccOfExecDispatcher :=
  @Yul.Reference.Imported.runResult_succ_of_exec_dispatcher

abbrev exactVarStackRel :=
  @Yul.Reference.ExactVarStackRel

abbrev storeDomainExact :=
  @Yul.Reference.StoreDomainExact

abbrev stateStoreDomainExact :=
  @Yul.Reference.SourceBridgeFacts.StateStoreDomainExact

abbrev stateStoreDomainExactInsertMem :=
  @Yul.Reference.SourceBridgeFacts.StateStoreDomainExact.insert_mem

abbrev stateStoreDomainExactMultifillMem :=
  @Yul.Reference.SourceBridgeFacts.StateStoreDomainExact.multifill_mem

abbrev storeDomainContains :=
  @Yul.Reference.SourceBridgeFacts.StoreDomainContains

abbrev storeDomainContainsOfExact :=
  @Yul.Reference.SourceBridgeFacts.StoreDomainContains.of_exact

abbrev storeDomainContainsInsert :=
  @Yul.Reference.SourceBridgeFacts.StoreDomainContains.insert

abbrev storeDomainContainsInsertPairs :=
  @Yul.Reference.SourceBridgeFacts.StoreDomainContains.insertPairs

abbrev storeDomainContainsZeroFill :=
  @Yul.Reference.SourceBridgeFacts.StoreDomainContains.zeroFill

abbrev storeDomainContainsRestrictVarStore :=
  @Yul.Reference.SourceBridgeFacts.StoreDomainContains.restrictVarStore

abbrev storeDomainExactRestrictVarStoreOfContains :=
  @Yul.Reference.SourceBridgeFacts.StoreDomainExact.restrictVarStore_of_contains

abbrev stateStoreContains :=
  @Yul.Reference.SourceBridgeFacts.StateStoreContains

abbrev stateStoreContainsOfExact :=
  @Yul.Reference.SourceBridgeFacts.StateStoreContains.of_exact

abbrev stateStoreContainsInitcallOfLength :=
  @Yul.Reference.SourceBridgeFacts.StateStoreContains.initcall_of_length

abbrev stateStoreContainsInsert :=
  @Yul.Reference.SourceBridgeFacts.StateStoreContains.insert

abbrev stateStoreContainsZeroFill :=
  @Yul.Reference.SourceBridgeFacts.StateStoreContains.zeroFill

abbrev stateStoreContainsMultifill :=
  @Yul.Reference.SourceBridgeFacts.StateStoreContains.multifill

abbrev stateStoreContainsRestrictStoreTo :=
  @Yul.Reference.SourceBridgeFacts.StateStoreContains.restrictStoreTo

abbrev stateStoreContainsMkOkOk :=
  @Yul.Reference.SourceBridgeFacts.StateStoreContains.mkOk_ok

abbrev stateStoreContainsMkOkOfNoCheckpoint :=
  @Yul.Reference.SourceBridgeFacts.StateStoreContains.mkOk_of_no_checkpoint

abbrev stateStoreContainsReviveJump :=
  @Yul.Reference.SourceBridgeFacts.StateStoreContains.reviveJump

abbrev stateStoreContainsSetBreak :=
  @Yul.Reference.SourceBridgeFacts.StateStoreContains.setBreak

abbrev stateStoreContainsSetContinue :=
  @Yul.Reference.SourceBridgeFacts.StateStoreContains.setContinue

abbrev stateStoreContainsSetLeave :=
  @Yul.Reference.SourceBridgeFacts.StateStoreContains.setLeave

abbrev stateStoreContainsOverwrite :=
  @Yul.Reference.SourceBridgeFacts.StateStoreContains.overwrite?

abbrev stateStoreContainsCallRestore :=
  @Yul.Reference.SourceBridgeFacts.StateStoreContains.callRestore

abbrev stateStoreDomainExactRestrictStoreToOfContains :=
  @Yul.Reference.SourceBridgeFacts.StateStoreDomainExact.restrictStoreTo_of_contains

abbrev sourceResultStoreContainsExecSeqNilSucc :=
  @Yul.Reference.SourceBridgeFacts.SourceResultStoreContains.execSeq_nil_succ

abbrev sourceResultStoreContainsExecSeqConsSucc :=
  @Yul.Reference.SourceBridgeFacts.SourceResultStoreContains.execSeq_cons_succ

abbrev sourceResultStoreContainsExecBlockSuccOfExecSeq :=
  @Yul.Reference.SourceBridgeFacts.SourceResultStoreContains.exec_block_succ_of_execSeq

abbrev sourceResultStoreContainsExecLetNoneSuccOfState :=
  @Yul.Reference.SourceBridgeFacts.SourceResultStoreContains.exec_let_none_succ_of_state

abbrev sourceResultStoreContainsExecLetSomeSuccOfEvalValues :=
  @Yul.Reference.SourceBridgeFacts.SourceResultStoreContains.exec_let_some_succ_of_evalValues

abbrev sourceResultStoreContainsExecAssignSuccOfEvalValues :=
  @Yul.Reference.SourceBridgeFacts.SourceResultStoreContains.exec_assign_succ_of_evalValues

abbrev sourceResultStoreContainsExecBreakSucc :=
  @Yul.Reference.SourceBridgeFacts.SourceResultStoreContains.exec_break_succ

abbrev sourceResultStoreContainsExecContinueSucc :=
  @Yul.Reference.SourceBridgeFacts.SourceResultStoreContains.exec_continue_succ

abbrev sourceResultStoreContainsExecLeaveSucc :=
  @Yul.Reference.SourceBridgeFacts.SourceResultStoreContains.exec_leave_succ

abbrev sourceResultStoreContainsExecIfSuccOfEvalAndBody :=
  @Yul.Reference.SourceBridgeFacts.SourceResultStoreContains.exec_if_succ_of_eval_and_body

abbrev sourceResultStoreContainsExecSwitchSuccOfEvalAndCase :=
  @Yul.Reference.SourceBridgeFacts.SourceResultStoreContains.exec_switch_succ_of_eval_and_case

abbrev storeDomainEmpty :=
  @Yul.Reference.StoreDomainExact.empty

abbrev storeDomainInsert :=
  @Yul.Reference.StoreDomainExact.insert

abbrev storeDomainInsertPairs :=
  @Yul.Reference.StoreDomainExact.insertPairs

abbrev storeDomainInsertZeros :=
  @Yul.Reference.StoreDomainExact.insertZeros

abbrev checkDeclarationOkFromStoreDomain :=
  @Yul.Reference.StoreDomainExact.checkDeclaration_ok

abbrev checkAssignmentOkFromStoreDomain :=
  @Yul.Reference.StoreDomainExact.checkAssignment_ok

abbrev storeDomainInsertMem :=
  @Yul.Reference.StoreDomainExact.insert_mem

abbrev stateStoreDomainRestrictStoreToOfDomain :=
  @Yul.Reference.SourceBridgeFacts.StateStoreDomainExact.restrictStoreTo_of_domain

abbrev stateStoreDomainInitcallOfLength :=
  @Yul.Reference.SourceBridgeFacts.StateStoreDomainExact.initcall_of_length

abbrev safeFunctionBodyOfContractLookup :=
  @Yul.Reference.SourceBridgeFacts.SafeLookup.function_body_safe_of_contract_lookup

abbrev scopedFunctionBodyOfContractLookup :=
  @Yul.Reference.SourceBridgeFacts.ControlFlow.function_body_scoped_of_contract_lookup

abbrev sourceResultCheckpointAllowedFunctionBodyOkOfScopedSafe :=
  @Yul.Reference.SourceBridgeFacts.SourceResultCheckpointAllowed.function_body_ok_of_scoped_safe

abbrev compilerStateRelWithTemps :=
  @Yul.Reference.CompilerStateRelWithTemps

abbrev compilerStateRelWithTempsNil :=
  @Yul.Reference.CompilerStateRel.withTemps_nil

abbrev compilerStateRelWithHiddenLocals :=
  @Yul.Reference.CompilerStateRelWithHiddenLocals

abbrev compilerStateRelWithHiddenNil :=
  @Yul.Reference.CompilerStateRel.withHidden_nil

abbrev compilerStateRelWithTempsAndHiddenLocals :=
  @Yul.Reference.CompilerStateRelWithTempsAndHiddenLocals

abbrev visibleVarSlotRel :=
  @Yul.Reference.VisibleVarSlotRel

abbrev lowerVisibleLookupSlotRel :=
  @Locals.StackLowering.VisibleLookupSlotRel

abbrev lowerVisibleLookupSlotRelConsSourceInsert :=
  @Locals.StackLowering.VisibleLookupSlotRel.cons_source_insert

abbrev lowerVisibleLookupSlotRelConsHidden :=
  @Locals.StackLowering.VisibleLookupSlotRel.cons_hidden

abbrev lowerVisibleLookupSlotRelPrefixHidden :=
  @Locals.StackLowering.VisibleLookupSlotRel.prefix_hidden

abbrev lowerVisibleLookupSlotRelAssign :=
  @Locals.StackLowering.VisibleLookupSlotRel.assign

abbrev compilerStateRelWithLayoutSlots :=
  @Yul.Reference.CompilerStateRelWithLayoutSlots

abbrev compilerStateRelWithTempsAndLayoutSlots :=
  @Yul.Reference.CompilerStateRelWithTempsAndLayoutSlots

abbrev compilerOkOutcomeRelWithLayoutSlots :=
  @Yul.Reference.BridgeFacts.CompilerOkOutcomeRelWithLayoutSlots

abbrev compilerResultOutcomeRelWithLayoutSlots :=
  @Yul.Reference.BridgeFacts.CompilerResultOutcomeRelWithLayoutSlots

abbrev compilerStateRelWithHiddenTempsNil :=
  @Yul.Reference.CompilerStateRelWithHiddenLocals.withTemps_nil

abbrev compilerStateRelWithTempsPushIncr :=
  @Yul.Reference.CompilerStateRelWithTemps.pushIncr

abbrev compilerStateRelWithTempsAndHiddenPushIncr :=
  @Yul.Reference.CompilerStateRelWithTempsAndHiddenLocals.pushIncr

abbrev compilerStateRelWithTempsAndLayoutSlotsPushIncr :=
  @Yul.Reference.BridgeFacts.CompilerStateRelWithTempsAndLayoutSlots.pushIncr

abbrev compilerStateRelRestrictVarStoreOfScopeContains :=
  @Yul.Reference.CompilerStateRel.restrictVarStore_of_scope_contains

abbrev compilerStateRelRestrictVarStoreOfDomainExact :=
  @Yul.Reference.CompilerStateRel.restrictVarStore_of_domain_exact

abbrev compilerStateRelWithTempsBindSingleExact :=
  @Yul.Reference.CompilerStateRelWithTemps.bindSingleExact

abbrev compilerStateRelWithTempsBindZerosExact :=
  @Yul.Reference.CompilerStateRelWithTemps.bindZerosExact

abbrev exactVarStackRelGet :=
  @Yul.Reference.ExactVarStackRel.get?

abbrev visibleVarSlotRelOfExact :=
  @Yul.Reference.BridgeFacts.VisibleVarSlotRel.of_exact

abbrev visibleVarSlotRelToExactOfSame :=
  @Yul.Reference.BridgeFacts.VisibleVarSlotRel.to_exact_of_same

abbrev visibleVarSlotRelOfExactHiddenPrefix :=
  @Yul.Reference.BridgeFacts.VisibleVarSlotRel.of_exact_hidden_prefix

abbrev visibleVarSlotRelConsSourceInsert :=
  @Yul.Reference.BridgeFacts.VisibleVarSlotRel.cons_source_insert

abbrev visibleVarSlotRelConsHidden :=
  @Yul.Reference.BridgeFacts.VisibleVarSlotRel.cons_hidden

abbrev visibleVarSlotRelPrefixHidden :=
  @Yul.Reference.BridgeFacts.VisibleVarSlotRel.prefix_hidden

abbrev visibleVarSlotRelAssign :=
  @Yul.Reference.BridgeFacts.VisibleVarSlotRel.assign

abbrev visibleVarSlotRelInsertPairsAppend :=
  @Yul.Reference.BridgeFacts.VisibleVarSlotRel.insertPairs_append

abbrev visibleVarSlotRelRestrictVarStoreOfScopeContains :=
  @Yul.Reference.BridgeFacts.VisibleVarSlotRel.restrictVarStore_of_scope_contains

abbrev compilerStateRelToLayoutSlots :=
  @Yul.Reference.BridgeFacts.CompilerStateRel.toLayoutSlots

abbrev compilerStateRelWithHiddenLocalsToLayoutSlots :=
  @Yul.Reference.BridgeFacts.CompilerStateRelWithHiddenLocals.toLayoutSlots

abbrev compilerStateRelWithLayoutSlotsConsSourceInsert :=
  @Yul.Reference.BridgeFacts.CompilerStateRelWithLayoutSlots.cons_source_insert

abbrev compilerStateRelWithLayoutSlotsConsHidden :=
  @Yul.Reference.BridgeFacts.CompilerStateRelWithLayoutSlots.cons_hidden

abbrev compilerStateRelWithLayoutSlotsPrefixHidden :=
  @Yul.Reference.BridgeFacts.CompilerStateRelWithLayoutSlots.prefix_hidden

abbrev compilerStateRelWithLayoutSlotsWithTempsNil :=
  @Yul.Reference.BridgeFacts.CompilerStateRelWithLayoutSlots.withTemps_nil

abbrev compilerStateRelWithLayoutSlotsAssign :=
  @Yul.Reference.BridgeFacts.CompilerStateRelWithLayoutSlots.assign

abbrev compilerStateRelWithLayoutSlotsInsertPairsAppend :=
  @Yul.Reference.BridgeFacts.CompilerStateRelWithLayoutSlots.insertPairs_append

abbrev compilerStateRelWithLayoutSlotsRestrictVarStoreOfScopeContains :=
  @Yul.Reference.BridgeFacts.CompilerStateRelWithLayoutSlots.restrictVarStore_of_scope_contains

abbrev compilerStateRelWithLayoutSlotsToCompilerStateRelOfSame :=
  @Yul.Reference.BridgeFacts.CompilerStateRelWithLayoutSlots.toCompilerStateRel_of_same

abbrev compilerResultOutcomeRelWithLayoutSlotsRestrictStoreToOfScopeContains :=
  @Yul.Reference.BridgeFacts.CompilerResultOutcomeRelWithLayoutSlots.restrictStoreTo_of_scope_contains

abbrev cleanupToCompilerStateRelWithLayoutSlotsRestrict :=
  @Yul.Reference.BridgeFacts.cleanupTo_compilerStateRelWithLayoutSlots_restrict

abbrev sourceLayoutEmbedded :=
  @Yul.Reference.BridgeFacts.SourceLayoutEmbedded

abbrev cleanupToCompilerStateRelWithLayoutSlotsSuffix :=
  @Yul.Reference.BridgeFacts.cleanupTo_compilerStateRelWithLayoutSlots_suffix

abbrev exactVarStackRelDrop :=
  @Yul.Reference.ExactVarStackRel.drop

abbrev exactVarStackRelConsInsert :=
  @Yul.Reference.ExactVarStackRel.cons_insert

abbrev exactVarStackRelInsertPairs :=
  @Yul.Reference.ExactVarStackRel.insertPairs

abbrev exactVarStackRelInsertZeros :=
  @Yul.Reference.ExactVarStackRel.insertZeros

abbrev exactVarStackRelAssign :=
  @Yul.Reference.ExactVarStackRel.assign

abbrev exactVarStackRelRestrictVarStoreOfScopeContains :=
  @Yul.Reference.ExactVarStackRel.restrictVarStore_of_scope_contains

abbrev exactVarStackRelRestrictVarStoreOfDomain :=
  @Yul.Reference.ExactVarStackRel.restrictVarStore_of_domain

abbrev exactVarStackInsertPairsAppend :=
  @Yul.Reference.VarStackRel.exact_insertPairs_append

abbrev exactVarStackInsertPairsReverse :=
  @Yul.Reference.VarStackRel.exact_insertPairs_reverse

abbrev exactVarStackInsertPairsPreserve :=
  @Yul.Reference.VarStackRel.exact_insertPairs_preserve

abbrev lookupInsertPairsPreserve :=
  @Yul.Reference.BridgeFacts.lookup_insertPairs_preserve

abbrev exactVarStackGet :=
  @Yul.Reference.VarStackRel.exact_get?

abbrev exactVarStackDrop :=
  @Yul.Reference.VarStackRel.exact_drop

abbrev insertZerosOk :=
  @Yul.Reference.VarStackRel.insertZeros_ok

abbrev restrictVarStoreSelf :=
  @Yul.Reference.FinmapFacts.restrictVarStore_self

abbrev lookupSdiffOfLookupNone :=
  @Yul.Reference.FinmapFacts.lookup_sdiff_of_lookup_none

abbrev lookupSdiffOfLookupSome :=
  @Yul.Reference.FinmapFacts.lookup_sdiff_of_lookup_some

abbrev lookupRestrictVarStoreOfScopeSome :=
  @Yul.Reference.FinmapFacts.lookup_restrictVarStore_of_scope_some

abbrev lookupRestrictVarStoreOfScopeNone :=
  @Yul.Reference.FinmapFacts.lookup_restrictVarStore_of_scope_none

abbrev noShadowingProgram :=
  @Yul.Reference.Safe.NoShadowing.program

abbrev noShadowingProgramOfAccepted :=
  @Yul.Reference.noShadowingProgram_of_accepted

abbrev letNamesFreshOfStmt :=
  @Yul.Reference.Safe.NoShadowing.let_names_fresh_of_stmt

abbrev noShadowingFreshNodup :=
  @Yul.Reference.Safe.NoShadowing.nodup_of_freshIn

abbrev noShadowingFreshNotMem :=
  @Yul.Reference.Safe.NoShadowing.not_mem_env_of_freshIn

abbrev multifillOk :=
  @Yul.Reference.VarStackRel.multifill_ok

abbrev execLetNoneOk :=
  @Yul.Reference.BridgeFacts.exec_let_none_ok

abbrev execLetNoneExactExtension :=
  @Yul.Reference.BridgeFacts.exec_let_none_exact_extension

abbrev lookupOk :=
  @Yul.Reference.BridgeFacts.lookup_ok

abbrev getElemBangOk :=
  @Yul.Reference.BridgeFacts.getElem!_ok

abbrev evalVariableExact :=
  @Yul.Reference.BridgeFacts.eval_var_exact

abbrev lowerLiteralToLocals :=
  @Yul.Expr.lower1?_lit

abbrev lowerVariableToLocals :=
  @Yul.Expr.lower1?_var

abbrev lowerBoundArgsNil :=
  @Yul.Expr.lowerBound1?_nil

abbrev lowerBoundArgsConsComponents :=
  @Yul.Expr.lowerBound1?_cons_components

abbrev lowerBoundArgsSingleComponents :=
  @Yul.Expr.lowerBound1?_single_components

abbrev lowerBoundArgsTwoComponents :=
  @Yul.Expr.lowerBound1?_two_components

abbrev lowerBoundArgsLiteralComponentsOfSome :=
  @Yul.Reference.BridgeFacts.lowerBound1?_lit_components_of_some

abbrev lowerBoundArgsLiteralPairComponentsOfSome :=
  @Yul.Reference.BridgeFacts.lowerBound1?_lit_lit_components_of_some

abbrev freshAuxNotMemUsed :=
  @Yul.Reference.BridgeFacts.freshAux_not_mem_used

abbrev freshNameNotMemUsed :=
  @Yul.Reference.BridgeFacts.fresh?_name_not_mem_used

abbrev freshStateUsed :=
  @Yul.Reference.BridgeFacts.fresh?_state_used

abbrev lowerBoundArgsLiteralPairComponentsDistinctOfSome :=
  @Yul.Reference.BridgeFacts.lowerBound1?_lit_lit_components_distinct_of_some

abbrev lowerAddOfBoundArgsTwo :=
  @Yul.Expr.lower1?_add_of_lowerBound1?_two

abbrev lowerMulOfBoundArgsTwo :=
  @Yul.Expr.lower1?_mul_of_lowerBound1?_two

abbrev lowerSubOfBoundArgsTwo :=
  @Yul.Expr.lower1?_sub_of_lowerBound1?_two

abbrev lowerDivOfBoundArgsTwo :=
  @Yul.Expr.lower1?_div_of_lowerBound1?_two

abbrev lowerSdivOfBoundArgsTwo :=
  @Yul.Expr.lower1?_sdiv_of_lowerBound1?_two

abbrev lowerModOfBoundArgsTwo :=
  @Yul.Expr.lower1?_mod_of_lowerBound1?_two

abbrev lowerSmodOfBoundArgsTwo :=
  @Yul.Expr.lower1?_smod_of_lowerBound1?_two

abbrev lowerAddmodOfBoundArgsThree :=
  @Yul.Expr.lower1?_addmod_of_lowerBound1?_three

abbrev lowerMulmodOfBoundArgsThree :=
  @Yul.Expr.lower1?_mulmod_of_lowerBound1?_three

abbrev lowerExpOfBoundArgsTwo :=
  @Yul.Expr.lower1?_exp_of_lowerBound1?_two

abbrev lowerSignextendOfBoundArgsTwo :=
  @Yul.Expr.lower1?_signextend_of_lowerBound1?_two

abbrev lowerLtOfBoundArgsTwo :=
  @Yul.Expr.lower1?_lt_of_lowerBound1?_two

abbrev lowerGtOfBoundArgsTwo :=
  @Yul.Expr.lower1?_gt_of_lowerBound1?_two

abbrev lowerSltOfBoundArgsTwo :=
  @Yul.Expr.lower1?_slt_of_lowerBound1?_two

abbrev lowerSgtOfBoundArgsTwo :=
  @Yul.Expr.lower1?_sgt_of_lowerBound1?_two

abbrev lowerEqOfBoundArgsTwo :=
  @Yul.Expr.lower1?_eq_of_lowerBound1?_two

abbrev lowerAndOfBoundArgsTwo :=
  @Yul.Expr.lower1?_and_of_lowerBound1?_two

abbrev lowerOrOfBoundArgsTwo :=
  @Yul.Expr.lower1?_or_of_lowerBound1?_two

abbrev lowerXorOfBoundArgsTwo :=
  @Yul.Expr.lower1?_xor_of_lowerBound1?_two

abbrev lowerByteOfBoundArgsTwo :=
  @Yul.Expr.lower1?_byte_of_lowerBound1?_two

abbrev lowerShlOfBoundArgsTwo :=
  @Yul.Expr.lower1?_shl_of_lowerBound1?_two

abbrev lowerShrOfBoundArgsTwo :=
  @Yul.Expr.lower1?_shr_of_lowerBound1?_two

abbrev lowerSarOfBoundArgsTwo :=
  @Yul.Expr.lower1?_sar_of_lowerBound1?_two

abbrev lowerPrimitiveOfBoundArgs :=
  @Yul.Expr.lower1?_prim_of_lowerBound1?

abbrev lowerZeroResultPrimitiveOfBoundArgs :=
  @Yul.Expr.lower0?_prim_of_lowerBound1?

abbrev lowerZeroResultPrimitivePreludeSoundOfBoundArgs :=
  @Yul.Reference.SourceBridgeFacts.lower0?_prim_exprValuePreludeSound_of_lowerBound1?

abbrev boundArgLowering :=
  @Yul.Expr.List.BoundLowering

abbrev boundArgLoweringToLowerBoundArgs :=
  @Yul.Expr.List.BoundLowering.to_lowerBound1?

abbrev boundArgLoweringLengthLowerArgs :=
  @Yul.Expr.List.BoundLowering.length_lowerArgs_eq

abbrev boundArgLoweringLowerArgsVars :=
  @Yul.Expr.List.BoundLowering.lowerArgs_vars

abbrev boundArgLoweringOfLowerBoundArgs :=
  @Yul.Expr.List.boundLowering_of_lowerBound1?

abbrev lowerBoundArgsLengthLowerArgs :=
  @Yul.Expr.List.lowerBound1?_length_lowerArgs_eq

abbrev lowerBoundArgsLowerArgsVars :=
  @Yul.Expr.List.lowerBound1?_lowerArgs_vars

abbrev lowerLetLiteralSingleToFunctions :=
  @Yul.Reference.BridgeFacts.toFunctionsListFuel?_let_lit_single

abbrev lowerLetVariableSingleToFunctions :=
  @Yul.Reference.BridgeFacts.toFunctionsListFuel?_let_var_single

abbrev lowerLetPrimitiveSingleComponents :=
  @Yul.Reference.BridgeFacts.toFunctionsListFuel?_let_prim_single_components

abbrev lowerLetUserCallToFunctionsEq :=
  @Yul.Reference.BridgeFacts.toFunctionsListFuel?_let_user_call_eq

abbrev lowerLetUserCallComponents :=
  @Yul.Reference.BridgeFacts.toFunctionsListFuel?_let_user_call_components

abbrev sourceRegularSeqRunBridgeHiddenConsLetPrimitiveOfLower :=
  @Yul.Reference.BridgeFacts.sourceRegularSeqRunBridgeHidden_cons_let_prim_of_lower

abbrev lowerLetNoneSingleToFunctions :=
  @Yul.Reference.BridgeFacts.toFunctionsListFuel?_let_none_single

abbrev lowerAssignLiteralSingleToFunctions :=
  @Yul.Reference.BridgeFacts.toFunctionsListFuel?_assign_lit_single

abbrev lowerAssignVariableSingleToFunctions :=
  @Yul.Reference.BridgeFacts.toFunctionsListFuel?_assign_var_single

abbrev lowerAssignPrimitiveSingleComponents :=
  @Yul.Reference.BridgeFacts.toFunctionsListFuel?_assign_prim_single_components

abbrev lowerAssignUserCallToFunctionsEq :=
  @Yul.Reference.BridgeFacts.toFunctionsListFuel?_assign_user_call_eq

abbrev lowerAssignUserCallComponents :=
  @Yul.Reference.BridgeFacts.toFunctionsListFuel?_assign_user_call_components

abbrev sourceRegularSeqRunBridgeHiddenConsAssignPrimitiveOfLower :=
  @Yul.Reference.BridgeFacts.sourceRegularSeqRunBridgeHidden_cons_assign_prim_of_lower

abbrev lowerExpressionPrimitiveSingleComponents :=
  @Yul.Reference.BridgeFacts.toFunctionsListFuel?_expr_prim_components

abbrev sourceRegularSeqRunBridgeHiddenConsExpressionPrimitivePrelude :=
  @Yul.Reference.SourceBridgeFacts.sourceRegularSeqRunBridgeHidden_cons_expr_prim_prelude

abbrev sourceRegularSeqRunBridgeHiddenConsExpressionPrimitiveOfLower :=
  @Yul.Reference.BridgeFacts.sourceRegularSeqRunBridgeHidden_cons_expr_prim_of_lower

abbrev exprValueBridgeWithLayoutSlots :=
  @Yul.Reference.BridgeFacts.ExprValueBridgeWithLayoutSlots

abbrev exprValueBridgeWithLayoutSlotsPreservingBase :=
  @Yul.Reference.BridgeFacts.ExprValueBridgeWithLayoutSlotsPreservingBase

abbrev exprValueBridgeWithLayoutSlotsPreservingBaseToBridge :=
  @Yul.Reference.BridgeFacts.ExprValueBridgeWithLayoutSlotsPreservingBase.toBridge

abbrev exprValueBridgeWithLayoutSlotsLiteral :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_lit

abbrev exprValueBridgeWithLayoutSlotsVariable :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_var

abbrev exprValueBridgeWithLayoutSlotsPreservingBaseLiteral :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlotsPreservingBase_lit

abbrev exprValueBridgeWithLayoutSlotsPreservingBaseVariable :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlotsPreservingBase_var

abbrev evalOfEvalValuesSingle :=
  @Yul.Reference.BridgeFacts.eval_of_evalValues_single

abbrev evalArgsSingletonOfEvalValuesSingle :=
  @Yul.Reference.BridgeFacts.evalArgs_singleton_of_evalValues_single

abbrev evalArgsPairOfEvalValuesSingle :=
  @Yul.Reference.BridgeFacts.evalArgs_pair_of_evalValues_single

abbrev evalArgsSingletonLitReverseOkEq :=
  @Yul.Reference.BridgeFacts.evalArgs_singleton_lit_reverse_ok_eq

abbrev evalArgsLitLitReverseOkEq :=
  @Yul.Reference.BridgeFacts.evalArgs_lit_lit_reverse_ok_eq

abbrev evalArgsAppendFuel :=
  @Yul.Reference.BridgeFacts.evalArgsAppendFuel

abbrev evalArgsAppendSingletonScheduled :=
  @Yul.Reference.BridgeFacts.evalArgs_append_singleton_scheduled

abbrev evalArgsReverseConsScheduledOfEvalValues :=
  @Yul.Reference.BridgeFacts.evalArgs_reverse_cons_scheduled_of_evalValues

abbrev lowerPrimCallIszeroOk :=
  @Yul.PrimSemantics.primCall_iszero_ok

abbrev lowerPrimCallNotOk :=
  @Yul.PrimSemantics.primCall_not_ok

abbrev lowerPrimCallAddOk :=
  @Yul.PrimSemantics.primCall_add_ok

abbrev lowerPrimCallMulOk :=
  @Yul.PrimSemantics.primCall_mul_ok

abbrev lowerPrimCallSubOk :=
  @Yul.PrimSemantics.primCall_sub_ok

abbrev lowerPrimCallDivOk :=
  @Yul.PrimSemantics.primCall_div_ok

abbrev lowerPrimCallSdivOk :=
  @Yul.PrimSemantics.primCall_sdiv_ok

abbrev lowerPrimCallModOk :=
  @Yul.PrimSemantics.primCall_mod_ok

abbrev lowerPrimCallSmodOk :=
  @Yul.PrimSemantics.primCall_smod_ok

abbrev lowerPrimCallAddmodOk :=
  @Yul.PrimSemantics.primCall_addmod_ok

abbrev lowerPrimCallMulmodOk :=
  @Yul.PrimSemantics.primCall_mulmod_ok

abbrev lowerPrimCallKeccak256Ok :=
  @Yul.PrimSemantics.primCall_keccak256_ok

abbrev lowerPrimCallKeccak256StateEqOfOkOfNonOk :=
  @Yul.PrimSemantics.primCall_keccak256_state_eq_of_ok_of_nonOk

abbrev lowerPrimCallKeccakStoreEqOfOk :=
  @Yul.PrimSemantics.primCall_keccak_store_eq_of_ok

abbrev lowerWrappedBinaryMachineStateOpNotCheckpointOfOk :=
  @Yul.PrimSemantics.wrapped_binaryMachineStateOp_not_checkpoint_of_ok

abbrev lowerWrappedBinaryMachineStateOpPrimeNotCheckpointOfOk :=
  @Yul.PrimSemantics.wrapped_binaryMachineStateOp'_not_checkpoint_of_ok

abbrev lowerWrappedTernaryMachineStateOpNotCheckpointOfOk :=
  @Yul.PrimSemantics.wrapped_ternaryMachineStateOp_not_checkpoint_of_ok

abbrev lowerWrappedUnaryStateOpNotCheckpointOfOk :=
  @Yul.PrimSemantics.wrapped_unaryStateOp_not_checkpoint_of_ok

abbrev lowerWrappedBinaryStateOpNotCheckpointOfOk :=
  @Yul.PrimSemantics.wrapped_binaryStateOp_not_checkpoint_of_ok

abbrev lowerWrappedTernaryCopyOpNotCheckpointOfOk :=
  @Yul.PrimSemantics.wrapped_ternaryCopyOp_not_checkpoint_of_ok

abbrev lowerPrimCallStopArithStateEqOfOk :=
  @Yul.PrimSemantics.primCall_stopArith_state_eq_of_ok

abbrev lowerPrimCallStopArithStoreEqOfOk :=
  @Yul.PrimSemantics.primCall_stopArith_store_eq_of_ok

abbrev lowerPrimCallCompBitStateEqOfOk :=
  @Yul.PrimSemantics.primCall_compBit_state_eq_of_ok

abbrev lowerPrimCallCompBitStoreEqOfOk :=
  @Yul.PrimSemantics.primCall_compBit_store_eq_of_ok

abbrev lowerPrimCallBlockStateEqOfOkOfNonOk :=
  @Yul.PrimSemantics.primCall_block_state_eq_of_ok_of_nonOk

abbrev lowerPrimCallBlockStoreEqOfOk :=
  @Yul.PrimSemantics.primCall_block_store_eq_of_ok

abbrev lowerPrimCallBlockNotCheckpointOfOk :=
  @Yul.PrimSemantics.primCall_block_not_checkpoint_of_ok

abbrev lowerEnvCheckpointSafe :=
  Yul.PrimSemantics.EnvCheckpointSafe

abbrev lowerPrimCallReturnDataCopyStateEqOfOkOfNonOk :=
  @Yul.PrimSemantics.primCall_returndatacopy_state_eq_of_ok_of_nonOk

abbrev lowerPrimCallReturnDataCopyStoreEqOfOk :=
  @Yul.PrimSemantics.primCall_returndatacopy_store_eq_of_ok

abbrev lowerPrimCallReturnDataCopyNotCheckpointOfOk :=
  @Yul.PrimSemantics.primCall_returndatacopy_not_checkpoint_of_ok

abbrev lowerPrimCallEnvStateEqOfOkOfNonOk :=
  @Yul.PrimSemantics.primCall_env_state_eq_of_ok_of_nonOk

abbrev lowerPrimCallEnvStoreEqOfOk :=
  @Yul.PrimSemantics.primCall_env_store_eq_of_ok

abbrev lowerPrimCallEnvNotCheckpointOfOk :=
  @Yul.PrimSemantics.primCall_env_not_checkpoint_of_ok

abbrev lowerStackMemFlowCheckpointSafe :=
  Yul.PrimSemantics.StackMemFlowCheckpointSafe

abbrev lowerPrimCallMLoadStateEqOfOkOfNonOk :=
  @Yul.PrimSemantics.primCall_mload_state_eq_of_ok_of_nonOk

abbrev lowerPrimCallMLoadNotCheckpointOfOk :=
  @Yul.PrimSemantics.primCall_mload_not_checkpoint_of_ok

abbrev lowerPrimCallStackMemFlowStateEqOfOkOfNonOk :=
  @Yul.PrimSemantics.primCall_stackMemFlow_state_eq_of_ok_of_nonOk

abbrev lowerPrimCallStackMemFlowNotCheckpointOfOk :=
  @Yul.PrimSemantics.primCall_stackMemFlow_not_checkpoint_of_ok

abbrev lowerSystemCheckpointSafe :=
  Yul.PrimSemantics.SystemCheckpointSafe

abbrev lowerPrimCallReturnImpossibleOfOk :=
  @Yul.PrimSemantics.primCall_return_impossible_of_ok

abbrev lowerPrimCallRevertImpossibleOfOk :=
  @Yul.PrimSemantics.primCall_revert_impossible_of_ok

abbrev lowerPrimCallInvalidImpossibleOfOk :=
  @Yul.PrimSemantics.primCall_invalid_impossible_of_ok

abbrev lowerPrimCallSelfdestructImpossibleOfOk :=
  @Yul.PrimSemantics.primCall_selfdestruct_impossible_of_ok

abbrev lowerPrimCallExpOk :=
  @Yul.PrimSemantics.primCall_exp_ok

abbrev lowerPrimCallSignextendOk :=
  @Yul.PrimSemantics.primCall_signextend_ok

abbrev lowerPrimCallLtOk :=
  @Yul.PrimSemantics.primCall_lt_ok

abbrev lowerPrimCallGtOk :=
  @Yul.PrimSemantics.primCall_gt_ok

abbrev lowerPrimCallSltOk :=
  @Yul.PrimSemantics.primCall_slt_ok

abbrev lowerPrimCallSgtOk :=
  @Yul.PrimSemantics.primCall_sgt_ok

abbrev lowerPrimCallEqOk :=
  @Yul.PrimSemantics.primCall_eq_ok

abbrev lowerPrimCallAndOk :=
  @Yul.PrimSemantics.primCall_and_ok

abbrev lowerPrimCallOrOk :=
  @Yul.PrimSemantics.primCall_or_ok

abbrev lowerPrimCallXorOk :=
  @Yul.PrimSemantics.primCall_xor_ok

abbrev lowerPrimCallByteOk :=
  @Yul.PrimSemantics.primCall_byte_ok

abbrev lowerPrimCallShlOk :=
  @Yul.PrimSemantics.primCall_shl_ok

abbrev lowerPrimCallShrOk :=
  @Yul.PrimSemantics.primCall_shr_ok

abbrev lowerPrimCallSarOk :=
  @Yul.PrimSemantics.primCall_sar_ok

abbrev lowerPrimCallAddressOk :=
  @Yul.PrimSemantics.primCall_address_ok

abbrev lowerPrimCallBalanceOk :=
  @Yul.PrimSemantics.primCall_balance_ok

abbrev lowerPrimCallSloadOk :=
  @Yul.PrimSemantics.primCall_sload_ok

abbrev lowerPrimCallSstoreOkOfWritable :=
  @Yul.PrimSemantics.primCall_sstore_ok_of_writable

abbrev lowerPrimCallSstoreStaticError :=
  @Yul.PrimSemantics.primCall_sstore_static_error

abbrev lowerPrimCallSstoreStoreEqOfOk :=
  @Yul.PrimSemantics.primCall_sstore_store_eq_of_ok

abbrev lowerPrimCallTloadOk :=
  @Yul.PrimSemantics.primCall_tload_ok

abbrev lowerPrimCallTstoreOkOfWritable :=
  @Yul.PrimSemantics.primCall_tstore_ok_of_writable

abbrev lowerPrimCallTstoreStaticError :=
  @Yul.PrimSemantics.primCall_tstore_static_error

abbrev lowerPrimCallTstoreStoreEqOfOk :=
  @Yul.PrimSemantics.primCall_tstore_store_eq_of_ok

abbrev lowerPrimCallMloadStoreEqOfOk :=
  @Yul.PrimSemantics.primCall_mload_store_eq_of_ok

abbrev lowerPrimCallStackMemFlowStoreEqOfOk :=
  @Yul.PrimSemantics.primCall_stackMemFlow_store_eq_of_ok

abbrev lowerPrimCallLog0OkOfWritable :=
  @Yul.PrimSemantics.primCall_log0_ok_of_writable

abbrev lowerPrimCallLog0StaticError :=
  @Yul.PrimSemantics.primCall_log0_static_error

abbrev lowerPrimCallLog1OkOfWritable :=
  @Yul.PrimSemantics.primCall_log1_ok_of_writable

abbrev lowerPrimCallLog1StaticError :=
  @Yul.PrimSemantics.primCall_log1_static_error

abbrev lowerPrimCallMloadOk :=
  @Yul.PrimSemantics.primCall_mload_ok

abbrev lowerPrimCallPopOk :=
  @Yul.PrimSemantics.primCall_pop_ok

abbrev lowerPrimCallMstoreOk :=
  @Yul.PrimSemantics.primCall_mstore_ok

abbrev lowerPrimCallMstore8Ok :=
  @Yul.PrimSemantics.primCall_mstore8_ok

abbrev lowerPrimCallMcopyOk :=
  @Yul.PrimSemantics.primCall_mcopy_ok

abbrev lowerPrimCallOriginOk :=
  @Yul.PrimSemantics.primCall_origin_ok

abbrev lowerPrimCallCallerOk :=
  @Yul.PrimSemantics.primCall_caller_ok

abbrev lowerPrimCallCallvalueOk :=
  @Yul.PrimSemantics.primCall_callvalue_ok

abbrev lowerPrimCallCalldataloadOk :=
  @Yul.PrimSemantics.primCall_calldataload_ok

abbrev lowerPrimCallCalldatasizeOk :=
  @Yul.PrimSemantics.primCall_calldatasize_ok

abbrev lowerPrimCallCalldatacopyOk :=
  @Yul.PrimSemantics.primCall_calldatacopy_ok

abbrev lowerPrimCallReturndatacopyOk :=
  @Yul.PrimSemantics.primCall_returndatacopy_ok

abbrev lowerPrimCallGaspriceOk :=
  @Yul.PrimSemantics.primCall_gasprice_ok

abbrev lowerPrimCallPrevrandaoOk :=
  @Yul.PrimSemantics.primCall_prevrandao_ok

abbrev lowerPrimCallBasefeeOk :=
  @Yul.PrimSemantics.primCall_basefee_ok

abbrev lowerPrimCallBlobbasefeeOk :=
  @Yul.PrimSemantics.primCall_blobbasefee_ok

abbrev lowerPrimCallCoinbaseOk :=
  @Yul.PrimSemantics.primCall_coinbase_ok

abbrev lowerPrimCallTimestampOk :=
  @Yul.PrimSemantics.primCall_timestamp_ok

abbrev lowerPrimCallNumberOk :=
  @Yul.PrimSemantics.primCall_number_ok

abbrev lowerPrimCallGaslimitOk :=
  @Yul.PrimSemantics.primCall_gaslimit_ok

abbrev lowerPrimCallChainidOk :=
  @Yul.PrimSemantics.primCall_chainid_ok

abbrev lowerPrimCallBlockhashOk :=
  @Yul.PrimSemantics.primCall_blockhash_ok

abbrev lowerPrimCallSelfbalanceOk :=
  @Yul.PrimSemantics.primCall_selfbalance_ok

abbrev lowerPrimCallBlobhashOk :=
  @Yul.PrimSemantics.primCall_blobhash_ok

abbrev lowerPrimCallReturndatasizeOk :=
  @Yul.PrimSemantics.primCall_returndatasize_ok

abbrev lowerPrimCallMsizeOk :=
  @Yul.PrimSemantics.primCall_msize_ok

abbrev lowerPrimCallGasOk :=
  @Yul.PrimSemantics.primCall_gas_ok

abbrev lowerBasicOpStepIszeroOfStack :=
  @Yul.PrimSemantics.basicOp_step_iszero_of_stack

abbrev lowerBasicOpStepNotOfStack :=
  @Yul.PrimSemantics.basicOp_step_not_of_stack

abbrev lowerBasicOpStepAddOfStack :=
  @Yul.PrimSemantics.basicOp_step_add_of_stack

abbrev lowerBasicOpStepMulOfStack :=
  @Yul.PrimSemantics.basicOp_step_mul_of_stack

abbrev lowerBasicOpStepSubOfStack :=
  @Yul.PrimSemantics.basicOp_step_sub_of_stack

abbrev lowerBasicOpStepDivOfStack :=
  @Yul.PrimSemantics.basicOp_step_div_of_stack

abbrev lowerBasicOpStepSdivOfStack :=
  @Yul.PrimSemantics.basicOp_step_sdiv_of_stack

abbrev lowerBasicOpStepModOfStack :=
  @Yul.PrimSemantics.basicOp_step_mod_of_stack

abbrev lowerBasicOpStepSmodOfStack :=
  @Yul.PrimSemantics.basicOp_step_smod_of_stack

abbrev lowerBasicOpStepAddmodOfStack :=
  @Yul.PrimSemantics.basicOp_step_addmod_of_stack

abbrev lowerBasicOpStepMulmodOfStack :=
  @Yul.PrimSemantics.basicOp_step_mulmod_of_stack

abbrev lowerBasicOpStepExpOfStack :=
  @Yul.PrimSemantics.basicOp_step_exp_of_stack

abbrev lowerBasicOpStepSignextendOfStack :=
  @Yul.PrimSemantics.basicOp_step_signextend_of_stack

abbrev lowerBasicOpStepLtOfStack :=
  @Yul.PrimSemantics.basicOp_step_lt_of_stack

abbrev lowerBasicOpStepGtOfStack :=
  @Yul.PrimSemantics.basicOp_step_gt_of_stack

abbrev lowerBasicOpStepSltOfStack :=
  @Yul.PrimSemantics.basicOp_step_slt_of_stack

abbrev lowerBasicOpStepSgtOfStack :=
  @Yul.PrimSemantics.basicOp_step_sgt_of_stack

abbrev lowerBasicOpStepEqOfStack :=
  @Yul.PrimSemantics.basicOp_step_eq_of_stack

abbrev lowerBasicOpStepAndOfStack :=
  @Yul.PrimSemantics.basicOp_step_and_of_stack

abbrev lowerBasicOpStepOrOfStack :=
  @Yul.PrimSemantics.basicOp_step_or_of_stack

abbrev lowerBasicOpStepXorOfStack :=
  @Yul.PrimSemantics.basicOp_step_xor_of_stack

abbrev lowerBasicOpStepByteOfStack :=
  @Yul.PrimSemantics.basicOp_step_byte_of_stack

abbrev lowerBasicOpStepShlOfStack :=
  @Yul.PrimSemantics.basicOp_step_shl_of_stack

abbrev lowerBasicOpStepShrOfStack :=
  @Yul.PrimSemantics.basicOp_step_shr_of_stack

abbrev lowerBasicOpStepSarOfStack :=
  @Yul.PrimSemantics.basicOp_step_sar_of_stack

abbrev lowerBasicOpStepAddressOfStack :=
  @Yul.PrimSemantics.basicOp_step_address_of_stack

abbrev lowerBasicOpStepExecutionEnvOfStack :=
  @Yul.PrimSemantics.basicOp_step_executionEnv_of_stack

abbrev lowerBasicOpStepStateOfStack :=
  @Yul.PrimSemantics.basicOp_step_state_of_stack

abbrev lowerBasicOpStepMachineStateOfStack :=
  @Yul.PrimSemantics.basicOp_step_machineState_of_stack

abbrev lowerBasicOpStepUnaryStateSameOfStack :=
  @Yul.PrimSemantics.basicOp_step_unaryState_same_of_stack

abbrev lowerBasicOpStepUnaryStateOfStack :=
  @Yul.PrimSemantics.basicOp_step_unaryState_of_stack

abbrev lowerBasicOpStepPopOfStack :=
  @Yul.PrimSemantics.basicOp_step_pop_of_stack

abbrev lowerBasicOpStepMloadOfStack :=
  @Yul.PrimSemantics.basicOp_step_mload_of_stack

abbrev lowerBasicOpStepMstoreOfStack :=
  @Yul.PrimSemantics.basicOp_step_mstore_of_stack

abbrev lowerBasicOpStepBinaryStateOfStack :=
  @Yul.PrimSemantics.basicOp_step_binaryState_of_stack

abbrev lowerBasicOpStepSstoreOfStack :=
  @Yul.PrimSemantics.basicOp_step_sstore_of_stack

abbrev lowerBasicOpStepTstoreOfStack :=
  @Yul.PrimSemantics.basicOp_step_tstore_of_stack

abbrev lowerBasicOpStepLog0OfStack :=
  @Yul.PrimSemantics.basicOp_step_log0_of_stack

abbrev lowerBasicOpStepLog1OfStack :=
  @Yul.PrimSemantics.basicOp_step_log1_of_stack

abbrev lowerBasicOpStepMstore8OfStack :=
  @Yul.PrimSemantics.basicOp_step_mstore8_of_stack

abbrev lowerBasicOpStepKeccak256OfStack :=
  @Yul.PrimSemantics.basicOp_step_keccak256_of_stack

abbrev lowerBasicOpStepTernaryCopyOfStack :=
  @Yul.PrimSemantics.basicOp_step_ternaryCopy_of_stack

abbrev lowerBasicOpStepTernaryMachineStateOfStack :=
  @Yul.PrimSemantics.basicOp_step_ternaryMachineState_of_stack

abbrev lowerBasicOpStepReturndatacopyOfStack :=
  @Yul.PrimSemantics.basicOp_step_returndatacopy_of_stack

abbrev lowerBasicOpStepUnaryExecutionEnvOfStack :=
  @Yul.PrimSemantics.basicOp_step_unaryExecutionEnv_of_stack

abbrev yulPrimCallIszeroOk :=
  @Yul.Reference.BridgeFacts.yul_primCall_iszero_ok

abbrev yulPrimCallNotOk :=
  @Yul.Reference.BridgeFacts.yul_primCall_not_ok

abbrev yulPrimCallAddOk :=
  @Yul.Reference.BridgeFacts.yul_primCall_add_ok

abbrev yulPrimCallMulOk :=
  @Yul.Reference.BridgeFacts.yul_primCall_mul_ok

abbrev yulPrimCallSubOk :=
  @Yul.Reference.BridgeFacts.yul_primCall_sub_ok

abbrev yulPrimCallDivOk :=
  @Yul.Reference.BridgeFacts.yul_primCall_div_ok

abbrev yulPrimCallSdivOk :=
  @Yul.Reference.BridgeFacts.yul_primCall_sdiv_ok

abbrev yulPrimCallModOk :=
  @Yul.Reference.BridgeFacts.yul_primCall_mod_ok

abbrev yulPrimCallSmodOk :=
  @Yul.Reference.BridgeFacts.yul_primCall_smod_ok

abbrev yulPrimCallAddmodOk :=
  @Yul.Reference.BridgeFacts.yul_primCall_addmod_ok

abbrev yulPrimCallMulmodOk :=
  @Yul.Reference.BridgeFacts.yul_primCall_mulmod_ok

abbrev yulPrimCallExpOk :=
  @Yul.Reference.BridgeFacts.yul_primCall_exp_ok

abbrev yulPrimCallSignextendOk :=
  @Yul.Reference.BridgeFacts.yul_primCall_signextend_ok

abbrev yulPrimCallLtOk :=
  @Yul.Reference.BridgeFacts.yul_primCall_lt_ok

abbrev yulPrimCallGtOk :=
  @Yul.Reference.BridgeFacts.yul_primCall_gt_ok

abbrev yulPrimCallSltOk :=
  @Yul.Reference.BridgeFacts.yul_primCall_slt_ok

abbrev yulPrimCallSgtOk :=
  @Yul.Reference.BridgeFacts.yul_primCall_sgt_ok

abbrev yulPrimCallEqOk :=
  @Yul.Reference.BridgeFacts.yul_primCall_eq_ok

abbrev yulPrimCallAndOk :=
  @Yul.Reference.BridgeFacts.yul_primCall_and_ok

abbrev yulPrimCallOrOk :=
  @Yul.Reference.BridgeFacts.yul_primCall_or_ok

abbrev yulPrimCallXorOk :=
  @Yul.Reference.BridgeFacts.yul_primCall_xor_ok

abbrev yulPrimCallByteOk :=
  @Yul.Reference.BridgeFacts.yul_primCall_byte_ok

abbrev yulPrimCallShlOk :=
  @Yul.Reference.BridgeFacts.yul_primCall_shl_ok

abbrev yulPrimCallShrOk :=
  @Yul.Reference.BridgeFacts.yul_primCall_shr_ok

abbrev yulPrimCallSarOk :=
  @Yul.Reference.BridgeFacts.yul_primCall_sar_ok

abbrev yulPrimCallKeccak256Ok :=
  @Yul.Reference.BridgeFacts.yul_primCall_keccak256_ok

abbrev yulPrimCallAddressOk :=
  @Yul.Reference.BridgeFacts.yul_primCall_address_ok

abbrev yulPrimCallBalanceOk :=
  @Yul.Reference.BridgeFacts.yul_primCall_balance_ok

abbrev yulPrimCallSloadOk :=
  @Yul.Reference.BridgeFacts.yul_primCall_sload_ok

abbrev yulPrimCallSstoreOkOfWritable :=
  @Yul.Reference.BridgeFacts.yul_primCall_sstore_ok_of_writable

abbrev yulPrimCallSstoreStaticError :=
  @Yul.Reference.BridgeFacts.yul_primCall_sstore_static_error

abbrev yulPrimCallTloadOk :=
  @Yul.Reference.BridgeFacts.yul_primCall_tload_ok

abbrev yulPrimCallTstoreOkOfWritable :=
  @Yul.Reference.BridgeFacts.yul_primCall_tstore_ok_of_writable

abbrev yulPrimCallTstoreStaticError :=
  @Yul.Reference.BridgeFacts.yul_primCall_tstore_static_error

abbrev yulPrimCallLog0OkOfWritable :=
  @Yul.Reference.BridgeFacts.yul_primCall_log0_ok_of_writable

abbrev yulPrimCallLog0StaticError :=
  @Yul.Reference.BridgeFacts.yul_primCall_log0_static_error

abbrev yulPrimCallLog1OkOfWritable :=
  @Yul.Reference.BridgeFacts.yul_primCall_log1_ok_of_writable

abbrev yulPrimCallLog1StaticError :=
  @Yul.Reference.BridgeFacts.yul_primCall_log1_static_error

abbrev yulPrimCallMloadOk :=
  @Yul.Reference.BridgeFacts.yul_primCall_mload_ok

abbrev yulPrimCallPopOk :=
  @Yul.Reference.BridgeFacts.yul_primCall_pop_ok

abbrev importedEvalArgsLengthOfOk :=
  @Yul.Reference.Imported.evalArgs_length_of_ok

abbrev yulPrimCallMstoreOk :=
  @Yul.Reference.BridgeFacts.yul_primCall_mstore_ok

abbrev yulPrimCallMstore8Ok :=
  @Yul.Reference.BridgeFacts.yul_primCall_mstore8_ok

abbrev yulPrimCallMcopyOk :=
  @Yul.Reference.BridgeFacts.yul_primCall_mcopy_ok

abbrev yulPrimCallOriginOk :=
  @Yul.Reference.BridgeFacts.yul_primCall_origin_ok

abbrev yulPrimCallCallerOk :=
  @Yul.Reference.BridgeFacts.yul_primCall_caller_ok

abbrev yulPrimCallCallvalueOk :=
  @Yul.Reference.BridgeFacts.yul_primCall_callvalue_ok

abbrev yulPrimCallCalldataloadOk :=
  @Yul.Reference.BridgeFacts.yul_primCall_calldataload_ok

abbrev yulPrimCallCalldatasizeOk :=
  @Yul.Reference.BridgeFacts.yul_primCall_calldatasize_ok

abbrev yulPrimCallCalldatacopyOk :=
  @Yul.Reference.BridgeFacts.yul_primCall_calldatacopy_ok

abbrev yulPrimCallReturndatacopyOk :=
  @Yul.Reference.BridgeFacts.yul_primCall_returndatacopy_ok

abbrev yulPrimCallGaspriceOk :=
  @Yul.Reference.BridgeFacts.yul_primCall_gasprice_ok

abbrev yulPrimCallPrevrandaoOk :=
  @Yul.Reference.BridgeFacts.yul_primCall_prevrandao_ok

abbrev yulPrimCallBasefeeOk :=
  @Yul.Reference.BridgeFacts.yul_primCall_basefee_ok

abbrev yulPrimCallBlobbasefeeOk :=
  @Yul.Reference.BridgeFacts.yul_primCall_blobbasefee_ok

abbrev yulPrimCallCoinbaseOk :=
  @Yul.Reference.BridgeFacts.yul_primCall_coinbase_ok

abbrev yulPrimCallTimestampOk :=
  @Yul.Reference.BridgeFacts.yul_primCall_timestamp_ok

abbrev yulPrimCallNumberOk :=
  @Yul.Reference.BridgeFacts.yul_primCall_number_ok

abbrev yulPrimCallGaslimitOk :=
  @Yul.Reference.BridgeFacts.yul_primCall_gaslimit_ok

abbrev yulPrimCallChainidOk :=
  @Yul.Reference.BridgeFacts.yul_primCall_chainid_ok

abbrev yulPrimCallBlockhashOk :=
  @Yul.Reference.BridgeFacts.yul_primCall_blockhash_ok

abbrev yulPrimCallSelfbalanceOk :=
  @Yul.Reference.BridgeFacts.yul_primCall_selfbalance_ok

abbrev yulPrimCallBlobhashOk :=
  @Yul.Reference.BridgeFacts.yul_primCall_blobhash_ok

abbrev yulPrimCallReturndatasizeOk :=
  @Yul.Reference.BridgeFacts.yul_primCall_returndatasize_ok

abbrev yulPrimCallMsizeOk :=
  @Yul.Reference.BridgeFacts.yul_primCall_msize_ok

abbrev yulPrimCallGasOk :=
  @Yul.Reference.BridgeFacts.yul_primCall_gas_ok

abbrev basicOpStepIszeroOfStack :=
  @Yul.Reference.BridgeFacts.basicOp_step_iszero_of_stack

abbrev basicOpStepNotOfStack :=
  @Yul.Reference.BridgeFacts.basicOp_step_not_of_stack

abbrev basicOpStepAddOfStack :=
  @Yul.Reference.BridgeFacts.basicOp_step_add_of_stack

abbrev basicOpStepMulOfStack :=
  @Yul.Reference.BridgeFacts.basicOp_step_mul_of_stack

abbrev basicOpStepSubOfStack :=
  @Yul.Reference.BridgeFacts.basicOp_step_sub_of_stack

abbrev basicOpStepDivOfStack :=
  @Yul.Reference.BridgeFacts.basicOp_step_div_of_stack

abbrev basicOpStepSdivOfStack :=
  @Yul.Reference.BridgeFacts.basicOp_step_sdiv_of_stack

abbrev basicOpStepModOfStack :=
  @Yul.Reference.BridgeFacts.basicOp_step_mod_of_stack

abbrev basicOpStepSmodOfStack :=
  @Yul.Reference.BridgeFacts.basicOp_step_smod_of_stack

abbrev basicOpStepAddmodOfStack :=
  @Yul.Reference.BridgeFacts.basicOp_step_addmod_of_stack

abbrev basicOpStepMulmodOfStack :=
  @Yul.Reference.BridgeFacts.basicOp_step_mulmod_of_stack

abbrev basicOpStepExpOfStack :=
  @Yul.Reference.BridgeFacts.basicOp_step_exp_of_stack

abbrev basicOpStepSignextendOfStack :=
  @Yul.Reference.BridgeFacts.basicOp_step_signextend_of_stack

abbrev basicOpStepLtOfStack :=
  @Yul.Reference.BridgeFacts.basicOp_step_lt_of_stack

abbrev basicOpStepGtOfStack :=
  @Yul.Reference.BridgeFacts.basicOp_step_gt_of_stack

abbrev basicOpStepSltOfStack :=
  @Yul.Reference.BridgeFacts.basicOp_step_slt_of_stack

abbrev basicOpStepSgtOfStack :=
  @Yul.Reference.BridgeFacts.basicOp_step_sgt_of_stack

abbrev basicOpStepEqOfStack :=
  @Yul.Reference.BridgeFacts.basicOp_step_eq_of_stack

abbrev basicOpStepAndOfStack :=
  @Yul.Reference.BridgeFacts.basicOp_step_and_of_stack

abbrev basicOpStepOrOfStack :=
  @Yul.Reference.BridgeFacts.basicOp_step_or_of_stack

abbrev basicOpStepXorOfStack :=
  @Yul.Reference.BridgeFacts.basicOp_step_xor_of_stack

abbrev basicOpStepByteOfStack :=
  @Yul.Reference.BridgeFacts.basicOp_step_byte_of_stack

abbrev basicOpStepShlOfStack :=
  @Yul.Reference.BridgeFacts.basicOp_step_shl_of_stack

abbrev basicOpStepShrOfStack :=
  @Yul.Reference.BridgeFacts.basicOp_step_shr_of_stack

abbrev basicOpStepSarOfStack :=
  @Yul.Reference.BridgeFacts.basicOp_step_sar_of_stack

abbrev basicOpStepAddressOfStack :=
  @Yul.Reference.BridgeFacts.basicOp_step_address_of_stack

abbrev exprValueBridgeWithLayoutSlotsIszero :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_iszero

abbrev exprValueBridgeWithLayoutSlotsPreservingBaseIszero :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlotsPreservingBase_iszero

abbrev exprValueBridgeWithLayoutSlotsNot :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_not

abbrev exprValueBridgeWithLayoutSlotsPreservingBaseNot :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlotsPreservingBase_not

abbrev twoHiddenArgsBridgeWithLayoutSlots :=
  @Yul.Reference.BridgeFacts.TwoHiddenArgsBridgeWithLayoutSlots

abbrev layoutSlotValue :=
  @Yul.Reference.LayoutSlotValue

abbrev layoutSlotValueTop :=
  @Yul.Reference.BridgeFacts.LayoutSlotValue.top

abbrev layoutSlotValueCons :=
  @Yul.Reference.BridgeFacts.LayoutSlotValue.cons

abbrev layoutSlotValuePrefix :=
  @Yul.Reference.BridgeFacts.LayoutSlotValue.prefix_hidden

abbrev twoHiddenArgsBridgeWithLayoutSlotValues :=
  @Yul.Reference.BridgeFacts.TwoHiddenArgsBridgeWithLayoutSlotValues

abbrev twoHiddenArgsPreludeBridgeWithLayoutSlotValues :=
  @Yul.Reference.BridgeFacts.TwoHiddenArgsPreludeBridgeWithLayoutSlotValues

abbrev twoHiddenArgsBridgeWithLayoutSlotsToSlotValues :=
  @Yul.Reference.BridgeFacts.TwoHiddenArgsBridgeWithLayoutSlots.toSlotValues

abbrev twoHiddenArgsBridgeWithLayoutSlotValuesOfPrelude :=
  @Yul.Reference.BridgeFacts.twoHiddenArgsBridgeWithLayoutSlotValues_of_prelude

abbrev layoutSuffixConsHidden :=
  @Yul.Reference.BridgeFacts.LayoutSuffix.cons_hidden

abbrev singleTempAsHiddenLayoutSlot :=
  @Yul.Reference.BridgeFacts.CompilerStateRelWithTempsAndLayoutSlots.single_as_hidden

abbrev exprValueBridgeWithLayoutSlotsBindHidden :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_bind_hidden

abbrev exprValueBridgeWithLayoutSlotsPreservingBaseBindHidden :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlotsPreservingBase_bind_hidden

abbrev boundArgsBridgeWithLayoutSlotValues :=
  @Yul.Reference.BridgeFacts.BoundArgsBridgeWithLayoutSlotValues

abbrev lowerArgSlotValue :=
  @Yul.ArgSlots.LayoutSlotValue

abbrev lowerArgSlotValues :=
  @Yul.ArgSlots.Values

abbrev lowerArgSlotValuesRunCodeToStackSeq :=
  @Yul.ArgSlots.Values.runCode_toStackSeq

abbrev argSlotValuesLengthEq :=
  @Yul.Reference.BridgeFacts.ArgSlotValues.length_eq

abbrev argSlotValuesAllVars :=
  @Yul.Reference.BridgeFacts.ArgSlotValues.all_vars

abbrev argSlotValuesSingleton :=
  @Yul.Reference.BridgeFacts.ArgSlotValues.singleton

abbrev argSlotValuesAppend :=
  @Yul.Reference.BridgeFacts.ArgSlotValues.append

abbrev argSlotValuesReverse :=
  @Yul.Reference.BridgeFacts.ArgSlotValues.reverse

abbrev argSlotValuesToLower :=
  @Yul.Reference.BridgeFacts.ArgSlotValues.toArgSlots

abbrev boundArgsBridgeWithLayoutSlotValuesNil :=
  @Yul.Reference.BridgeFacts.boundArgsBridgeWithLayoutSlotValues_nil

abbrev boundArgsBridgeWithLayoutSlotValuesConsComponents :=
  @Yul.Reference.BridgeFacts.boundArgsBridgeWithLayoutSlotValues_cons_components

abbrev boundArgsBridgeWithLayoutSlotValuesConsScheduled :=
  @Yul.Reference.BridgeFacts.boundArgsBridgeWithLayoutSlotValues_cons_scheduled

abbrev boundArgsBridgeWithLayoutSlotValuesSingleOfPreservingBase :=
  @Yul.Reference.BridgeFacts.boundArgsBridgeWithLayoutSlotValues_single_of_preserving_base

abbrev boundArgsBridgeWithLayoutSlotValuesTwoToLegacy :=
  @Yul.Reference.BridgeFacts.boundArgsBridgeWithLayoutSlotValues_two_to_legacy

abbrev boundArgsBridgeWithLayoutSlotValuesOfTwoPrelude :=
  @Yul.Reference.BridgeFacts.boundArgsBridgeWithLayoutSlotValues_of_two_prelude

abbrev twoHiddenArgsPreludeBridgeWithLayoutSlotValuesLitLit :=
  @Yul.Reference.BridgeFacts.twoHiddenArgsPreludeBridgeWithLayoutSlotValues_lit_lit

abbrev boundArgsBridgeWithLayoutSlotValuesLit :=
  @Yul.Reference.BridgeFacts.boundArgsBridgeWithLayoutSlotValues_lit

abbrev boundArgsBridgeWithLayoutSlotValuesLitLit :=
  @Yul.Reference.BridgeFacts.boundArgsBridgeWithLayoutSlotValues_lit_lit

abbrev generatedSingletonArgStackBound :=
  @Yul.Reference.BridgeFacts.generatedSingletonArgStackBound

abbrev generatedPairArgStackBound :=
  @Yul.Reference.BridgeFacts.generatedPairArgStackBound

abbrev resultSeqRunBridgeWithLayoutSlotsConsReturnLitLitGeneratedPrelude :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_return_lit_lit_generated_prelude

abbrev resultSeqRunBridgeWithLayoutSlotsConsRevertLitLitGeneratedPrelude :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_revert_lit_lit_generated_prelude

abbrev resultSeqRunBridgeWithLayoutSlotsConsSelfdestructLitGeneratedPrelude :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_selfdestruct_lit_generated_prelude

abbrev resultSeqRunBridgeWithLayoutSlotsConsReturnLitLitGeneratedOfLower :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_return_lit_lit_generated_of_lower

abbrev resultSeqRunBridgeWithLayoutSlotsConsRevertLitLitGeneratedOfLower :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_revert_lit_lit_generated_of_lower

abbrev resultSeqRunBridgeWithLayoutSlotsConsSelfdestructLitGeneratedOfLower :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_selfdestruct_lit_generated_of_lower

abbrev boundArgsBridgeWithLayoutSlotValuesRunStackSeq :=
  @Yul.Reference.BridgeFacts.boundArgsBridgeWithLayoutSlotValues_runStackSeq

abbrev resultSeqRunBridgeWithLayoutSlotsConsBoundTerminalArgsOfSourceError :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_boundTerminalArgs_of_source_error

abbrev resultSeqRunBridgeWithLayoutSlotsConsReturnLitLitBoundBridge :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_return_lit_lit_bound_bridge

abbrev resultSeqRunBridgeWithLayoutSlotsConsRevertLitLitBoundBridge :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_revert_lit_lit_bound_bridge

abbrev resultSeqRunBridgeWithLayoutSlotsConsSelfdestructLitBoundBridge :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_selfdestruct_lit_bound_bridge

abbrev resultSeqRunBridgeWithLayoutSlotsConsReturnLitLitBoundOfLower :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_return_lit_lit_bound_of_lower

abbrev resultSeqRunBridgeWithLayoutSlotsConsRevertLitLitBoundOfLower :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_revert_lit_lit_bound_of_lower

abbrev resultSeqRunBridgeWithLayoutSlotsConsSelfdestructLitBoundOfLower :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_selfdestruct_lit_bound_of_lower

abbrev exprValueBridgeWithLayoutSlotsUnaryHiddenOfTarget :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_unary_hidden_of_target

abbrev runCodeTopVar :=
  @Yul.Reference.BridgeFacts.runCode_top_var

abbrev runCodeVarLayoutSlotValue :=
  @Locals.Direct.Expr.runCode_var_layout_slot_value

abbrev exprSeqRunCodeOfVarSlotValuesAt :=
  @Locals.Direct.Expr.ExprSeq.runCode_of_varSlotValuesAt

abbrev varSlotValuesAtSeqCast :=
  @Yul.Reference.BridgeFacts.varSlotValuesAt_seqCast

abbrev argSlotValuesToVarSlotValuesAtOfToSeq :=
  @Yul.Reference.BridgeFacts.ArgSlotValues.toVarSlotValuesAt_of_toSeq?

abbrev exprSeqRunCodeToStackSeqOfArgSlots :=
  @Yul.Reference.BridgeFacts.exprSeq_runCode_toStackSeq_of_argSlots

abbrev exprSeqRunCodeTwoLayoutSlots :=
  @Yul.Reference.BridgeFacts.exprSeq_runCode_two_layout_slots

abbrev exprSeqRunCodeTopTwoHiddenVars :=
  @Yul.Reference.BridgeFacts.exprSeq_runCode_top_two_hidden_vars

abbrev exprValueBridgeWithLayoutSlotsIszeroHidden :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_iszero_hidden

abbrev exprValueBridgeWithLayoutSlotsIszeroOfBoundLowering :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_iszero_of_bound_lowering

abbrev exprValueBridgeWithLayoutSlotsNotHidden :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_not_hidden

abbrev exprValueBridgeWithLayoutSlotsNotOfBoundLowering :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_not_of_bound_lowering

abbrev exprValueBridgeWithLayoutSlotsAddHiddenOfArgs :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_add_hidden_of_args

abbrev exprValueBridgeWithLayoutSlotsAddHiddenOfSlotArgs :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_add_hidden_of_slot_args

abbrev exprValueBridgeWithLayoutSlotsBinaryOfBoundArgsTarget :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_binary_of_bound_args_target

abbrev exprValueBridgeWithLayoutSlotsBinaryPrimOfBoundArgs :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_binary_prim_of_bound_args

abbrev exprValueBridgeWithLayoutSlotsTernaryPrimOfBoundArgs :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_ternary_prim_of_bound_args

abbrev exprValueBridgeWithLayoutSlotsNullaryPrim :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_nullary_prim

abbrev exprValueBridgeWithLayoutSlotsNullaryExecutionEnv :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_nullary_executionEnv

abbrev exprValueBridgeWithLayoutSlotsAddress :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_address

abbrev sharedStateRelBalance :=
  @Yul.Reference.SharedStateRel.balance

abbrev sharedStateRelSload :=
  @Yul.Reference.SharedStateRel.sload

abbrev sharedStateRelSstore :=
  @Yul.Reference.SharedStateRel.sstore

abbrev sharedStateRelTload :=
  @Yul.Reference.SharedStateRel.tload

abbrev sharedStateRelTstore :=
  @Yul.Reference.SharedStateRel.tstore

abbrev sharedStateRelLogOp :=
  @Yul.Reference.SharedStateRel.logOp

abbrev machineStateRelMloadValue :=
  @Yul.Reference.MachineStateRel.mload_value

abbrev machineStateRelMload :=
  @Yul.Reference.MachineStateRel.mload

abbrev machineStateRelMstore :=
  @Yul.Reference.MachineStateRel.mstore

abbrev machineStateRelMstore8 :=
  @Yul.Reference.MachineStateRel.mstore8

abbrev machineStateRelMcopy :=
  @Yul.Reference.MachineStateRel.mcopy

abbrev machineStateRelReturndatacopy :=
  @Yul.Reference.MachineStateRel.returndatacopy

abbrev machineStateRelKeccak256Value :=
  @Yul.Reference.MachineStateRel.keccak256_value

abbrev machineStateRelKeccak256 :=
  @Yul.Reference.MachineStateRel.keccak256

abbrev sharedStateRelMload :=
  @Yul.Reference.SharedStateRel.mload

abbrev sharedStateRelMstore :=
  @Yul.Reference.SharedStateRel.mstore

abbrev sharedStateRelMstore8 :=
  @Yul.Reference.SharedStateRel.mstore8

abbrev sharedStateRelMcopy :=
  @Yul.Reference.SharedStateRel.mcopy

abbrev sharedStateRelReturndatacopy :=
  @Yul.Reference.SharedStateRel.returndatacopy

abbrev sharedStateRelCalldatacopy :=
  @Yul.Reference.SharedStateRel.calldatacopy

abbrev sharedStateRelKeccak256 :=
  @Yul.Reference.SharedStateRel.keccak256

abbrev exprValueBridgeWithLayoutSlotsBalanceHidden :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_balance_hidden

abbrev exprValueBridgeWithLayoutSlotsBalanceOfBoundLowering :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_balance_of_bound_lowering

abbrev exprValueBridgeWithLayoutSlotsSloadHidden :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_sload_hidden

abbrev exprValueBridgeWithLayoutSlotsSloadOfBoundLowering :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_sload_of_bound_lowering

abbrev exprValueBridgeWithLayoutSlotsTloadHidden :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_tload_hidden

abbrev exprValueBridgeWithLayoutSlotsTloadOfBoundLowering :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_tload_of_bound_lowering

abbrev exprValueBridgeWithLayoutSlotsMloadHidden :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_mload_hidden

abbrev exprValueBridgeWithLayoutSlotsMloadOfBoundLowering :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_mload_of_bound_lowering

abbrev exprValueBridgeWithLayoutSlotsKeccak256OfBoundArgsBinary :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_keccak256_of_bound_args_binary

abbrev exprValueBridgeWithLayoutSlotsKeccak256OfBoundLowering :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_keccak256_of_bound_lowering

abbrev regularPrefixWithLayoutSlotsBinaryZeroPrimOfBoundArgsTarget :=
  @Yul.Reference.BridgeFacts.regularPrefixWithLayoutSlots_binary_zero_prim_of_bound_args_target

abbrev regularPrefixWithLayoutSlotsUnaryZeroPrimOfBoundArgsTarget :=
  @Yul.Reference.BridgeFacts.regularPrefixWithLayoutSlots_unary_zero_prim_of_bound_args_target

abbrev regularPrefixWithLayoutSlotsPopOfBoundArgsUnary :=
  @Yul.Reference.BridgeFacts.regularPrefixWithLayoutSlots_pop_of_bound_args_unary

abbrev regularPrefixWithLayoutSlotsTernaryZeroPrimOfBoundArgsTarget :=
  @Yul.Reference.BridgeFacts.regularPrefixWithLayoutSlots_ternary_zero_prim_of_bound_args_target

abbrev regularPrefixWithLayoutSlotsCalldatacopyOfBoundArgsTernary :=
  @Yul.Reference.BridgeFacts.regularPrefixWithLayoutSlots_calldatacopy_of_bound_args_ternary

abbrev regularPrefixWithLayoutSlotsReturndatacopyOfBoundArgsTernary :=
  @Yul.Reference.BridgeFacts.regularPrefixWithLayoutSlots_returndatacopy_of_bound_args_ternary

abbrev regularPrefixWithLayoutSlotsMcopyOfBoundArgsTernary :=
  @Yul.Reference.BridgeFacts.regularPrefixWithLayoutSlots_mcopy_of_bound_args_ternary

abbrev regularPrefixWithLayoutSlotsMstoreOfBoundArgsBinary :=
  @Yul.Reference.BridgeFacts.regularPrefixWithLayoutSlots_mstore_of_bound_args_binary

abbrev regularPrefixWithLayoutSlotsSstoreOfBoundArgsBinary :=
  @Yul.Reference.BridgeFacts.regularPrefixWithLayoutSlots_sstore_of_bound_args_binary

abbrev regularPrefixWithLayoutSlotsTstoreOfBoundArgsBinary :=
  @Yul.Reference.BridgeFacts.regularPrefixWithLayoutSlots_tstore_of_bound_args_binary

abbrev regularPrefixWithLayoutSlotsLog0OfBoundArgsBinary :=
  @Yul.Reference.BridgeFacts.regularPrefixWithLayoutSlots_log0_of_bound_args_binary

abbrev regularPrefixWithLayoutSlotsLog1OfBoundArgsTernary :=
  @Yul.Reference.BridgeFacts.regularPrefixWithLayoutSlots_log1_of_bound_args_ternary

abbrev regularPrefixWithLayoutSlotsMstore8OfBoundArgsBinary :=
  @Yul.Reference.BridgeFacts.regularPrefixWithLayoutSlots_mstore8_of_bound_args_binary

abbrev exprValueBridgeWithLayoutSlotsOrigin :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_origin

abbrev exprValueBridgeWithLayoutSlotsCaller :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_caller

abbrev exprValueBridgeWithLayoutSlotsCallvalue :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_callvalue

abbrev exprValueBridgeWithLayoutSlotsCalldatasize :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_calldatasize

abbrev exprValueBridgeWithLayoutSlotsUnaryStateSameHidden :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_unary_state_same_hidden

abbrev exprValueBridgeWithLayoutSlotsCalldataloadHidden :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_calldataload_hidden

abbrev exprValueBridgeWithLayoutSlotsCalldataloadOfBoundLowering :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_calldataload_of_bound_lowering

abbrev exprValueBridgeWithLayoutSlotsBlockhashHidden :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_blockhash_hidden

abbrev exprValueBridgeWithLayoutSlotsBlockhashOfBoundLowering :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_blockhash_of_bound_lowering

abbrev exprValueBridgeWithLayoutSlotsBlobhashHidden :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_blobhash_hidden

abbrev exprValueBridgeWithLayoutSlotsBlobhashOfBoundLowering :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_blobhash_of_bound_lowering

abbrev exprValueBridgeWithLayoutSlotsGasprice :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_gasprice

abbrev exprValueBridgeWithLayoutSlotsPrevrandao :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_prevrandao

abbrev exprValueBridgeWithLayoutSlotsBasefee :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_basefee

abbrev exprValueBridgeWithLayoutSlotsBlobbasefee :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_blobbasefee

abbrev exprValueBridgeWithLayoutSlotsNullaryState :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_nullary_state

abbrev exprValueBridgeWithLayoutSlotsCoinbase :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_coinbase

abbrev exprValueBridgeWithLayoutSlotsTimestamp :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_timestamp

abbrev exprValueBridgeWithLayoutSlotsNumber :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_number

abbrev exprValueBridgeWithLayoutSlotsGaslimit :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_gaslimit

abbrev exprValueBridgeWithLayoutSlotsChainid :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_chainid

abbrev exprValueBridgeWithLayoutSlotsSelfbalance :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_selfbalance

abbrev exprValueBridgeWithLayoutSlotsNullaryMachineState :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_nullary_machineState

abbrev exprValueBridgeWithLayoutSlotsReturndatasize :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_returndatasize

abbrev exprValueBridgeWithLayoutSlotsMsize :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_msize

abbrev exprValueBridgeWithLayoutSlotsGas :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_gas

abbrev exprValueBridgeWithLayoutSlotsAddOfBoundArgs :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_add_of_bound_args

abbrev exprValueBridgeWithLayoutSlotsAddOfBoundArgsBinary :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_add_of_bound_args_binary

abbrev exprValueBridgeWithLayoutSlotsAddOfBoundLowering :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_add_of_bound_lowering

abbrev exprValueBridgeWithLayoutSlotsMulOfBoundArgsBinary :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_mul_of_bound_args_binary

abbrev exprValueBridgeWithLayoutSlotsMulOfBoundLowering :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_mul_of_bound_lowering

abbrev exprValueBridgeWithLayoutSlotsSubOfBoundArgs :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_sub_of_bound_args

abbrev exprValueBridgeWithLayoutSlotsSubOfBoundArgsBinary :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_sub_of_bound_args_binary

abbrev exprValueBridgeWithLayoutSlotsSubOfBoundLowering :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_sub_of_bound_lowering

abbrev exprValueBridgeWithLayoutSlotsDivOfBoundArgsBinary :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_div_of_bound_args_binary

abbrev exprValueBridgeWithLayoutSlotsDivOfBoundLowering :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_div_of_bound_lowering

abbrev exprValueBridgeWithLayoutSlotsSdivOfBoundArgsBinary :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_sdiv_of_bound_args_binary

abbrev exprValueBridgeWithLayoutSlotsSdivOfBoundLowering :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_sdiv_of_bound_lowering

abbrev exprValueBridgeWithLayoutSlotsModOfBoundArgsBinary :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_mod_of_bound_args_binary

abbrev exprValueBridgeWithLayoutSlotsModOfBoundLowering :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_mod_of_bound_lowering

abbrev exprValueBridgeWithLayoutSlotsSmodOfBoundArgsBinary :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_smod_of_bound_args_binary

abbrev exprValueBridgeWithLayoutSlotsSmodOfBoundLowering :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_smod_of_bound_lowering

abbrev exprValueBridgeWithLayoutSlotsAddmodOfBoundArgsTernary :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_addmod_of_bound_args_ternary

abbrev exprValueBridgeWithLayoutSlotsAddmodOfBoundLowering :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_addmod_of_bound_lowering

abbrev exprValueBridgeWithLayoutSlotsMulmodOfBoundArgsTernary :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_mulmod_of_bound_args_ternary

abbrev exprValueBridgeWithLayoutSlotsMulmodOfBoundLowering :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_mulmod_of_bound_lowering

abbrev exprValueBridgeWithLayoutSlotsExpOfBoundArgsBinary :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_exp_of_bound_args_binary

abbrev exprValueBridgeWithLayoutSlotsExpOfBoundLowering :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_exp_of_bound_lowering

abbrev exprValueBridgeWithLayoutSlotsSignextendOfBoundArgsBinary :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_signextend_of_bound_args_binary

abbrev exprValueBridgeWithLayoutSlotsSignextendOfBoundLowering :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_signextend_of_bound_lowering

abbrev exprValueBridgeWithLayoutSlotsEqOfBoundArgsBinary :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_eq_of_bound_args_binary

abbrev exprValueBridgeWithLayoutSlotsEqOfBoundLowering :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_eq_of_bound_lowering

abbrev exprValueBridgeWithLayoutSlotsLtOfBoundArgsBinary :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_lt_of_bound_args_binary

abbrev exprValueBridgeWithLayoutSlotsLtOfBoundLowering :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_lt_of_bound_lowering

abbrev exprValueBridgeWithLayoutSlotsGtOfBoundArgsBinary :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_gt_of_bound_args_binary

abbrev exprValueBridgeWithLayoutSlotsGtOfBoundLowering :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_gt_of_bound_lowering

abbrev exprValueBridgeWithLayoutSlotsSltOfBoundArgsBinary :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_slt_of_bound_args_binary

abbrev exprValueBridgeWithLayoutSlotsSltOfBoundLowering :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_slt_of_bound_lowering

abbrev exprValueBridgeWithLayoutSlotsSgtOfBoundArgsBinary :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_sgt_of_bound_args_binary

abbrev exprValueBridgeWithLayoutSlotsSgtOfBoundLowering :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_sgt_of_bound_lowering

abbrev exprValueBridgeWithLayoutSlotsAndOfBoundArgsBinary :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_and_of_bound_args_binary

abbrev exprValueBridgeWithLayoutSlotsAndOfBoundLowering :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_and_of_bound_lowering

abbrev exprValueBridgeWithLayoutSlotsOrOfBoundArgsBinary :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_or_of_bound_args_binary

abbrev exprValueBridgeWithLayoutSlotsOrOfBoundLowering :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_or_of_bound_lowering

abbrev exprValueBridgeWithLayoutSlotsXorOfBoundArgsBinary :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_xor_of_bound_args_binary

abbrev exprValueBridgeWithLayoutSlotsXorOfBoundLowering :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_xor_of_bound_lowering

abbrev exprValueBridgeWithLayoutSlotsByteOfBoundArgsBinary :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_byte_of_bound_args_binary

abbrev exprValueBridgeWithLayoutSlotsByteOfBoundLowering :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_byte_of_bound_lowering

abbrev exprValueBridgeWithLayoutSlotsShlOfBoundArgsBinary :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_shl_of_bound_args_binary

abbrev exprValueBridgeWithLayoutSlotsShlOfBoundLowering :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_shl_of_bound_lowering

abbrev exprValueBridgeWithLayoutSlotsShrOfBoundArgsBinary :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_shr_of_bound_args_binary

abbrev exprValueBridgeWithLayoutSlotsShrOfBoundLowering :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_shr_of_bound_lowering

abbrev exprValueBridgeWithLayoutSlotsSarOfBoundArgsBinary :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_sar_of_bound_args_binary

abbrev exprValueBridgeWithLayoutSlotsSarOfBoundLowering :=
  @Yul.Reference.BridgeFacts.exprValueBridgeWithLayoutSlots_sar_of_bound_lowering

abbrev lowerBlockNilToFunctions :=
  @Yul.Reference.BridgeFacts.toFunctionsListFuel?_block_nil

abbrev lowerBlockComponentsToFunctions :=
  @Yul.Reference.BridgeFacts.toFunctionsListFuel?_block_components

abbrev lowerIfComponentsToFunctions :=
  @Yul.Reference.BridgeFacts.toFunctionsListFuel?_if_components

abbrev lowerForComponentsToFunctions :=
  @Yul.Reference.BridgeFacts.toFunctionsListFuel?_for_components

abbrev lowerTerminalComponentsToFunctions :=
  @Yul.Reference.BridgeFacts.toFunctionsListFuel?_terminal_components

abbrev lowerListNilToFunctions :=
  @Yul.Reference.BridgeFacts.listToFunctionsFuel?_nil

abbrev lowerListConsComponentsToFunctions :=
  @Yul.Reference.BridgeFacts.listToFunctionsFuel?_cons_components

abbrev lowerBlockComponentsToBlock :=
  @Yul.Reference.BridgeFacts.listToBlockFuel?_components

abbrev lowerContinueToFunctions :=
  @Yul.Reference.BridgeFacts.toFunctionsListFuel?_continue

abbrev lowerBreakToFunctions :=
  @Yul.Reference.BridgeFacts.toFunctionsListFuel?_break

abbrev lowerLeaveToFunctions :=
  @Yul.Reference.BridgeFacts.toFunctionsListFuel?_leave

abbrev importedBlockConsOk :=
  @Yul.Reference.BridgeFacts.imported_block_cons_ok

abbrev functionsBlockConsRegular :=
  @Yul.Reference.BridgeFacts.functions_block_cons_regular

abbrev functionsBlockNilBridge :=
  @Yul.Reference.BridgeFacts.functions_block_nil_bridge

abbrev runCleanupToSelf :=
  @Yul.Reference.BridgeFacts.runCleanupTo_self

abbrev functionsForGuardBreakRunScoped :=
  @Yul.Reference.BridgeFacts.functions_for_guard_break_runScoped

abbrev functionsStmtBlockNilBridge :=
  @Yul.Reference.BridgeFacts.functions_stmt_block_nil_bridge

abbrev regularPrefixBlockNilBridge :=
  @Yul.Reference.BridgeFacts.regularPrefix_block_nil_bridge

abbrev functionsRunOpenAppendRegularExists :=
  @Functions.Direct.Block.runOpen_append_regular_exists

abbrev regularStmtPrefixBridgeExists :=
  @Yul.Reference.BridgeFacts.RegularStmtPrefixBridgeExists

abbrev regularStmtPrefixBridgeWithLayout :=
  @Yul.Reference.BridgeFacts.RegularStmtPrefixBridgeWithLayout

abbrev regularStmtPrefixBridgeWithHiddenLayout :=
  @Yul.Reference.BridgeFacts.RegularStmtPrefixBridgeWithHiddenLayout

abbrev regularStmtPrefixBridgeWithLayoutSlots :=
  @Yul.Reference.BridgeFacts.RegularStmtPrefixBridgeWithLayoutSlots

abbrev regularStmtPrefixBridgeExistsOfPrefix :=
  @Yul.Reference.BridgeFacts.regularStmtPrefixBridgeExists_of_prefix

abbrev regularStmtPrefixBridgeWithLayoutToExists :=
  @Yul.Reference.BridgeFacts.regularStmtPrefixBridgeWithLayout_to_exists

abbrev blockConsRegularBridge :=
  @Yul.Reference.BridgeFacts.block_cons_regular_bridge

abbrev regularStmtPrefixBlockCons :=
  @Yul.Reference.BridgeFacts.regularStmtPrefix_block_cons

abbrev regularBlockRunBridgeNil :=
  @Yul.Reference.BridgeFacts.regularBlockRunBridge_nil

abbrev regularBlockRunBridgeConsOfPrefix :=
  @Yul.Reference.BridgeFacts.regularBlockRunBridge_cons_of_prefix

abbrev compilerOkOutcomeRel :=
  @Yul.Reference.BridgeFacts.CompilerOkOutcomeRel

abbrev compilerResultOutcomeRel :=
  @Yul.Reference.BridgeFacts.CompilerResultOutcomeRel

abbrev compilerOkOutcomeRelRestrictStoreToOfScopeContains :=
  @Yul.Reference.BridgeFacts.CompilerOkOutcomeRel.restrictStoreTo_of_scope_contains

abbrev compilerOkOutcomeRelRestrictStoreToOfDomainExact :=
  @Yul.Reference.BridgeFacts.CompilerOkOutcomeRel.restrictStoreTo_of_domain_exact

abbrev compilerResultOutcomeRelRestrictStoreToOfScopeContains :=
  @Yul.Reference.BridgeFacts.CompilerResultOutcomeRel.restrictStoreTo_of_scope_contains

abbrev compilerResultOutcomeRelRestrictStoreToOfDomainExact :=
  @Yul.Reference.BridgeFacts.CompilerResultOutcomeRel.restrictStoreTo_of_domain_exact

abbrev compilerOkOutcomeRelModeNeRegularOfCheckpoint :=
  @Yul.Reference.BridgeFacts.CompilerOkOutcomeRel.mode_ne_regular_of_checkpoint

abbrev compilerResultOutcomeRelModeNeRegularOfCheckpoint :=
  @Yul.Reference.BridgeFacts.CompilerResultOutcomeRel.mode_ne_regular_of_checkpoint

abbrev compilerResultOutcomeRelModeNeRegularOfError :=
  @Yul.Reference.BridgeFacts.CompilerResultOutcomeRel.mode_ne_regular_of_error

abbrev compilerOkOutcomeRelWithLayoutSlotsModeNeRegularOfCheckpoint :=
  @Yul.Reference.BridgeFacts.CompilerOkOutcomeRelWithLayoutSlots.mode_ne_regular_of_checkpoint

abbrev compilerResultOutcomeRelWithLayoutSlotsModeNeRegularOfCheckpoint :=
  @Yul.Reference.BridgeFacts.CompilerResultOutcomeRelWithLayoutSlots.mode_ne_regular_of_checkpoint

abbrev compilerResultOutcomeRelWithLayoutSlotsModeNeRegularOfError :=
  @Yul.Reference.BridgeFacts.CompilerResultOutcomeRelWithLayoutSlots.mode_ne_regular_of_error

abbrev errorStmtPrefixBridge :=
  @Yul.Reference.BridgeFacts.ErrorStmtPrefixBridge

abbrev nonregularStmtPrefixBridge :=
  @Yul.Reference.BridgeFacts.NonregularStmtPrefixBridge

abbrev nonregularStmtPrefixOfErrorPrefix :=
  @Yul.Reference.BridgeFacts.nonregularStmtPrefix_of_errorPrefix

abbrev okBlockRunBridge :=
  @Yul.Reference.BridgeFacts.OkBlockRunBridge

abbrev someOkBlockRunBridge :=
  @Yul.Reference.BridgeFacts.SomeOkBlockRunBridge

abbrev resultBlockRunBridge :=
  @Yul.Reference.BridgeFacts.ResultBlockRunBridge

abbrev resultBlockRunBridgeWithLayoutSlots :=
  @Yul.Reference.BridgeFacts.ResultBlockRunBridgeWithLayoutSlots

abbrev someResultBlockRunBridge :=
  @Yul.Reference.BridgeFacts.SomeResultBlockRunBridge

abbrev nonregularBlockRunBridge :=
  @Yul.Reference.BridgeFacts.NonregularBlockRunBridge

abbrev nonregularBlockRunBridgeWithLayoutSlots :=
  @Yul.Reference.BridgeFacts.NonregularBlockRunBridgeWithLayoutSlots

abbrev okBlockRunBridgeOfRegular :=
  @Yul.Reference.BridgeFacts.okBlockRunBridge_of_regular

abbrev someOkBlockRunBridgeOfOk :=
  @Yul.Reference.BridgeFacts.someOkBlockRunBridge_of_ok

abbrev resultBlockRunBridgeOfOk :=
  @Yul.Reference.BridgeFacts.resultBlockRunBridge_of_ok

abbrev someResultBlockRunBridgeOfOk :=
  @Yul.Reference.BridgeFacts.someResultBlockRunBridge_of_ok

abbrev someResultBlockRunBridgeOfSomeOk :=
  @Yul.Reference.BridgeFacts.someResultBlockRunBridge_of_someOk

abbrev nonregularBlockRunBridgeOfResultBlockRunBridgeCheckpoint :=
  @Yul.Reference.BridgeFacts.nonregularBlockRunBridge_of_resultBlockRunBridge_checkpoint

abbrev nonregularBlockRunBridgeOfResultBlockRunBridgeError :=
  @Yul.Reference.BridgeFacts.nonregularBlockRunBridge_of_resultBlockRunBridge_error

abbrev nonregularBlockRunBridgeOfResultSeqRunBridgeWithLayoutCheckpoint :=
  @Yul.Reference.BridgeFacts.nonregularBlockRunBridge_of_resultSeqRunBridgeWithLayout_checkpoint

abbrev nonregularBlockRunBridgeOfResultSeqRunBridgeWithLayoutError :=
  @Yul.Reference.BridgeFacts.nonregularBlockRunBridge_of_resultSeqRunBridgeWithLayout_error

abbrev resultBlockRunBridgeWithLayoutSlotsOfResultSeqRunBridgeWithLayoutSlotsRestrict :=
  @Yul.Reference.BridgeFacts.resultBlockRunBridgeWithLayoutSlots_of_resultSeqRunBridgeWithLayoutSlots_restrict

abbrev nonregularBlockRunBridgeWithLayoutSlotsOfResultSeqRunBridgeWithLayoutSlotsCheckpoint :=
  @Yul.Reference.BridgeFacts.nonregularBlockRunBridgeWithLayoutSlots_of_resultSeqRunBridgeWithLayoutSlots_checkpoint

abbrev nonregularBlockRunBridgeWithLayoutSlotsOfResultSeqRunBridgeWithLayoutSlotsError :=
  @Yul.Reference.BridgeFacts.nonregularBlockRunBridgeWithLayoutSlots_of_resultSeqRunBridgeWithLayoutSlots_error

abbrev nonregularStmtPrefixBlockOfNonregularBlockRunBridge :=
  @Yul.Reference.BridgeFacts.nonregularStmtPrefix_block_of_nonregularBlockRunBridge

abbrev nonregularBlockRunBridgeRunScoped :=
  @Yul.Reference.BridgeFacts.nonregularBlockRunBridge_runScoped

abbrev nonregularBlockRunBridgeWithLayoutSlotsRunScoped :=
  @Yul.Reference.BridgeFacts.nonregularBlockRunBridgeWithLayoutSlots_runScoped

abbrev nonregularBlockRunBridgeFunctionsProgramRun :=
  @Yul.Reference.BridgeFacts.nonregularBlockRunBridge_functionsProgram_run

abbrev nonregularBlockRunBridgeLoweredRun :=
  @Yul.Reference.BridgeFacts.nonregularBlockRunBridge_lowered_run

abbrev okBlockRunBridgeConsOfRegularPrefix :=
  @Yul.Reference.BridgeFacts.okBlockRunBridge_cons_of_regular_prefix

abbrev someOkBlockRunBridgeConsOfRegularPrefix :=
  @Yul.Reference.BridgeFacts.someOkBlockRunBridge_cons_of_regular_prefix

abbrev resultSeqRunBridgeConsOfRegularPrefix :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridge_cons_of_regular_prefix

abbrev someResultSeqRunBridgeConsOfRegularPrefix :=
  @Yul.Reference.BridgeFacts.someResultSeqRunBridge_cons_of_regular_prefix

abbrev resultSeqRunBridgeConsOfRegularPrefixExists :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridge_cons_of_regular_prefix_exists

abbrev someResultSeqRunBridgeConsOfRegularPrefixExists :=
  @Yul.Reference.BridgeFacts.someResultSeqRunBridge_cons_of_regular_prefix_exists

abbrev resultSeqRunBridgeConsOfNonregularPrefix :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridge_cons_of_nonregular_prefix

abbrev someResultSeqRunBridgeConsOfNonregularPrefix :=
  @Yul.Reference.BridgeFacts.someResultSeqRunBridge_cons_of_nonregular_prefix

abbrev regularSeqRunBridge :=
  @Yul.Reference.BridgeFacts.RegularSeqRunBridge

abbrev layoutSuffix :=
  @Yul.Reference.BridgeFacts.LayoutSuffix

abbrev regularSeqRunBridgeWithLayout :=
  @Yul.Reference.BridgeFacts.RegularSeqRunBridgeWithLayout

abbrev regularSeqRunBridgeWithLayoutSlots :=
  @Yul.Reference.BridgeFacts.RegularSeqRunBridgeWithLayoutSlots

abbrev regularSeqRunBridgeWithLayoutSlotsNil :=
  @Yul.Reference.BridgeFacts.regularSeqRunBridgeWithLayoutSlots_nil

abbrev okSeqRunBridge :=
  @Yul.Reference.BridgeFacts.OkSeqRunBridge

abbrev someOkSeqRunBridge :=
  @Yul.Reference.BridgeFacts.SomeOkSeqRunBridge

abbrev resultSeqRunBridge :=
  @Yul.Reference.BridgeFacts.ResultSeqRunBridge

abbrev resultSeqRunBridgeWithLayout :=
  @Yul.Reference.BridgeFacts.ResultSeqRunBridgeWithLayout

abbrev resultSeqRunBridgeWithLayoutSlots :=
  @Yul.Reference.BridgeFacts.ResultSeqRunBridgeWithLayoutSlots

abbrev someResultSeqRunBridge :=
  @Yul.Reference.BridgeFacts.SomeResultSeqRunBridge

abbrev regularSeqRunBridgeNil :=
  @Yul.Reference.BridgeFacts.regularSeqRunBridge_nil

abbrev regularSeqRunBridgeWithLayoutToRegular :=
  @Yul.Reference.BridgeFacts.regularSeqRunBridgeWithLayout_to_regular

abbrev regularSeqRunBridgeWithLayoutNil :=
  @Yul.Reference.BridgeFacts.regularSeqRunBridgeWithLayout_nil

abbrev okSeqRunBridgeNil :=
  @Yul.Reference.BridgeFacts.okSeqRunBridge_nil

abbrev someOkSeqRunBridgeNil :=
  @Yul.Reference.BridgeFacts.someOkSeqRunBridge_nil

abbrev resultSeqRunBridgeNil :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridge_nil

abbrev someResultSeqRunBridgeNil :=
  @Yul.Reference.BridgeFacts.someResultSeqRunBridge_nil

abbrev resultSeqRunBridgeWithLayoutNil :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayout_nil

abbrev resultSeqRunBridgeWithLayoutSlotsNil :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_nil

abbrev regularSeqRunBridgeWithLayoutSlotsRunScoped :=
  @Yul.Reference.BridgeFacts.regularSeqRunBridgeWithLayoutSlots_runScoped

abbrev regularPrefixWithLayoutSlotsBlockOfSeqWithLayoutSlots :=
  @Yul.Reference.BridgeFacts.regularPrefixWithLayoutSlots_block_of_seq_with_layout_slots

abbrev resultBlockRunBridgeOfResultSeqRunBridgeRestrict :=
  @Yul.Reference.BridgeFacts.resultBlockRunBridge_of_resultSeqRunBridge_restrict

abbrev someResultBlockRunBridgeOfResultSeqRunBridgeRestrict :=
  @Yul.Reference.BridgeFacts.someResultBlockRunBridge_of_resultSeqRunBridge_restrict

abbrev resultSeqRunBridgeOfOk :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridge_of_ok

abbrev resultSeqRunBridgeOfWithLayout :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridge_of_withLayout

abbrev resultSeqRunBridgeWithLayoutOfRegular :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayout_of_regular

abbrev regularSeqRunBridgeWithLayoutOfResultSeqRunBridgeWithLayoutOk :=
  @Yul.Reference.BridgeFacts.regularSeqRunBridgeWithLayout_of_resultSeqRunBridgeWithLayout_ok

abbrev someResultSeqRunBridgeOfWithLayout :=
  @Yul.Reference.BridgeFacts.someResultSeqRunBridge_of_withLayout

abbrev someResultSeqRunBridgeOfOk :=
  @Yul.Reference.BridgeFacts.someResultSeqRunBridge_of_ok

abbrev someResultSeqRunBridgeOfSomeOk :=
  @Yul.Reference.BridgeFacts.someResultSeqRunBridge_of_someOk

abbrev resultSeqRunBridgeConsOfErrorPrefix :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridge_cons_of_error_prefix

abbrev someResultSeqRunBridgeConsOfErrorPrefix :=
  @Yul.Reference.BridgeFacts.someResultSeqRunBridge_cons_of_error_prefix

abbrev errorPrefixStopBridge :=
  @Yul.Reference.BridgeFacts.errorPrefix_stop_bridge

abbrev zeroZeroReturnArgs :=
  @Yul.Reference.BridgeFacts.zeroZeroReturnArgs

abbrev zeroZeroRevertArgs :=
  @Yul.Reference.BridgeFacts.zeroZeroRevertArgs

abbrev returnZeroZeroSourceState :=
  @Yul.Reference.BridgeFacts.returnZeroZeroSourceState

abbrev revertZeroZeroSourceState :=
  @Yul.Reference.BridgeFacts.revertZeroZeroSourceState

abbrev returnZeroZeroTargetState :=
  @Yul.Reference.BridgeFacts.returnZeroZeroTargetState

abbrev revertZeroZeroTargetState :=
  @Yul.Reference.BridgeFacts.revertZeroZeroTargetState

abbrev zeroSelfdestructArgs :=
  @Yul.Reference.BridgeFacts.zeroSelfdestructArgs

abbrev literalPairArgs :=
  @Yul.Reference.BridgeFacts.literalPairArgs

abbrev toStackSeqLiteralPairArgs :=
  @Yul.Reference.BridgeFacts.toStackSeq_literalPairArgs

abbrev zeroSelfdestructArgTargetState :=
  @Yul.Reference.BridgeFacts.zeroSelfdestructArgTargetState

abbrev literalPairArgsTargetState :=
  @Yul.Reference.BridgeFacts.literalPairArgsTargetState

abbrev terminalStepReturnZeroZero :=
  @Yul.Reference.BridgeFacts.terminal_step_return_zero_zero

abbrev terminalStepRevertZeroZero :=
  @Yul.Reference.BridgeFacts.terminal_step_revert_zero_zero

abbrev terminalStepReturnOfStack :=
  @Yul.Reference.BridgeFacts.terminal_step_return_of_stack

abbrev terminalStepRevertOfStack :=
  @Yul.Reference.BridgeFacts.terminal_step_revert_of_stack

abbrev terminalStepReturnLiteralPairArgsTargetState :=
  @Yul.Reference.BridgeFacts.terminal_step_return_literalPairArgsTargetState

abbrev terminalStepRevertLiteralPairArgsTargetState :=
  @Yul.Reference.BridgeFacts.terminal_step_revert_literalPairArgsTargetState

abbrev exprSeqRunCodeLiteralPairArgs :=
  @Yul.Reference.BridgeFacts.exprSeq_runCode_literalPairArgs

abbrev exprSeqRunCodeZeroSelfdestructArgs :=
  @Yul.Reference.BridgeFacts.exprSeq_runCode_zeroSelfdestructArgs

abbrev functionsRunOpenTerminalArgsReturnZeroZero :=
  @Yul.Reference.BridgeFacts.functions_runOpen_terminalArgs_return_zero_zero

abbrev functionsRunOpenTerminalArgsRevertZeroZero :=
  @Yul.Reference.BridgeFacts.functions_runOpen_terminalArgs_revert_zero_zero

abbrev functionsRunOpenTerminalArgsReturnLitLit :=
  @Yul.Reference.BridgeFacts.functions_runOpen_terminalArgs_return_lit_lit

abbrev functionsRunOpenTerminalArgsRevertLitLit :=
  @Yul.Reference.BridgeFacts.functions_runOpen_terminalArgs_revert_lit_lit

abbrev errorPrefixReturnZeroZeroBridge :=
  @Yul.Reference.BridgeFacts.errorPrefix_return_zero_zero_bridge

abbrev errorPrefixRevertZeroZeroBridge :=
  @Yul.Reference.BridgeFacts.errorPrefix_revert_zero_zero_bridge

abbrev errorPrefixReturnLitLitBridge :=
  @Yul.Reference.BridgeFacts.errorPrefix_return_lit_lit_bridge

abbrev errorPrefixRevertLitLitBridge :=
  @Yul.Reference.BridgeFacts.errorPrefix_revert_lit_lit_bridge

abbrev errorPrefixSelfdestructZeroBridge :=
  @Yul.Reference.BridgeFacts.errorPrefix_selfdestruct_zero_bridge

abbrev resultSeqRunBridgeConsStopBridge :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridge_cons_stop_bridge

abbrev resultSeqRunBridgeConsReturnLitLitBridge :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridge_cons_return_lit_lit_bridge

abbrev resultSeqRunBridgeConsRevertLitLitBridge :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridge_cons_revert_lit_lit_bridge

abbrev resultSeqRunBridgeConsReturnZeroZeroBridge :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridge_cons_return_zero_zero_bridge

abbrev resultSeqRunBridgeConsRevertZeroZeroBridge :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridge_cons_revert_zero_zero_bridge

abbrev resultSeqRunBridgeConsSelfdestructZeroBridge :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridge_cons_selfdestruct_zero_bridge

abbrev someResultSeqRunBridgeConsStopBridge :=
  @Yul.Reference.BridgeFacts.someResultSeqRunBridge_cons_stop_bridge

abbrev resultSeqRunBridgeWithLayoutSlotsConsStopBridge :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_stop_bridge

abbrev resultSeqRunBridgeWithLayoutSlotsConsReturnLitLitBridge :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_return_lit_lit_bridge

abbrev resultSeqRunBridgeWithLayoutSlotsConsRevertLitLitBridge :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_revert_lit_lit_bridge

abbrev resultSeqRunBridgeWithLayoutSlotsConsReturnZeroZeroBridge :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_return_zero_zero_bridge

abbrev resultSeqRunBridgeWithLayoutSlotsConsRevertZeroZeroBridge :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_revert_zero_zero_bridge

abbrev resultSeqRunBridgeWithLayoutSlotsConsSelfdestructZeroBridge :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_selfdestruct_zero_bridge

abbrev someResultSeqRunBridgeConsReturnLitLitBridge :=
  @Yul.Reference.BridgeFacts.someResultSeqRunBridge_cons_return_lit_lit_bridge

abbrev someResultSeqRunBridgeConsRevertLitLitBridge :=
  @Yul.Reference.BridgeFacts.someResultSeqRunBridge_cons_revert_lit_lit_bridge

abbrev someResultSeqRunBridgeConsReturnZeroZeroBridge :=
  @Yul.Reference.BridgeFacts.someResultSeqRunBridge_cons_return_zero_zero_bridge

abbrev someResultSeqRunBridgeConsRevertZeroZeroBridge :=
  @Yul.Reference.BridgeFacts.someResultSeqRunBridge_cons_revert_zero_zero_bridge

abbrev someResultSeqRunBridgeConsSelfdestructZeroBridge :=
  @Yul.Reference.BridgeFacts.someResultSeqRunBridge_cons_selfdestruct_zero_bridge

abbrev regularSeqRunBridgeConsOfPrefix :=
  @Yul.Reference.BridgeFacts.regularSeqRunBridge_cons_of_prefix

abbrev regularSeqRunBridgeConsOfPrefixExists :=
  @Yul.Reference.BridgeFacts.regularSeqRunBridge_cons_of_prefix_exists

abbrev regularSeqRunBridgeWithLayoutConsOfPrefix :=
  @Yul.Reference.BridgeFacts.regularSeqRunBridgeWithLayout_cons_of_prefix

abbrev regularSeqRunBridgeWithLayoutSlotsConsOfRegularPrefix :=
  @Yul.Reference.BridgeFacts.regularSeqRunBridgeWithLayoutSlots_cons_of_regular_prefix

abbrev resultSeqRunBridgeWithLayoutConsOfRegularPrefix :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayout_cons_of_regular_prefix

abbrev resultSeqRunBridgeWithLayoutSlotsConsOfRegularPrefix :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_of_regular_prefix

abbrev regularSeqRunBridgeWithLayoutSlotsConsOfLowerRegularPrefix :=
  @Yul.Reference.BridgeFacts.regularSeqRunBridgeWithLayoutSlots_cons_of_lower_regular_prefix

abbrev resultSeqRunBridgeWithLayoutSlotsConsOfLowerRegularPrefix :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_of_lower_regular_prefix

abbrev resultSeqRunBridgeWithLayoutSlotsNilOfLower :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_nil_of_lower

abbrev regularSeqRunBridgeWithLayoutSlotsNilOfLower :=
  @Yul.Reference.BridgeFacts.regularSeqRunBridgeWithLayoutSlots_nil_of_lower

abbrev resultSeqRunBridgeWithLayoutSlotsOfBlockLower :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_of_block_lower

abbrev regularSeqRunBridgeWithLayoutSlotsOfBlockLower :=
  @Yul.Reference.BridgeFacts.regularSeqRunBridgeWithLayoutSlots_of_block_lower

abbrev resultSeqRunBridgeWithLayoutConsLetNoneChecked :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayout_cons_let_none_checked

abbrev resultSeqRunBridgeWithLayoutConsLetLiteralSingleChecked :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayout_cons_let_lit_single_checked

abbrev resultSeqRunBridgeWithLayoutConsLetVariableSingleChecked :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayout_cons_let_var_single_checked

abbrev resultSeqRunBridgeWithLayoutConsAssignLiteralSingleChecked :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayout_cons_assign_lit_single_checked

abbrev resultSeqRunBridgeWithLayoutConsAssignVariableSingleChecked :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayout_cons_assign_var_single_checked

abbrev regularPrefixWithLayoutSlotsAssignSingleOfExprBridge :=
  @Yul.Reference.BridgeFacts.regularPrefixWithLayoutSlots_assign_single_of_expr_bridge

abbrev resultSeqRunBridgeWithLayoutSlotsConsAssignSingleOfExprBridge :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_assign_single_of_expr_bridge

abbrev regularSeqRunBridgeWithLayoutSlotsConsAssignSingleOfExprBridge :=
  @Yul.Reference.BridgeFacts.regularSeqRunBridgeWithLayoutSlots_cons_assign_single_of_expr_bridge

abbrev resultSeqRunBridgeWithLayoutConsBlockChecked :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayout_cons_block_checked

abbrev regularSeqRunBridgeWithLayoutConsLetNoneChecked :=
  @Yul.Reference.BridgeFacts.regularSeqRunBridgeWithLayout_cons_let_none_checked

abbrev regularSeqRunBridgeWithLayoutConsLetLiteralSingleChecked :=
  @Yul.Reference.BridgeFacts.regularSeqRunBridgeWithLayout_cons_let_lit_single_checked

abbrev regularSeqRunBridgeWithLayoutConsLetVariableSingleChecked :=
  @Yul.Reference.BridgeFacts.regularSeqRunBridgeWithLayout_cons_let_var_single_checked

abbrev regularSeqRunBridgeWithLayoutConsAssignLiteralSingleChecked :=
  @Yul.Reference.BridgeFacts.regularSeqRunBridgeWithLayout_cons_assign_lit_single_checked

abbrev regularSeqRunBridgeWithLayoutConsAssignVariableSingleChecked :=
  @Yul.Reference.BridgeFacts.regularSeqRunBridgeWithLayout_cons_assign_var_single_checked

abbrev regularSeqRunBridgeWithLayoutConsBlockChecked :=
  @Yul.Reference.BridgeFacts.regularSeqRunBridgeWithLayout_cons_block_checked

abbrev regularPrefixWithLayoutIfFalseOfCondition :=
  @Yul.Reference.BridgeFacts.regularPrefixWithLayout_if_false_of_condition

abbrev regularPrefixWithHiddenLayoutIfFalseOfCondition :=
  @Yul.Reference.BridgeFacts.regularPrefixWithHiddenLayout_if_false_of_condition

abbrev regularPrefixWithLayoutSlotsIfFalseOfCondition :=
  @Yul.Reference.BridgeFacts.regularPrefixWithLayoutSlots_if_false_of_condition

abbrev resultSeqRunBridgeWithLayoutConsIfFalseChecked :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayout_cons_if_false_checked

abbrev regularPrefixWithLayoutIfTrueOfCondition :=
  @Yul.Reference.BridgeFacts.regularPrefixWithLayout_if_true_of_condition

abbrev regularPrefixWithHiddenLayoutIfTrueOfCondition :=
  @Yul.Reference.BridgeFacts.regularPrefixWithHiddenLayout_if_true_of_condition

abbrev regularPrefixWithLayoutSlotsIfTrueOfCondition :=
  @Yul.Reference.BridgeFacts.regularPrefixWithLayoutSlots_if_true_of_condition

abbrev resultSeqRunBridgeWithLayoutConsIfTrueRegularChecked :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayout_cons_if_true_regular_checked

abbrev resultSeqRunBridgeWithLayoutSlotsConsIfFalseChecked :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_if_false_checked

abbrev resultSeqRunBridgeWithLayoutSlotsConsIfTrueRegularChecked :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_if_true_regular_checked

abbrev regularSeqRunBridgeWithLayoutSlotsConsIfFalseChecked :=
  @Yul.Reference.BridgeFacts.regularSeqRunBridgeWithLayoutSlots_cons_if_false_checked

abbrev regularSeqRunBridgeWithLayoutSlotsConsIfTrueRegularChecked :=
  @Yul.Reference.BridgeFacts.regularSeqRunBridgeWithLayoutSlots_cons_if_true_regular_checked

abbrev resultSeqRunBridgeWithLayoutSlotsConsIfTrueNonregularChecked :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_if_true_nonregular_checked

abbrev resultSeqRunBridgeWithLayoutConsIfTrueNonregularChecked :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayout_cons_if_true_nonregular_checked

abbrev resultSeqRunBridgeWithLayoutConsIfLiteralFalseChecked :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayout_cons_if_lit_false_checked

abbrev resultSeqRunBridgeWithLayoutSlotsConsIfLiteralFalseChecked :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_if_lit_false_checked

abbrev resultSeqRunBridgeWithLayoutConsIfLiteralTrueRegularChecked :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayout_cons_if_lit_true_regular_checked

abbrev resultSeqRunBridgeWithLayoutConsIfLiteralTrueNonregularChecked :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayout_cons_if_lit_true_nonregular_checked

abbrev resultSeqRunBridgeWithLayoutSlotsConsIfLiteralTrueNonregularChecked :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_if_lit_true_nonregular_checked

abbrev resultSeqRunBridgeWithLayoutConsIfVariableFalseChecked :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayout_cons_if_var_false_checked

abbrev resultSeqRunBridgeWithLayoutSlotsConsIfVariableFalseChecked :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_if_var_false_checked

abbrev resultSeqRunBridgeWithLayoutConsIfVariableTrueRegularChecked :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayout_cons_if_var_true_regular_checked

abbrev resultSeqRunBridgeWithLayoutConsIfVariableTrueNonregularChecked :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayout_cons_if_var_true_nonregular_checked

abbrev resultSeqRunBridgeWithLayoutSlotsConsIfVariableTrueNonregularChecked :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_if_var_true_nonregular_checked

abbrev regularSeqRunBridgeWithLayoutSlotsConsIfLiteralFalseChecked :=
  @Yul.Reference.BridgeFacts.regularSeqRunBridgeWithLayoutSlots_cons_if_lit_false_checked

abbrev resultSeqRunBridgeWithLayoutSlotsConsIfLiteralFalseOfLower :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_if_lit_false_of_lower

abbrev regularSeqRunBridgeWithLayoutSlotsConsIfLiteralFalseOfLower :=
  @Yul.Reference.BridgeFacts.regularSeqRunBridgeWithLayoutSlots_cons_if_lit_false_of_lower

abbrev resultSeqRunBridgeWithLayoutSlotsConsIfLiteralTrueNonregularOfLower :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_if_lit_true_nonregular_of_lower

abbrev resultSeqRunBridgeWithLayoutSlotsConsIfLiteralTrueRegularOfLower :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_if_lit_true_regular_of_lower

abbrev regularSeqRunBridgeWithLayoutSlotsConsIfLiteralTrueRegularOfLower :=
  @Yul.Reference.BridgeFacts.regularSeqRunBridgeWithLayoutSlots_cons_if_lit_true_regular_of_lower

abbrev regularSeqRunBridgeWithLayoutSlotsConsIfLiteralTrueRegularChecked :=
  @Yul.Reference.BridgeFacts.regularSeqRunBridgeWithLayoutSlots_cons_if_lit_true_regular_checked

abbrev regularSeqRunBridgeWithLayoutSlotsConsIfVariableFalseChecked :=
  @Yul.Reference.BridgeFacts.regularSeqRunBridgeWithLayoutSlots_cons_if_var_false_checked

abbrev resultSeqRunBridgeWithLayoutSlotsConsIfVariableFalseOfLower :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_if_var_false_of_lower

abbrev regularSeqRunBridgeWithLayoutSlotsConsIfVariableFalseOfLower :=
  @Yul.Reference.BridgeFacts.regularSeqRunBridgeWithLayoutSlots_cons_if_var_false_of_lower

abbrev resultSeqRunBridgeWithLayoutSlotsConsIfVariableTrueNonregularOfLower :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_if_var_true_nonregular_of_lower

abbrev resultSeqRunBridgeWithLayoutSlotsConsIfVariableTrueRegularOfLower :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_if_var_true_regular_of_lower

abbrev regularSeqRunBridgeWithLayoutSlotsConsIfVariableTrueRegularOfLower :=
  @Yul.Reference.BridgeFacts.regularSeqRunBridgeWithLayoutSlots_cons_if_var_true_regular_of_lower

abbrev regularSeqRunBridgeWithLayoutSlotsConsIfVariableTrueRegularChecked :=
  @Yul.Reference.BridgeFacts.regularSeqRunBridgeWithLayoutSlots_cons_if_var_true_regular_checked

abbrev toFunctionsListFuelSwitchEmptyDefaultComponents :=
  @Yul.Reference.BridgeFacts.toFunctionsListFuel?_switch_empty_default_components

abbrev toFunctionsListFuelSwitchNonemptyDefaultComponents :=
  @Yul.Reference.BridgeFacts.toFunctionsListFuel?_switch_nonempty_default_components

abbrev selectSwitchCaseNilOfCaseListToFunctionsFuelSelectNone :=
  @Yul.Reference.BridgeFacts.selectSwitchCase_nil_of_caseList_toFunctionsFuel_select_none

abbrev selectSwitchCaseSomeOfCaseListToFunctionsFuelSelectSomeNone :=
  @Yul.Reference.BridgeFacts.selectSwitchCase_some_of_caseList_toFunctionsFuel_select_some_none

abbrev selectSwitchCaseSomeOfCaseListToFunctionsFuelSelectSomeSome :=
  @Yul.Reference.BridgeFacts.selectSwitchCase_some_of_caseList_toFunctionsFuel_select_some_some

abbrev switchSelectedLowering :=
  @Yul.Reference.BridgeFacts.SwitchSelectedLowering

abbrev switchSelectedLoweringOfCaseListSelectSomeNone :=
  @Yul.Reference.BridgeFacts.switchSelectedLowering_of_caseList_select_some_none

abbrev switchSelectedLoweringOfCaseListSelectSomeSome :=
  @Yul.Reference.BridgeFacts.switchSelectedLowering_of_caseList_select_some_some

abbrev switchNoMatchLowering :=
  @Yul.Reference.BridgeFacts.SwitchNoMatchLowering

abbrev switchNoMatchLoweringOfCaseListSelectNone :=
  @Yul.Reference.BridgeFacts.switchNoMatchLowering_of_caseList_select_none

abbrev functionsSwitchSelectSomeDefault :=
  @Yul.Reference.BridgeFacts.functionsSwitchSelect_some_default

abbrev regularPrefixWithLayoutSwitchNoneOfScrutinee :=
  @Yul.Reference.BridgeFacts.regularPrefixWithLayout_switch_none_of_scrutinee

abbrev resultSeqRunBridgeWithLayoutConsSwitchNoneOfScrutinee :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayout_cons_switch_none_of_scrutinee

abbrev regularPrefixWithLayoutSwitchNoMatchEmptyDefaultOfScrutinee :=
  @Yul.Reference.BridgeFacts.regularPrefixWithLayout_switch_no_match_empty_default_of_scrutinee

abbrev resultSeqRunBridgeWithLayoutConsSwitchNoMatchEmptyDefaultOfScrutinee :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayout_cons_switch_no_match_empty_default_of_scrutinee

abbrev regularPrefixWithLayoutSwitchSomeRegularOfScrutinee :=
  @Yul.Reference.BridgeFacts.regularPrefixWithLayout_switch_some_regular_of_scrutinee

abbrev resultSeqRunBridgeWithLayoutConsSwitchSomeRegularOfScrutinee :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayout_cons_switch_some_regular_of_scrutinee

abbrev resultSeqRunBridgeWithLayoutConsSwitchSomeNonregularOfScrutinee :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayout_cons_switch_some_nonregular_of_scrutinee

abbrev regularPrefixWithLayoutSwitchSelectedRegularOfScrutinee :=
  @Yul.Reference.BridgeFacts.regularPrefixWithLayout_switch_selected_regular_of_scrutinee

abbrev resultSeqRunBridgeWithLayoutConsSwitchSelectedRegularOfScrutinee :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayout_cons_switch_selected_regular_of_scrutinee

abbrev resultSeqRunBridgeWithLayoutConsSwitchSelectedNonregularOfScrutinee :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayout_cons_switch_selected_nonregular_of_scrutinee

abbrev runStatePopOfSingleTempLayoutSlots :=
  @Yul.Reference.BridgeFacts.runState_pop_of_single_temp_layout_slots

abbrev runStateVariableLayoutSlotBridgeOfLookup :=
  @Yul.Reference.BridgeFacts.runState_var_layout_slot_bridge_of_lookup

abbrev regularPrefixWithLayoutSlotsSwitchNoneOfScrutinee :=
  @Yul.Reference.BridgeFacts.regularPrefixWithLayoutSlots_switch_none_of_scrutinee

abbrev regularSeqRunBridgeWithLayoutSlotsConsSwitchNoneOfScrutinee :=
  @Yul.Reference.BridgeFacts.regularSeqRunBridgeWithLayoutSlots_cons_switch_none_of_scrutinee

abbrev regularPrefixWithLayoutSlotsSwitchSomeRegularOfScrutinee :=
  @Yul.Reference.BridgeFacts.regularPrefixWithLayoutSlots_switch_some_regular_of_scrutinee

abbrev regularSeqRunBridgeWithLayoutSlotsConsSwitchSomeRegularOfScrutinee :=
  @Yul.Reference.BridgeFacts.regularSeqRunBridgeWithLayoutSlots_cons_switch_some_regular_of_scrutinee

abbrev regularPrefixWithLayoutSlotsSwitchLiteralNoneChecked :=
  @Yul.Reference.BridgeFacts.regularPrefixWithLayoutSlots_switch_lit_none_checked

abbrev regularSeqRunBridgeWithLayoutSlotsConsSwitchLiteralNoneChecked :=
  @Yul.Reference.BridgeFacts.regularSeqRunBridgeWithLayoutSlots_cons_switch_lit_none_checked

abbrev resultSeqRunBridgeWithLayoutSlotsConsSwitchLiteralNoneChecked :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_switch_lit_none_checked

abbrev resultSeqRunBridgeWithLayoutSlotsConsSwitchLiteralNoneOfLower :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_switch_lit_none_of_lower

abbrev regularSeqRunBridgeWithLayoutSlotsConsSwitchLiteralNoneOfLower :=
  @Yul.Reference.BridgeFacts.regularSeqRunBridgeWithLayoutSlots_cons_switch_lit_none_of_lower

abbrev regularPrefixWithLayoutSlotsSwitchLiteralSomeRegularChecked :=
  @Yul.Reference.BridgeFacts.regularPrefixWithLayoutSlots_switch_lit_some_regular_checked

abbrev regularSeqRunBridgeWithLayoutSlotsConsSwitchLiteralSomeRegularChecked :=
  @Yul.Reference.BridgeFacts.regularSeqRunBridgeWithLayoutSlots_cons_switch_lit_some_regular_checked

abbrev regularPrefixWithLayoutSlotsSwitchVariableNoneChecked :=
  @Yul.Reference.BridgeFacts.regularPrefixWithLayoutSlots_switch_var_none_checked

abbrev regularSeqRunBridgeWithLayoutSlotsConsSwitchVariableNoneChecked :=
  @Yul.Reference.BridgeFacts.regularSeqRunBridgeWithLayoutSlots_cons_switch_var_none_checked

abbrev resultSeqRunBridgeWithLayoutSlotsConsSwitchVariableNoneChecked :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_switch_var_none_checked

abbrev resultSeqRunBridgeWithLayoutSlotsConsSwitchVariableNoneOfLower :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_switch_var_none_of_lower

abbrev regularSeqRunBridgeWithLayoutSlotsConsSwitchVariableNoneOfLower :=
  @Yul.Reference.BridgeFacts.regularSeqRunBridgeWithLayoutSlots_cons_switch_var_none_of_lower

abbrev regularPrefixWithLayoutSlotsSwitchVariableSomeRegularChecked :=
  @Yul.Reference.BridgeFacts.regularPrefixWithLayoutSlots_switch_var_some_regular_checked

abbrev regularSeqRunBridgeWithLayoutSlotsConsSwitchVariableSomeRegularChecked :=
  @Yul.Reference.BridgeFacts.regularSeqRunBridgeWithLayoutSlots_cons_switch_var_some_regular_checked

abbrev resultSeqRunBridgeWithLayoutSlotsConsSwitchNoneOfScrutinee :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_switch_none_of_scrutinee

abbrev resultSeqRunBridgeWithLayoutSlotsConsSwitchSomeRegularOfScrutinee :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_switch_some_regular_of_scrutinee

abbrev resultSeqRunBridgeWithLayoutSlotsConsSwitchSomeNonregularOfScrutinee :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_switch_some_nonregular_of_scrutinee

abbrev regularPrefixWithLayoutSlotsSwitchSelectedRegularOfScrutinee :=
  @Yul.Reference.BridgeFacts.regularPrefixWithLayoutSlots_switch_selected_regular_of_scrutinee

abbrev resultSeqRunBridgeWithLayoutSlotsConsSwitchSelectedRegularOfScrutinee :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_switch_selected_regular_of_scrutinee

abbrev resultSeqRunBridgeWithLayoutSlotsConsSwitchSelectedNonregularOfScrutinee :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_switch_selected_nonregular_of_scrutinee

abbrev resultSeqRunBridgeWithLayoutSlotsConsSwitchLiteralSelectedRegularChecked :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_switch_lit_selected_regular_checked

abbrev resultSeqRunBridgeWithLayoutSlotsConsSwitchLiteralSelectedNonregularChecked :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_switch_lit_selected_nonregular_checked

abbrev resultSeqRunBridgeWithLayoutSlotsConsSwitchLiteralSelectedRegularOfLower :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_switch_lit_selected_regular_of_lower

abbrev resultSeqRunBridgeWithLayoutSlotsConsSwitchLiteralSelectedNonregularOfLower :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_switch_lit_selected_nonregular_of_lower

abbrev regularSeqRunBridgeWithLayoutSlotsConsSwitchLiteralSelectedRegularOfLower :=
  @Yul.Reference.BridgeFacts.regularSeqRunBridgeWithLayoutSlots_cons_switch_lit_selected_regular_of_lower

abbrev resultSeqRunBridgeWithLayoutSlotsConsSwitchLiteralSelectedRegularNonemptyDefaultOfLower :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_switch_lit_selected_regular_nonempty_default_of_lower

abbrev resultSeqRunBridgeWithLayoutSlotsConsSwitchLiteralSelectedNonregularNonemptyDefaultOfLower :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_switch_lit_selected_nonregular_nonempty_default_of_lower

abbrev regularSeqRunBridgeWithLayoutSlotsConsSwitchLiteralSelectedRegularNonemptyDefaultOfLower :=
  @Yul.Reference.BridgeFacts.regularSeqRunBridgeWithLayoutSlots_cons_switch_lit_selected_regular_nonempty_default_of_lower

abbrev resultSeqRunBridgeWithLayoutSlotsConsSwitchVariableSelectedRegularChecked :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_switch_var_selected_regular_checked

abbrev resultSeqRunBridgeWithLayoutSlotsConsSwitchVariableSelectedNonregularChecked :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_switch_var_selected_nonregular_checked

abbrev resultSeqRunBridgeWithLayoutSlotsConsSwitchVariableSelectedRegularOfLower :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_switch_var_selected_regular_of_lower

abbrev resultSeqRunBridgeWithLayoutSlotsConsSwitchVariableSelectedNonregularOfLower :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_switch_var_selected_nonregular_of_lower

abbrev regularSeqRunBridgeWithLayoutSlotsConsSwitchVariableSelectedRegularOfLower :=
  @Yul.Reference.BridgeFacts.regularSeqRunBridgeWithLayoutSlots_cons_switch_var_selected_regular_of_lower

abbrev resultSeqRunBridgeWithLayoutSlotsConsSwitchVariableSelectedRegularNonemptyDefaultOfLower :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_switch_var_selected_regular_nonempty_default_of_lower

abbrev resultSeqRunBridgeWithLayoutSlotsConsSwitchVariableSelectedNonregularNonemptyDefaultOfLower :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_switch_var_selected_nonregular_nonempty_default_of_lower

abbrev regularSeqRunBridgeWithLayoutSlotsConsSwitchVariableSelectedRegularNonemptyDefaultOfLower :=
  @Yul.Reference.BridgeFacts.regularSeqRunBridgeWithLayoutSlots_cons_switch_var_selected_regular_nonempty_default_of_lower

abbrev regularPrefixWithLayoutSwitchLiteralNoneChecked :=
  @Yul.Reference.BridgeFacts.regularPrefixWithLayout_switch_lit_none_checked

abbrev resultSeqRunBridgeWithLayoutConsSwitchLiteralNoneChecked :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayout_cons_switch_lit_none_checked

abbrev regularPrefixWithLayoutSwitchLiteralSomeRegularChecked :=
  @Yul.Reference.BridgeFacts.regularPrefixWithLayout_switch_lit_some_regular_checked

abbrev resultSeqRunBridgeWithLayoutConsSwitchLiteralSomeRegularChecked :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayout_cons_switch_lit_some_regular_checked

abbrev resultSeqRunBridgeWithLayoutConsSwitchLiteralSomeNonregularChecked :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayout_cons_switch_lit_some_nonregular_checked

abbrev regularPrefixWithLayoutSwitchVariableNoneChecked :=
  @Yul.Reference.BridgeFacts.regularPrefixWithLayout_switch_var_none_checked

abbrev resultSeqRunBridgeWithLayoutConsSwitchVariableNoneChecked :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayout_cons_switch_var_none_checked

abbrev regularPrefixWithLayoutSwitchVariableSomeRegularChecked :=
  @Yul.Reference.BridgeFacts.regularPrefixWithLayout_switch_var_some_regular_checked

abbrev resultSeqRunBridgeWithLayoutConsSwitchVariableSomeRegularChecked :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayout_cons_switch_var_some_regular_checked

abbrev resultSeqRunBridgeWithLayoutConsSwitchVariableSomeNonregularChecked :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayout_cons_switch_var_some_nonregular_checked

abbrev someResultSeqRunBridgeConsLetNoneChecked :=
  @Yul.Reference.BridgeFacts.someResultSeqRunBridge_cons_let_none_checked

abbrev someResultSeqRunBridgeConsLetLiteralSingleChecked :=
  @Yul.Reference.BridgeFacts.someResultSeqRunBridge_cons_let_lit_single_checked

abbrev someResultSeqRunBridgeConsLetVariableSingleChecked :=
  @Yul.Reference.BridgeFacts.someResultSeqRunBridge_cons_let_var_single_checked

abbrev someResultSeqRunBridgeConsAssignLiteralSingleChecked :=
  @Yul.Reference.BridgeFacts.someResultSeqRunBridge_cons_assign_lit_single_checked

abbrev someResultSeqRunBridgeConsAssignVariableSingleChecked :=
  @Yul.Reference.BridgeFacts.someResultSeqRunBridge_cons_assign_var_single_checked

abbrev someResultSeqRunBridgeConsBlockChecked :=
  @Yul.Reference.BridgeFacts.someResultSeqRunBridge_cons_block_checked

abbrev someResultSeqRunBridgeConsBlockNonregular :=
  @Yul.Reference.BridgeFacts.someResultSeqRunBridge_cons_block_nonregular

abbrev resultSeqRunBridgeWithLayoutConsBlockNonregular :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayout_cons_block_nonregular

abbrev resultSeqRunBridgeWithLayoutSlotsConsBlockNonregular :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_block_nonregular

abbrev functionsRunOpenTerminalArgsOfRunCode :=
  @Yul.Reference.BridgeFacts.functions_runOpen_terminalArgs_of_runCode

abbrev errorPrefixTerminalArgsOfSourceError :=
  @Yul.Reference.BridgeFacts.errorPrefix_terminalArgs_of_source_error

abbrev resultSeqRunBridgeConsTerminalArgsOfSourceError :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridge_cons_terminalArgs_of_source_error

abbrev resultSeqRunBridgeWithLayoutConsTerminalArgsOfSourceError :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayout_cons_terminalArgs_of_source_error

abbrev resultSeqRunBridgeWithLayoutSlotsConsTerminalArgsOfSourceError :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_terminalArgs_of_source_error

abbrev someResultSeqRunBridgeConsTerminalArgsOfSourceError :=
  @Yul.Reference.BridgeFacts.someResultSeqRunBridge_cons_terminalArgs_of_source_error

abbrev okSeqRunBridgeConsOfRegularPrefix :=
  @Yul.Reference.BridgeFacts.okSeqRunBridge_cons_of_regular_prefix

abbrev someOkSeqRunBridgeConsOfRegularPrefix :=
  @Yul.Reference.BridgeFacts.someOkSeqRunBridge_cons_of_regular_prefix

abbrev okSeqRunBridgeBreakPrefix :=
  @Yul.Reference.BridgeFacts.okSeqRunBridge_break_prefix

abbrev someOkSeqRunBridgeBreakPrefix :=
  @Yul.Reference.BridgeFacts.someOkSeqRunBridge_break_prefix

abbrev okSeqRunBridgeContinuePrefix :=
  @Yul.Reference.BridgeFacts.okSeqRunBridge_continue_prefix

abbrev someOkSeqRunBridgeContinuePrefix :=
  @Yul.Reference.BridgeFacts.someOkSeqRunBridge_continue_prefix

abbrev okSeqRunBridgeLeaveZeroReturnsPrefix :=
  @Yul.Reference.BridgeFacts.okSeqRunBridge_leave_zeroReturns_prefix

abbrev someOkSeqRunBridgeLeaveZeroReturnsPrefix :=
  @Yul.Reference.BridgeFacts.someOkSeqRunBridge_leave_zeroReturns_prefix

abbrev someResultSeqRunBridgeBreakPrefix :=
  @Yul.Reference.BridgeFacts.someResultSeqRunBridge_break_prefix

abbrev someResultSeqRunBridgeContinuePrefix :=
  @Yul.Reference.BridgeFacts.someResultSeqRunBridge_continue_prefix

abbrev someResultSeqRunBridgeLeaveZeroReturnsPrefix :=
  @Yul.Reference.BridgeFacts.someResultSeqRunBridge_leave_zeroReturns_prefix

abbrev resultSeqRunBridgeWithLayoutConsBreakChecked :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayout_cons_break_checked

abbrev resultSeqRunBridgeWithLayoutConsContinueChecked :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayout_cons_continue_checked

abbrev resultSeqRunBridgeWithLayoutConsLeaveZeroReturnsChecked :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayout_cons_leave_zeroReturns_checked

abbrev resultSeqRunBridgeWithLayoutSlotsConsBreakChecked :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_break_checked

abbrev resultSeqRunBridgeWithLayoutSlotsConsContinueChecked :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_continue_checked

abbrev resultSeqRunBridgeWithLayoutSlotsConsLeaveZeroReturnsChecked :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_leave_zeroReturns_checked

abbrev resultSeqRunBridgeWithLayoutSlotsConsLeaveChecked :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_leave_checked

abbrev resultSeqRunBridgeWithLayoutSlotsConsBreakOfLower :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_break_of_lower

abbrev resultSeqRunBridgeWithLayoutSlotsConsContinueOfLower :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_continue_of_lower

abbrev resultSeqRunBridgeWithLayoutSlotsConsLeaveOfLower :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_leave_of_lower

abbrev runReplicatePopExists :=
  @Yul.Reference.BridgeFacts.run_replicate_pop_exists

abbrev cleanupManyPreservingRunExists :=
  @Yul.Reference.BridgeFacts.cleanupManyPreserving_run_exists

abbrev runCleanupToPreservingCompilerStateRelWithTempsAndLayoutSlotsSuffix :=
  @Yul.Reference.BridgeFacts.runCleanupToPreserving_compilerStateRelWithTempsAndLayoutSlots_suffix

abbrev cleanupToCompilerStateRelExact :=
  @Yul.Reference.BridgeFacts.cleanupTo_compilerStateRel_exact

abbrev cleanupToHiddenLocals :=
  @Yul.Reference.BridgeFacts.cleanupTo_hiddenLocals

abbrev cleanupToCompilerStateRelRestrictExact :=
  @Yul.Reference.BridgeFacts.cleanupTo_compilerStateRel_restrict_exact

abbrev cleanupToCompilerStateRelRestrictDomainExact :=
  @Yul.Reference.BridgeFacts.cleanupTo_compilerStateRel_restrict_domain_exact

abbrev regularBlockScopeCloseBridge :=
  @Yul.Reference.BridgeFacts.regular_block_scope_close_bridge

abbrev toObjectsRootComponents :=
  @Yul.Reference.BridgeFacts.toObjects?_root_components

abbrev toObjectsDispatcherBody :=
  @Yul.Reference.BridgeFacts.toObjects?_dispatcher_body

abbrev regularSeqRunBridgeWithLayoutRunScoped :=
  @Yul.Reference.BridgeFacts.regularSeqRunBridgeWithLayout_runScoped

abbrev regularSeqRunBridgeWithLayoutFunctionsProgramRun :=
  @Yul.Reference.BridgeFacts.regularSeqRunBridgeWithLayout_functionsProgram_run

abbrev regularSeqRunBridgeWithLayoutLoweredRun :=
  @Yul.Reference.BridgeFacts.regularSeqRunBridgeWithLayout_lowered_run

abbrev regularPrefixExistsBlockOfOpen :=
  @Yul.Reference.BridgeFacts.regularPrefixExists_block_of_open

abbrev regularPrefixExistsBlockOfSeqWithLayout :=
  @Yul.Reference.BridgeFacts.regularPrefixExists_block_of_seq_with_layout

abbrev regularPrefixWithLayoutBlockOfSeqWithLayout :=
  @Yul.Reference.BridgeFacts.regularPrefixWithLayout_block_of_seq_with_layout

abbrev okBlockRunBridgeNil :=
  @Yul.Reference.BridgeFacts.okBlockRunBridge_nil

abbrev someOkBlockRunBridgeNil :=
  @Yul.Reference.BridgeFacts.someOkBlockRunBridge_nil

abbrev resultBlockRunBridgeNil :=
  @Yul.Reference.BridgeFacts.resultBlockRunBridge_nil

abbrev someResultBlockRunBridgeNil :=
  @Yul.Reference.BridgeFacts.someResultBlockRunBridge_nil

abbrev okBlockRunBridgeBreak :=
  @Yul.Reference.BridgeFacts.okBlockRunBridge_break

abbrev someOkBlockRunBridgeBreak :=
  @Yul.Reference.BridgeFacts.someOkBlockRunBridge_break

abbrev someResultBlockRunBridgeBreak :=
  @Yul.Reference.BridgeFacts.someResultBlockRunBridge_break

abbrev okBlockRunBridgeContinue :=
  @Yul.Reference.BridgeFacts.okBlockRunBridge_continue

abbrev someOkBlockRunBridgeContinue :=
  @Yul.Reference.BridgeFacts.someOkBlockRunBridge_continue

abbrev someResultBlockRunBridgeContinue :=
  @Yul.Reference.BridgeFacts.someResultBlockRunBridge_continue

abbrev okBlockRunBridgeLeaveZeroReturns :=
  @Yul.Reference.BridgeFacts.okBlockRunBridge_leave_zeroReturns

abbrev someOkBlockRunBridgeLeaveZeroReturns :=
  @Yul.Reference.BridgeFacts.someOkBlockRunBridge_leave_zeroReturns

abbrev someResultBlockRunBridgeLeaveZeroReturns :=
  @Yul.Reference.BridgeFacts.someResultBlockRunBridge_leave_zeroReturns

abbrev lookupDepthFromOfGetNodup :=
  @Locals.Layout.lookupDepthFrom_of_get?_nodup

abbrev lookupDepthOfGetNodup :=
  @Locals.Layout.lookupDepth?_of_get?_nodup

abbrev evmDupSuccGet :=
  @Locals.Direct.evm_dup_succ_get?

abbrev stackOpDupStepEqDup :=
  @Locals.Direct.stackOp_dup?_step_eq_dup

abbrev evmSwapAssignGet :=
  @Yul.Reference.BridgeFacts.evm_swap_assign_get?

abbrev stackOpSwapStepEqSwap :=
  @Yul.Reference.BridgeFacts.stackOp_swap?_step_eq_swap

abbrev execLetLiteralSingleOk :=
  @Yul.Reference.BridgeFacts.exec_let_lit_single_ok

abbrev execLetLiteralSingleExactExtension :=
  @Yul.Reference.BridgeFacts.exec_let_lit_single_exact_extension

abbrev execLetNoneSingleOk :=
  @Yul.Reference.BridgeFacts.exec_let_none_single_ok

abbrev execLetVariableSingleOk :=
  @Yul.Reference.BridgeFacts.exec_let_var_single_ok

abbrev execLetVariableSingleExactExtension :=
  @Yul.Reference.BridgeFacts.exec_let_var_single_exact_extension

abbrev evalLitCompilerPushTemp :=
  @Yul.Reference.BridgeFacts.eval_lit_compiler_push_temp

abbrev evalLitCompilerPushTempHidden :=
  @Yul.Reference.BridgeFacts.eval_lit_compiler_push_temp_hidden

abbrev evalVarCompilerPushTemp :=
  @Yul.Reference.BridgeFacts.eval_var_compiler_push_temp

abbrev evalVarCompilerPushTempWithTempsHidden :=
  @Yul.Reference.BridgeFacts.eval_var_compiler_push_temp_withTemps_hidden

abbrev evalVarCompilerPushTempHidden :=
  @Yul.Reference.BridgeFacts.eval_var_compiler_push_temp_hidden

abbrev runConditionOfSingleTemp :=
  @Yul.Reference.BridgeFacts.runCondition_of_single_temp

abbrev runConditionOfSingleTempHidden :=
  @Yul.Reference.BridgeFacts.runCondition_of_single_temp_hidden

abbrev runConditionOfSingleTempLayoutSlots :=
  @Yul.Reference.BridgeFacts.runCondition_of_single_temp_layout_slots

abbrev runConditionIszeroOfSingleZeroTempLayoutSlots :=
  @Yul.Reference.BridgeFacts.runCondition_iszero_of_single_zero_temp_layout_slots

abbrev runStatePopOfSingleTemp :=
  @Yul.Reference.BridgeFacts.runState_pop_of_single_temp

abbrev runStatePopOfSingleTempHidden :=
  @Yul.Reference.BridgeFacts.runState_pop_of_single_temp_hidden

abbrev conditionLiteralBridge :=
  @Yul.Reference.BridgeFacts.condition_lit_bridge

abbrev conditionLiteralHiddenBridge :=
  @Yul.Reference.BridgeFacts.condition_lit_hidden_bridge

abbrev conditionLiteralLayoutSlotBridge :=
  @Yul.Reference.BridgeFacts.condition_lit_layout_slot_bridge

abbrev conditionVariableBridge :=
  @Yul.Reference.BridgeFacts.condition_var_bridge

abbrev conditionVariableHiddenBridge :=
  @Yul.Reference.BridgeFacts.condition_var_hidden_bridge

abbrev conditionVariableBridgeOfLookup :=
  @Yul.Reference.BridgeFacts.condition_var_bridge_of_lookup

abbrev conditionVariableHiddenBridgeOfLookup :=
  @Yul.Reference.BridgeFacts.condition_var_hidden_bridge_of_lookup

abbrev conditionVariableSlotBridgeOfLookup :=
  @Yul.Reference.BridgeFacts.condition_var_slot_bridge_of_lookup

abbrev conditionVariableLayoutSlotBridge :=
  @Yul.Reference.BridgeFacts.condition_var_layout_slot_bridge

abbrev conditionVariableLayoutSlotBridgeOfLookup :=
  @Yul.Reference.BridgeFacts.condition_var_layout_slot_bridge_of_lookup

abbrev evalLiteralCompilerPushTempLayoutSlots :=
  @Yul.Reference.BridgeFacts.eval_lit_compiler_push_temp_layout_slots

abbrev evalVariableCompilerPushTempLayoutSlots :=
  @Yul.Reference.BridgeFacts.eval_var_compiler_push_temp_layout_slots

abbrev evalVariableCompilerPushTempWithTempsLayoutSlots :=
  @Yul.Reference.BridgeFacts.eval_var_compiler_push_temp_withTemps_layout_slots

abbrev runCodeVariableWithTempsLayoutSlots :=
  @Yul.Reference.BridgeFacts.runCode_var_withTemps_layout_slots

abbrev returnLayoutBounds :=
  @Yul.Reference.BridgeFacts.ReturnLayoutBounds

abbrev exprSeqRunCodeCongrArg :=
  @Yul.Reference.BridgeFacts.exprSeq_runCode_congrArg

abbrev returnStackRelNil :=
  @Yul.Reference.BridgeFacts.returnStackRel_nil

abbrev returnStackRelCons :=
  @Yul.Reference.BridgeFacts.returnStackRel_cons

abbrev returnStackRelLength :=
  @Yul.Reference.BridgeFacts.returnStackRel_length

abbrev compilerStateRelWithTempsAndLayoutSlotsWithReturnLayout :=
  @Yul.Reference.BridgeFacts.CompilerStateRelWithTempsAndLayoutSlots.withReturnLayout

abbrev returnExprsRunCodeLayoutSlots :=
  @Yul.Reference.BridgeFacts.returnExprs_runCode_layout_slots

abbrev pushReturnsLayoutSlotsBridge :=
  @Yul.Reference.BridgeFacts.pushReturns_layout_slots_bridge

abbrev functionsStmtLetLiteralSingleBridge :=
  @Yul.Reference.BridgeFacts.functions_stmt_let_lit_single_bridge

abbrev functionsStmtLetLiteralHiddenBridge :=
  @Yul.Reference.BridgeFacts.functions_stmt_let_lit_hidden_bridge

abbrev functionsStmtLetLiteralLayoutSlotsBridge :=
  @Yul.Reference.BridgeFacts.functions_stmt_let_lit_layout_slots_bridge

abbrev functionsStmtLetLiteralLayoutSlotsHiddenBridge :=
  @Yul.Reference.BridgeFacts.functions_stmt_let_lit_layout_slots_hidden_bridge

abbrev functionsStmtLetLiteralSingleBridgeChecked :=
  @Yul.Reference.BridgeFacts.functions_stmt_let_lit_single_bridge_checked

abbrev functionsStmtLetNoneSingleBridge :=
  @Yul.Reference.BridgeFacts.functions_stmt_let_none_single_bridge

abbrev functionsStmtLetNoneLayoutSlotsBridge :=
  @Yul.Reference.BridgeFacts.functions_stmt_let_none_layout_slots_bridge

abbrev functionsInitNamesRunOpenStack :=
  @Yul.Reference.BridgeFacts.functions_initNames_runOpen_stack

abbrev functionsInitNamesHiddenBridge :=
  @Yul.Reference.BridgeFacts.functions_initNames_hidden_bridge

abbrev functionsInitNamesLayoutSlotsHiddenBridge :=
  @Yul.Reference.BridgeFacts.functions_initNames_layout_slots_hidden_bridge

abbrev functionsInitNamesAppendRunOpenStack :=
  @Yul.Reference.BridgeFacts.functions_initNames_append_runOpen_stack

abbrev functionsInitNamesAppendHiddenBridge :=
  @Yul.Reference.BridgeFacts.functions_initNames_append_hidden_bridge

abbrev functionsBlockLetNoneBridge :=
  @Yul.Reference.BridgeFacts.functions_block_let_none_bridge

abbrev functionsBlockLetNoneLayoutSlotsBridge :=
  @Yul.Reference.BridgeFacts.functions_block_let_none_layout_slots_bridge

abbrev functionsBlockLetNoneBridgeChecked :=
  @Yul.Reference.BridgeFacts.functions_block_let_none_bridge_checked

abbrev importedBlockLetNoneConsOk :=
  @Yul.Reference.BridgeFacts.imported_block_let_none_cons_ok

abbrev regularPrefixLetNoneBridge :=
  @Yul.Reference.BridgeFacts.regularPrefix_let_none_bridge

abbrev regularPrefixLetNoneBridgeChecked :=
  @Yul.Reference.BridgeFacts.regularPrefix_let_none_bridge_checked

abbrev regularPrefixWithLayoutLetNoneBridgeChecked :=
  @Yul.Reference.BridgeFacts.regularPrefixWithLayout_let_none_bridge_checked

abbrev regularPrefixLetLiteralSingleBridge :=
  @Yul.Reference.BridgeFacts.regularPrefix_let_lit_single_bridge

abbrev regularPrefixLetLiteralSingleBridgeChecked :=
  @Yul.Reference.BridgeFacts.regularPrefix_let_lit_single_bridge_checked

abbrev regularPrefixWithLayoutLetLiteralSingleBridgeChecked :=
  @Yul.Reference.BridgeFacts.regularPrefixWithLayout_let_lit_single_bridge_checked

abbrev regularPrefixLetVariableSingleBridge :=
  @Yul.Reference.BridgeFacts.regularPrefix_let_var_single_bridge

abbrev regularPrefixLetVariableSingleBridgeChecked :=
  @Yul.Reference.BridgeFacts.regularPrefix_let_var_single_bridge_checked

abbrev regularPrefixWithLayoutLetVariableSingleBridgeChecked :=
  @Yul.Reference.BridgeFacts.regularPrefixWithLayout_let_var_single_bridge_checked

abbrev regularPrefixWithLayoutSlotsLetNoneSingleBridgeChecked :=
  @Yul.Reference.BridgeFacts.regularPrefixWithLayoutSlots_let_none_single_bridge_checked

abbrev regularPrefixWithLayoutSlotsLetNoneBridgeChecked :=
  @Yul.Reference.BridgeFacts.regularPrefixWithLayoutSlots_let_none_bridge_checked

abbrev regularPrefixWithLayoutSlotsLetLiteralSingleBridgeChecked :=
  @Yul.Reference.BridgeFacts.regularPrefixWithLayoutSlots_let_lit_single_bridge_checked

abbrev regularPrefixWithLayoutSlotsLetVariableSingleBridgeChecked :=
  @Yul.Reference.BridgeFacts.regularPrefixWithLayoutSlots_let_var_single_bridge_checked

abbrev functionsStmtLetVariableSingleBridge :=
  @Yul.Reference.BridgeFacts.functions_stmt_let_var_single_bridge

abbrev functionsStmtLetVariableLayoutSlotsBridge :=
  @Yul.Reference.BridgeFacts.functions_stmt_let_var_layout_slots_bridge

abbrev functionsStmtLetVariableSingleBridgeChecked :=
  @Yul.Reference.BridgeFacts.functions_stmt_let_var_single_bridge_checked

abbrev execAssignLiteralSingleOk :=
  @Yul.Reference.BridgeFacts.exec_assign_lit_single_ok

abbrev execAssignVariableSingleOk :=
  @Yul.Reference.BridgeFacts.exec_assign_var_single_ok

abbrev assignTopCompilerExact :=
  @Yul.Reference.BridgeFacts.assignTop_compiler_exact

abbrev assignTopCompilerLayoutSlots :=
  @Yul.Reference.BridgeFacts.assignTop_compiler_layout_slots

abbrev functionsStmtAssignSingleLayoutSlotsBridgeOfEval :=
  @Yul.Reference.BridgeFacts.functions_stmt_assign_single_layout_slots_bridge_of_eval

abbrev functionsStmtAssignLiteralLayoutSlotsBridge :=
  @Yul.Reference.BridgeFacts.functions_stmt_assign_lit_layout_slots_bridge

abbrev functionsStmtAssignVariableLayoutSlotsBridge :=
  @Yul.Reference.BridgeFacts.functions_stmt_assign_var_layout_slots_bridge

abbrev functionsStmtAssignLiteralSingleBridge :=
  @Yul.Reference.BridgeFacts.functions_stmt_assign_lit_single_bridge

abbrev functionsStmtAssignLiteralSingleBridgeChecked :=
  @Yul.Reference.BridgeFacts.functions_stmt_assign_lit_single_bridge_checked

abbrev functionsStmtAssignVariableSingleBridge :=
  @Yul.Reference.BridgeFacts.functions_stmt_assign_var_single_bridge

abbrev functionsStmtAssignVariableSingleBridgeChecked :=
  @Yul.Reference.BridgeFacts.functions_stmt_assign_var_single_bridge_checked

abbrev regularPrefixAssignLiteralSingleBridge :=
  @Yul.Reference.BridgeFacts.regularPrefix_assign_lit_single_bridge

abbrev regularPrefixAssignLiteralSingleBridgeChecked :=
  @Yul.Reference.BridgeFacts.regularPrefix_assign_lit_single_bridge_checked

abbrev regularPrefixWithLayoutAssignLiteralSingleBridgeChecked :=
  @Yul.Reference.BridgeFacts.regularPrefixWithLayout_assign_lit_single_bridge_checked

abbrev regularPrefixAssignVariableSingleBridge :=
  @Yul.Reference.BridgeFacts.regularPrefix_assign_var_single_bridge

abbrev regularPrefixAssignVariableSingleBridgeChecked :=
  @Yul.Reference.BridgeFacts.regularPrefix_assign_var_single_bridge_checked

abbrev regularPrefixWithLayoutAssignVariableSingleBridgeChecked :=
  @Yul.Reference.BridgeFacts.regularPrefixWithLayout_assign_var_single_bridge_checked

abbrev regularPrefixWithLayoutSlotsAssignLiteralSingleBridgeChecked :=
  @Yul.Reference.BridgeFacts.regularPrefixWithLayoutSlots_assign_lit_single_bridge_checked

abbrev regularPrefixWithLayoutSlotsAssignVariableSingleBridgeChecked :=
  @Yul.Reference.BridgeFacts.regularPrefixWithLayoutSlots_assign_var_single_bridge_checked

abbrev regularSeqRunBridgeWithLayoutSlotsConsLetNoneChecked :=
  @Yul.Reference.BridgeFacts.regularSeqRunBridgeWithLayoutSlots_cons_let_none_checked

abbrev regularSeqRunBridgeWithLayoutSlotsConsLetNoneSingleChecked :=
  @Yul.Reference.BridgeFacts.regularSeqRunBridgeWithLayoutSlots_cons_let_none_single_checked

abbrev regularSeqRunBridgeWithLayoutSlotsConsLetNoneSingleOfLower :=
  @Yul.Reference.BridgeFacts.regularSeqRunBridgeWithLayoutSlots_cons_let_none_single_of_lower

abbrev regularSeqRunBridgeWithLayoutSlotsConsLetLiteralSingleChecked :=
  @Yul.Reference.BridgeFacts.regularSeqRunBridgeWithLayoutSlots_cons_let_lit_single_checked

abbrev regularSeqRunBridgeWithLayoutSlotsConsLetLiteralSingleOfLower :=
  @Yul.Reference.BridgeFacts.regularSeqRunBridgeWithLayoutSlots_cons_let_lit_single_of_lower

abbrev regularSeqRunBridgeWithLayoutSlotsConsLetVariableSingleChecked :=
  @Yul.Reference.BridgeFacts.regularSeqRunBridgeWithLayoutSlots_cons_let_var_single_checked

abbrev regularSeqRunBridgeWithLayoutSlotsConsLetVariableSingleOfLower :=
  @Yul.Reference.BridgeFacts.regularSeqRunBridgeWithLayoutSlots_cons_let_var_single_of_lower

abbrev regularSeqRunBridgeWithLayoutSlotsConsAssignLiteralSingleChecked :=
  @Yul.Reference.BridgeFacts.regularSeqRunBridgeWithLayoutSlots_cons_assign_lit_single_checked

abbrev regularSeqRunBridgeWithLayoutSlotsConsAssignLiteralSingleOfLower :=
  @Yul.Reference.BridgeFacts.regularSeqRunBridgeWithLayoutSlots_cons_assign_lit_single_of_lower

abbrev regularSeqRunBridgeWithLayoutSlotsConsAssignVariableSingleChecked :=
  @Yul.Reference.BridgeFacts.regularSeqRunBridgeWithLayoutSlots_cons_assign_var_single_checked

abbrev regularSeqRunBridgeWithLayoutSlotsConsAssignVariableSingleOfLower :=
  @Yul.Reference.BridgeFacts.regularSeqRunBridgeWithLayoutSlots_cons_assign_var_single_of_lower

abbrev regularSeqRunBridgeWithLayoutSlotsConsBlockChecked :=
  @Yul.Reference.BridgeFacts.regularSeqRunBridgeWithLayoutSlots_cons_block_checked

abbrev resultSeqRunBridgeWithLayoutSlotsConsBlockNilOfLower :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_block_nil_of_lower

abbrev regularSeqRunBridgeWithLayoutSlotsConsBlockNilOfLower :=
  @Yul.Reference.BridgeFacts.regularSeqRunBridgeWithLayoutSlots_cons_block_nil_of_lower

abbrev resultSeqRunBridgeWithLayoutSlotsConsBlockRegularOfLower :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_block_regular_of_lower

abbrev regularSeqRunBridgeWithLayoutSlotsConsBlockRegularOfLower :=
  @Yul.Reference.BridgeFacts.regularSeqRunBridgeWithLayoutSlots_cons_block_regular_of_lower

abbrev resultSeqRunBridgeWithLayoutSlotsConsBlockNonregularOfLower :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_block_nonregular_of_lower

abbrev resultSeqRunBridgeWithLayoutSlotsConsLetNoneSingleChecked :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_let_none_single_checked

abbrev resultSeqRunBridgeWithLayoutSlotsConsLetNoneSingleOfLower :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_let_none_single_of_lower

abbrev resultSeqRunBridgeWithLayoutSlotsConsLetNoneChecked :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_let_none_checked

abbrev resultSeqRunBridgeWithLayoutSlotsConsLetLiteralSingleChecked :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_let_lit_single_checked

abbrev resultSeqRunBridgeWithLayoutSlotsConsLetLiteralSingleOfLower :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_let_lit_single_of_lower

abbrev resultSeqRunBridgeWithLayoutSlotsConsLetVariableSingleChecked :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_let_var_single_checked

abbrev resultSeqRunBridgeWithLayoutSlotsConsLetVariableSingleOfLower :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_let_var_single_of_lower

abbrev resultSeqRunBridgeWithLayoutSlotsConsAssignLiteralSingleChecked :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_assign_lit_single_checked

abbrev resultSeqRunBridgeWithLayoutSlotsConsAssignLiteralSingleOfLower :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_assign_lit_single_of_lower

abbrev resultSeqRunBridgeWithLayoutSlotsConsAssignVariableSingleChecked :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_assign_var_single_checked

abbrev resultSeqRunBridgeWithLayoutSlotsConsAssignVariableSingleOfLower :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_assign_var_single_of_lower

abbrev resultSeqRunBridgeWithLayoutSlotsConsBlockChecked :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_block_checked

abbrev regularPrefixWithLayoutSlotsForFalseOfCondition :=
  @Yul.Reference.BridgeFacts.regularPrefixWithLayoutSlots_for_false_of_condition

abbrev regularPrefixWithLayoutSlotsForFalseOfRunCode :=
  @Yul.Reference.BridgeFacts.regularPrefixWithLayoutSlots_for_false_of_runCode

abbrev resultSeqRunBridgeWithLayoutSlotsConsForFalseOfCondition :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_for_false_of_condition

abbrev resultSeqRunBridgeWithLayoutSlotsConsForFalseOfRunCode :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_for_false_of_runCode

abbrev regularSeqRunBridgeWithLayoutSlotsConsForFalseOfCondition :=
  @Yul.Reference.BridgeFacts.regularSeqRunBridgeWithLayoutSlots_cons_for_false_of_condition

abbrev regularSeqRunBridgeWithLayoutSlotsConsForFalseOfRunCode :=
  @Yul.Reference.BridgeFacts.regularSeqRunBridgeWithLayoutSlots_cons_for_false_of_runCode

abbrev resultSeqRunBridgeWithLayoutSlotsConsForLiteralFalseOfLower :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_for_lit_false_of_lower

abbrev regularSeqRunBridgeWithLayoutSlotsConsForLiteralFalseOfLower :=
  @Yul.Reference.BridgeFacts.regularSeqRunBridgeWithLayoutSlots_cons_for_lit_false_of_lower

abbrev resultSeqRunBridgeWithLayoutSlotsConsForVariableFalseOfLower :=
  @Yul.Reference.BridgeFacts.resultSeqRunBridgeWithLayoutSlots_cons_for_var_false_of_lower

abbrev regularSeqRunBridgeWithLayoutSlotsConsForVariableFalseOfLower :=
  @Yul.Reference.BridgeFacts.regularSeqRunBridgeWithLayoutSlots_cons_for_var_false_of_lower

abbrev switchDefaultCheckedByReferenceBridge :=
  @Yul.Reference.Safe.switch_default_safe_of_stmt

abbrev revertAcceptedByReferenceBridge :=
  Yul.Reference.Safe.accepts_revert

abbrev selfdestructAcceptedByReferenceBridge :=
  Yul.Reference.Safe.accepts_selfdestruct

abbrev returnAcceptedByReferenceBridge :=
  Yul.Reference.Safe.accepts_return

abbrev callAcceptedByFullReferenceSurface :=
  Yul.Reference.Safe.Full.accepts_call

abbrev createAcceptedByFullReferenceSurface :=
  Yul.Reference.Safe.Full.accepts_create

abbrev callcodeAcceptedByFullReferenceSurface :=
  Yul.Reference.Safe.Full.accepts_callcode

abbrev delegatecallAcceptedByFullReferenceSurface :=
  Yul.Reference.Safe.Full.accepts_delegatecall

abbrev create2AcceptedByFullReferenceSurface :=
  Yul.Reference.Safe.Full.accepts_create2

abbrev staticcallAcceptedByFullReferenceSurface :=
  Yul.Reference.Safe.Full.accepts_staticcall

abbrev callRejectedByReferenceBridge :=
  Yul.Reference.Safe.rejects_call

abbrev createRejectedByReferenceBridge :=
  Yul.Reference.Safe.rejects_create

abbrev callcodeRejectedByReferenceBridge :=
  Yul.Reference.Safe.rejects_callcode

abbrev delegatecallRejectedByReferenceBridge :=
  Yul.Reference.Safe.rejects_delegatecall

abbrev create2RejectedByReferenceBridge :=
  Yul.Reference.Safe.rejects_create2

abbrev staticcallRejectedByReferenceBridge :=
  Yul.Reference.Safe.rejects_staticcall

abbrev primitiveBoundaryExact :=
  Yul.Reference.Safe.primitive_iff_not_codeImage_not_external

abbrev primitiveBoundaryImportedIncompleteExternal :=
  Yul.Reference.Safe.primitive_iff_not_importedIncomplete_not_externalBoundary

abbrev acceptedLoweredPrimitiveNoCallCreate :=
  @Yul.Reference.Safe.lowered_basicOp_not_callCreate

abbrev yulToSeqNoCallCreate :=
  @Yul.NoCallCreate.toSeq?_noCallCreate

abbrev yulToStackSeqNoCallCreate :=
  @Yul.NoCallCreate.toStackSeq?_noCallCreate

abbrev yulExprToLocalsNoCallCreate :=
  @Yul.NoCallCreate.expr_toLocals?_noCallCreate

abbrev yulExprListToLocalsNoCallCreate :=
  @Yul.NoCallCreate.exprList_toLocals1?_all_noCallCreate

abbrev yulExprLowerNoCallCreate :=
  @Yul.NoCallCreate.expr_lower?_noCallCreate

abbrev yulExprLowerBoundNoCallCreate :=
  @Yul.NoCallCreate.exprList_lowerBound1?_noCallCreate

abbrev yulExprStmtCallNoCallCreate :=
  @Yul.NoCallCreate.exprStmtCall_toFunctionsListFuel?_noCallCreate

abbrev yulStmtToFunctionsNoCallCreate :=
  @Yul.NoCallCreate.stmt_toFunctionsListFuel?_noCallCreate

abbrev yulStmtListToFunctionsNoCallCreate :=
  @Yul.NoCallCreate.stmtList_toFunctionsFuel?_noCallCreate

abbrev yulCaseListToFunctionsNoCallCreate :=
  @Yul.NoCallCreate.caseList_toFunctionsFuel?_noCallCreate

abbrev yulBlockToFunctionsNoCallCreate :=
  @Yul.NoCallCreate.block_toFunctionsFuel?_noCallCreate

abbrev yulFunctionDefinitionNoCallCreate :=
  @Yul.NoCallCreate.functionDefinition_toFunDefFuel?_noCallCreate

abbrev yulFunctionListNoCallCreate :=
  @Yul.NoCallCreate.functionList_toFunDefsFuel?_noCallCreate

abbrev yulContractToObjectsNoCallCreate :=
  @Yul.NoCallCreate.contract_toObjects?_functions_noCallCreate

abbrev yulProgramToObjectsNoCallCreate :=
  @Yul.NoCallCreate.program_toObjects?_functions_noCallCreate

abbrev assemblyUsesCallCreateAppend :=
  Assembly.Program.usesCallCreate_append

abbrev assemblyUsesCallCreateAppendFalse :=
  @Assembly.Program.usesCallCreate_append_eq_false

abbrev structuredCodeToAssemblyUsesCallCreate :=
  Structured.Code.toAssembly_usesCallCreate

abbrev structuredGeneratedSwapNoCallCreate :=
  @Structured.CompilerFacts.GeneratedNoCallCreate.swapInstr

abbrev structuredGeneratedDupNoCallCreate :=
  @Structured.CompilerFacts.GeneratedNoCallCreate.dupInstr

abbrev structuredGeneratedSinkNoCallCreate :=
  @Structured.CompilerFacts.GeneratedNoCallCreate.sinkTopUnder

abbrev structuredGeneratedLiftNoCallCreate :=
  @Structured.CompilerFacts.GeneratedNoCallCreate.liftBuriedToTop

abbrev structuredGeneratedRemoveNoCallCreate :=
  @Structured.CompilerFacts.GeneratedNoCallCreate.removeBuriedUnder

abbrev structuredGeneratedSwitchTestsNoCallCreate :=
  @Structured.CompilerFacts.GeneratedNoCallCreate.switchTests

abbrev structuredBlockCompileNoCallCreate :=
  @Structured.CompilerFacts.block_compileFromCtx_noCallCreate

abbrev structuredProcCompileBodyNoCallCreate :=
  @Structured.CompilerFacts.proc_compileBody_noCallCreate

abbrev structuredDispatchTestsNoCallCreate :=
  @Structured.CompilerFacts.dispatch_testsForRetc_noCallCreate

abbrev structuredDispatchCasesNoCallCreate :=
  @Structured.CompilerFacts.dispatch_casesForRetc_noCallCreate

abbrev structuredDispatchForProcNoCallCreate :=
  @Structured.CompilerFacts.dispatch_forProc_noCallCreate

abbrev structuredCompiledProcBodiesEmitNoCallCreate :=
  @Structured.CompilerFacts.compiledProcBodies_emit_noCallCreate

abbrev structuredProcBodiesCompileNoCallCreate :=
  @Structured.CompilerFacts.procBodies_compile_emit_noCallCreate

abbrev structuredProgramCompileNoCallCreate :=
  @Structured.CompilerFacts.program_compile_noCallCreate

abbrev expressionsCompileNoCallCreate :=
  @Expressions.CompilerFacts.Program.compile_noCallCreate

abbrev localsStackDupNoCallCreate :=
  @Locals.CompilerFacts.StackOp.dup?_not_callCreate

abbrev localsStackSwapNoCallCreate :=
  @Locals.CompilerFacts.StackOp.swap?_not_callCreate

abbrev localsCleanupToNoCallCreate :=
  @Locals.CompilerFacts.Ctx.cleanupTo?_noCallCreate

abbrev localsCleanupToPreservingNoCallCreate :=
  @Locals.CompilerFacts.Ctx.cleanupToPreserving?_noCallCreate

abbrev localsCleanupAllNoCallCreate :=
  @Locals.CompilerFacts.Ctx.cleanupAll_noCallCreate

abbrev localsExprCompileCodeNoCallCreate :=
  @Locals.CompilerFacts.Expr.compileCode_noCallCreate

abbrev localsExprSeqCompileCodeNoCallCreate :=
  @Locals.CompilerFacts.ExprSeq.compileCode_noCallCreate

abbrev localsCodeStmtNoCallCreate :=
  @Locals.CompilerFacts.codeStmt_noCallCreate

abbrev localsFinishScopedNoCallCreate :=
  @Locals.CompilerFacts.finishScoped_noCallCreate

abbrev localsBlockCompileOpenNoCallCreate :=
  @Locals.CompilerFacts.Block.compileOpen_noCallCreate

abbrev localsStmtCompileNoCallCreate :=
  @Locals.CompilerFacts.Stmt.compile_noCallCreate

abbrev localsCaseListCompileNoCallCreate :=
  @Locals.CompilerFacts.CaseList.compile_noCallCreate

abbrev localsDefaultCompileNoCallCreate :=
  @Locals.CompilerFacts.Default.compile_noCallCreate

abbrev localsBlockCompileToPreservingNoCallCreate :=
  @Locals.CompilerFacts.Block.compileToPreserving_noCallCreate

abbrev localsBlockCompileNoCallCreate :=
  @Locals.CompilerFacts.Block.compile_noCallCreate

abbrev localsProcToExpressionsNoCallCreate :=
  @Locals.CompilerFacts.Proc.toExpressions?_noCallCreate

abbrev localsProcListToExpressionsNoCallCreate :=
  @Locals.CompilerFacts.ProcList.toExpressions?_noCallCreate

abbrev localsProgramToExpressionsNoCallCreate :=
  @Locals.CompilerFacts.Program.toExpressions?_noCallCreate

abbrev localsProgramCompileNoCallCreate :=
  @Locals.CompilerFacts.Program.compile_noCallCreate

abbrev structuredCompileCheckedNoCallCreate :=
  @Structured.Preservation.ProcedurePreservation.compileChecked?_noCallCreate

abbrev expressionsCompileCheckedNoCallCreate :=
  @Expressions.Program.compileChecked?_noCallCreate

abbrev localsCompileCheckedNoCallCreate :=
  @Locals.Program.compileChecked?_noCallCreate

abbrev localsSourceCompileCheckedNoCallCreate :=
  @Locals.Source.Program.compileChecked?_noCallCreate

abbrev functionsToLocalsNoCallCreate :=
  @Functions.CompilerFacts.Program.toLocals_noCallCreate

abbrev functionsCompileCheckedNoCallCreate :=
  @Functions.Program.compileChecked?_noCallCreate

abbrev functionsSourceCompileCheckedNoCallCreate :=
  @Functions.Source.Program.compileChecked?_noCallCreate

abbrev objectsCompileCheckedNoCallCreate :=
  @Objects.Program.compileChecked?_noCallCreate

abbrev objectsSourceCompileCheckedNoCallCreate :=
  @Objects.Source.Program.compileChecked?_noCallCreate

abbrev yulCompileCheckedNoCallCreate :=
  @Yul.NoCallCreate.compileChecked?_noCallCreate

abbrev yulCompileCheckedAssemblyTargetNoCallCreate :=
  @Yul.Program.compileCheckedAssemblyTarget?_noCallCreate

abbrev externalInteractionNoCallCreate
    {program : Assembly.Program} {target : Assembly.TargetProgram}
    {initial : EvmYul.EVM.State} :
    program.usesCallCreate = false →
      Assembly.ExternalInteractionAssumption program target initial :=
  Assembly.ExternalInteractionAssumption.noCallCreate

abbrev runtimeAssumptionsNoCallCreate
    {program : Assembly.Program} {target : Assembly.TargetProgram}
    {initial : EvmYul.EVM.State} :
    Assembly.Bytecode.TargetFitsDecodeWindow target →
      Assembly.Bytecode.JumpdestCorrect target →
      Assembly.GasOracleAssumption program initial →
      Assembly.OutOfGasPolicyAssumption program initial →
      Assembly.CurrentContractProjectionAssumption program initial →
      program.usesCallCreate = false →
      Assembly.RuntimeAssumptions program target initial :=
  Assembly.RuntimeAssumptions.withNoCallCreate

abbrev recursiveBridgeTargetRuntimeNoCallCreate
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {initial : EvmYul.EVM.State} :
    Assembly.Bytecode.TargetFitsDecodeWindow target →
      Assembly.Bytecode.JumpdestCorrect target →
      Assembly.GasOracleAssumption asm initial →
      Assembly.OutOfGasPolicyAssumption asm initial →
      Assembly.CurrentContractProjectionAssumption asm initial →
      asm.usesCallCreate = false →
      initial.pc = Assembly.Program.pcAfter [] →
      initial.stack = [] →
      Yul.Program.RecursiveBridgeTargetRuntime asm target initial :=
  Yul.Program.RecursiveBridgeTargetRuntime.withNoCallCreate

abbrev recursiveBridgeTargetRuntimeAcceptedNoCallCreate
    {program : Yul.Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram} {initial : EvmYul.EVM.State} :
    Yul.Reference.Accepted program →
      Yul.Program.compileCheckedAssemblyTarget? program = some (asm, target) →
      Assembly.Bytecode.TargetFitsDecodeWindow target →
      Assembly.Bytecode.JumpdestCorrect target →
      Assembly.GasOracleAssumption asm initial →
      Assembly.OutOfGasPolicyAssumption asm initial →
      Assembly.CurrentContractProjectionAssumption asm initial →
      initial.pc = Assembly.Program.pcAfter [] →
      initial.stack = [] →
      Yul.Program.RecursiveBridgeTargetRuntime asm target initial :=
  Yul.Program.RecursiveBridgeTargetRuntime.withAcceptedNoCallCreate

abbrev codesizeRejectedByReferenceBridge :=
  Yul.Reference.Safe.rejects_codesize

abbrev codesizeAcceptedByFullReferenceSurface :=
  Yul.Reference.Safe.Full.accepts_codesize

abbrev codecopyRejectedByReferenceBridge :=
  Yul.Reference.Safe.rejects_codecopy

abbrev codecopyAcceptedByFullReferenceSurface :=
  Yul.Reference.Safe.Full.accepts_codecopy

abbrev extcodesizeRejectedByReferenceBridge :=
  Yul.Reference.Safe.rejects_extcodesize

abbrev extcodesizeAcceptedByFullReferenceSurface :=
  Yul.Reference.Safe.Full.accepts_extcodesize

abbrev extcodecopyRejectedByReferenceBridge :=
  Yul.Reference.Safe.rejects_extcodecopy

abbrev extcodecopyAcceptedByFullReferenceSurface :=
  Yul.Reference.Safe.Full.accepts_extcodecopy

abbrev extcodehashRejectedByReferenceBridge :=
  Yul.Reference.Safe.rejects_extcodehash

abbrev extcodehashAcceptedByFullReferenceSurface :=
  Yul.Reference.Safe.Full.accepts_extcodehash

abbrev sstoreAcceptedByReferenceBridge :=
  Yul.Reference.Safe.accepts_sstore

abbrev tstoreAcceptedByReferenceBridge :=
  Yul.Reference.Safe.accepts_tstore

abbrev log0AcceptedByReferenceBridge :=
  Yul.Reference.Safe.accepts_log0

abbrev log1AcceptedByReferenceBridge :=
  Yul.Reference.Safe.accepts_log1

abbrev log2AcceptedByReferenceBridge :=
  Yul.Reference.Safe.accepts_log2

abbrev log3AcceptedByReferenceBridge :=
  Yul.Reference.Safe.accepts_log3

abbrev log4AcceptedByReferenceBridge :=
  Yul.Reference.Safe.accepts_log4

namespace OneConstructFacts

abbrev evalLit :=
  @Yul.Reference.Imported.eval_lit_succ

abbrev evalVar :=
  @Yul.Reference.Imported.eval_var_succ

abbrev execEmptyBlock :=
  @Yul.Reference.Imported.exec_block_nil_succ

abbrev selectSwitchCaseEmpty :=
  @Yul.Reference.Imported.select_switch_case_nil

abbrev selectSwitchCaseCons :=
  @Yul.Reference.Imported.select_switch_case_cons

abbrev execLetWithoutValue :=
  @Yul.Reference.Imported.exec_let_none_succ

abbrev execLetLiteral :=
  @Yul.Reference.Imported.exec_let_lit_succ

abbrev execLetVariable :=
  @Yul.Reference.Imported.exec_let_var_succ

abbrev execAssign :=
  @Yul.Reference.Imported.exec_assign_succ

abbrev evalArgsEmpty :=
  @Yul.Reference.Imported.evalArgs_nil_succ

abbrev evalArgsCons :=
  @Yul.Reference.Imported.evalArgs_cons_succ

abbrev evalTailEmptyOk :=
  @Yul.Reference.Imported.evalTail_nil_ok_succ

abbrev evalPrimitiveCall :=
  @Yul.Reference.Imported.eval_prim_call_succ

abbrev evalUserCall :=
  @Yul.Reference.Imported.eval_user_call_succ

abbrev execBlockCons :=
  @Yul.Reference.Imported.exec_block_cons_succ

abbrev execSeqNil :=
  @Yul.Reference.Imported.execSeq_nil_succ

abbrev execSeqConsOk :=
  @Yul.Reference.Imported.execSeq_cons_ok_succ

abbrev execSeqConsOkResult :=
  @Yul.Reference.Imported.execSeq_cons_ok_result_succ

abbrev execSeqConsCheckpoint :=
  @Yul.Reference.Imported.execSeq_cons_checkpoint_succ

abbrev execSeqConsOutOfFuel :=
  @Yul.Reference.Imported.execSeq_cons_outOfFuel_succ

abbrev execSeqConsError :=
  @Yul.Reference.Imported.execSeq_cons_error_succ

abbrev execSeqSingle :=
  @Yul.Reference.Imported.execSeq_single_succ

abbrev execIf :=
  @Yul.Reference.Imported.exec_if_succ

abbrev execSwitch :=
  @Yul.Reference.Imported.exec_switch_succ

abbrev execSwitchEmptyDefault :=
  @Yul.Reference.Imported.exec_switch_empty_default_succ_succ

abbrev execPrimitiveExpressionStatement :=
  @Yul.Reference.Imported.exec_expr_prim_call_succ

abbrev execReturnZeroZeroExpressionStatement :=
  @Yul.Reference.Imported.exec_expr_return_zero_zero_succ6

abbrev execRevertZeroZeroExpressionStatement :=
  @Yul.Reference.Imported.exec_expr_revert_zero_zero_succ6

abbrev returnLitLitSourceState :=
  @Yul.Reference.Imported.returnLitLitSourceState

abbrev revertLitLitSourceState :=
  @Yul.Reference.Imported.revertLitLitSourceState

abbrev execReturnLitLitExpressionStatement :=
  @Yul.Reference.Imported.exec_expr_return_lit_lit_succ6

abbrev execRevertLitLitExpressionStatement :=
  @Yul.Reference.Imported.exec_expr_revert_lit_lit_succ6

abbrev selfdestructZeroSourceState :=
  @Yul.Reference.Imported.selfdestructZeroSourceState

abbrev yulStepSelfdestructZero :=
  @Yul.Reference.Imported.yul_step_selfdestruct_zero_eq

abbrev execSelfdestructZeroExpressionStatement :=
  @Yul.Reference.Imported.exec_expr_selfdestruct_zero_succ4

abbrev execSelfdestructZeroStaticExpressionStatement :=
  @Yul.Reference.Imported.exec_expr_selfdestruct_zero_static_succ4

abbrev execUserExpressionStatement :=
  @Yul.Reference.Imported.exec_expr_user_call_succ

abbrev execPrimitiveLet :=
  @Yul.Reference.Imported.exec_let_prim_call_succ

abbrev execUserLet :=
  @Yul.Reference.Imported.exec_let_user_call_succ

abbrev execFor :=
  @Yul.Reference.Imported.exec_for_succ

abbrev loopOutOfFuelZero :=
  @Yul.Reference.Imported.loop_zero

abbrev loopOutOfFuelOne :=
  @Yul.Reference.Imported.loop_one

abbrev loopSuccSucc :=
  @Yul.Reference.Imported.loop_succ_succ

abbrev callDispatcherOutOfFuel :=
  @Yul.Reference.Imported.callDispatcher_zero

abbrev callDispatcherSucc :=
  @Yul.Reference.Imported.callDispatcher_succ

abbrev evalPrimCallError :=
  @Yul.Reference.Imported.evalPrimCall_error

abbrev evalPrimCallOk :=
  @Yul.Reference.Imported.evalPrimCall_ok

abbrev execPrimCallError :=
  @Yul.Reference.Imported.execPrimCall_error

abbrev execPrimCallOk :=
  @Yul.Reference.Imported.execPrimCall_ok

abbrev evalCallError :=
  @Yul.Reference.Imported.evalCall_error

abbrev evalCallOutOfFuel :=
  @Yul.Reference.Imported.evalCall_ok_zero

abbrev evalCallSucc :=
  @Yul.Reference.Imported.evalCall_ok_succ

abbrev execCallError :=
  @Yul.Reference.Imported.execCall_error

abbrev execCallOutOfFuel :=
  @Yul.Reference.Imported.execCall_ok_zero

abbrev execCallSucc :=
  @Yul.Reference.Imported.execCall_ok_succ

abbrev execBreak :=
  @Yul.Reference.Imported.exec_break_succ

abbrev execContinue :=
  @Yul.Reference.Imported.exec_continue_succ

abbrev execLeave :=
  @Yul.Reference.Imported.exec_leave_succ

end OneConstructFacts

end ImportedYulBoundary

end LayerAudit
end EvmCompiler
