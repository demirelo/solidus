import EvmCompiler.Yul.NoCallRuntime
import EvmCompiler.Yul.Preservation
import EvmCompiler.Functions.Preservation
import EvmCompiler.Functions.LiveLayout
import EvmCompiler.Locals.SourceLowering

/-!
Independently checkable stack-guard proof pins.

`LayerAudit` also pins these facts in the public theorem spine, but it currently
imports the CALL boundary first.  This module deliberately avoids that surface
so stack-resource, adaptive-spill, and conservative-spill facts can be checked
while CALL support is being refactored in parallel.
-/

namespace EvmCompiler
namespace StackGuardAudit

noncomputable section

namespace FunctionFrameWordSumChecker

/-!
The source-side stack resource checker uses accumulated hidden-return frame
words along each active call path, not the older uniform `17 * depth` product.
These pins keep the exact checker surface visible independently of the
Yul-facing compile wrappers below.
-/

example :=
  Functions.CallDepth.Program.maxActiveFrameWords?

example :=
  @Functions.CallDepth.Program.maxActiveFrameWords?_sound

example :=
  Functions.CallDepth.Program.stackFrameWordSumBudgetOk?

example :=
  Functions.CallDepth.Program.stackFrameWordSumVisibleBudgetOk?

example :=
  Functions.CallDepth.Program.stackFrameWordSumCheck?

example :=
  Functions.CallDepth.Program.stackFrameWordSumVisibleCheck?

example :=
  @Functions.CallDepth.Program.stackFrameWordSumCheck?_eq_some

example :=
  @Functions.CallDepth.Program.stackFrameWordSumVisibleCheck?_eq_some

example :=
  @Functions.CallDepth.Program.StackFrameWordSumCheckResult.path_words_bound

example :=
  @Functions.CallDepth.Program.StackFrameWordSumVisibleCheckResult.path_words_bound

example :=
  @Functions.CallDepth.Program.ActiveCallFrameWords.words_le_check

example :=
  @Functions.CallDepth.Program.ActiveCallFrameWords.words_le_visible_check

example :=
  @Functions.CallDepth.ActiveHiddenFrameWordsContext.returnStackWeight_le_check

example :=
  @Functions.CallDepth.ActiveHiddenFrameWordsContext.returnStackWeight_le_visible_check

example :=
  @Functions.CallDepth.ActiveHiddenFrameWordsContext.callersWordsLe_programMax

example :=
  @Functions.CallDepth.ActiveHiddenFrameWordsContext.sourceStackHeadroom_of_visible_check

example :=
  @Functions.CallDepth.ActiveHiddenFrameWordsContext.sourceStackHeadroom_of_sourceDirectStateRel_visible_check

example :=
  @Functions.CallDepth.ActiveHiddenFrameWordsContext.sourceStackHeadroom_of_sourceDirectStateRel_layout_check

example :=
  @Functions.CallDepth.SourceDirectWeightedFrameContext.returnStackWeight_le_checked_frameWords

example :=
  @Functions.CallDepth.SourceDirectWeightedFrameContext.toFrameWordsContextProgramMax

example :=
  @Functions.CallDepth.SourceDirectWeightedFrameContext.returnStackWeight_le_visible_checked_frameWords

example :=
  @Functions.CallDepth.SourceDirectWeightedFrameContext.sourceStackWeight_le_layout_plus_checked_frameWords

example :=
  @Functions.CallDepth.SourceDirectWeightedFrameContext.sourceStackWeight_le_layout_plus_visible_checked_frameWords

example :=
  @Functions.CallDepth.SourceDirectWeightedFrameContext.sourceStackWeight_le_checked_frameWords

example :=
  @Functions.CallDepth.SourceDirectWeightedFrameContext.sourceStackHeadroom_of_layout_budget

example :=
  @Functions.CallDepth.SourceDirectWeightedFrameContext.sourceStackHeadroom_of_visible_check

example :=
  @Functions.CallDepth.SourceDirectWeightedFrameContext.sourceStackHeadroom_of_layout_check

example :=
  @Functions.CallDepth.SourceFrameWordSumResourceBound.checked

example :=
  @Functions.CallDepth.SourceFrameWordSumResourceBound.budget

example :=
  @Functions.CallDepth.SourceFrameWordSumResourceBound.sourceStackHeadroom_of_weightedContext

example :=
  @Functions.CallDepth.SourceFrameWordSumResourceBound.sourceStackHeadroom_of_weightedContext_layout_budget

example :=
  @Functions.CallDepth.SourceFrameWordSumResourceBound.returnStackWeight_le_checked_frameWords_of_weightedContext

example :=
  @Functions.CallDepth.SourceFrameWordSumResourceBound.sourceStackWeight_le_layout_plus_checked_frameWords_of_weightedContext

example :=
  @Functions.CallDepth.SourceFrameWordSumResourceBound.sourceStackWeight_le_checked_frameWords_of_weightedContext

example :=
  @Functions.CallDepth.SourceFrameWordSumVisibleResourceBound.checked

example :=
  @Functions.CallDepth.SourceFrameWordSumVisibleResourceBound.budget

example :=
  @Functions.CallDepth.SourceFrameWordSumVisibleResourceBound.sourceStackHeadroom_of_weightedContext

example :=
  @Functions.CallDepth.SourceFrameWordSumVisibleResourceBound.sourceStackHeadroom_of_weightedContext_layout_check

example :=
  @Functions.CallDepth.SourceFrameWordSumVisibleResourceBound.returnStackWeight_le_checked_frameWords_of_weightedContext

example :=
  @Functions.CallDepth.SourceFrameWordSumVisibleResourceBound.sourceStackWeight_le_layout_plus_checked_frameWords_of_weightedContext

example :=
  Functions.CallDepth.Program.sourceFrameWordSumResourceBound?

example :=
  @Functions.CallDepth.Program.sourceFrameWordSumResourceBound?_eq_some

example :=
  @Functions.CallDepth.Program.sourceFrameWordSumResourceBound?_sound

example :=
  Functions.CallDepth.Program.sourceFrameWordSumVisibleResourceBound?

example :=
  @Functions.CallDepth.Program.sourceFrameWordSumVisibleResourceBound?_eq_some

example :=
  @Functions.CallDepth.Program.sourceFrameWordSumVisibleResourceBound?_sound

example :=
  Yul.Program.RecursiveBridgeExecutableFrameWordSumVisibleStackCheckResult

example :=
  Yul.Program.RecursiveBridgeExecutableFrameWordSumLiveLayoutStackCheckResult

example :=
  Yul.Program.RecursiveBridgeSourceFrameWordSumVisibleResourceBound

example :=
  Yul.Program.recursiveBridgeExecutableFrameWordSumVisibleStackCheck?

example :=
  Yul.Program.recursiveBridgeExecutableFrameWordSumLiveLayoutStackCheck?

example :=
  @Yul.Program.recursiveBridgeExecutableFrameWordSumVisibleStackCheck?_checked

example :=
  @Yul.Program.recursiveBridgeExecutableFrameWordSumLiveLayoutStackCheck?_checked

example :=
  @Yul.Program.RecursiveBridgeExecutableFrameWordSumVisibleStackCheckResult.toSourceFrameWordSumVisibleResourceBound

example :=
  @Yul.Program.RecursiveBridgeExecutableFrameWordSumLiveLayoutStackCheckResult.toSourceFrameWordSumVisibleResourceBound

example :=
  @Yul.Program.RecursiveBridgeExecutableFrameWordSumLiveLayoutStackCheckResult.body_layoutsBoundedBy

example :=
  @Yul.Program.RecursiveBridgeExecutableFrameWordSumVisibleStackCheckResult.sourceStackHeadroom_of_weightedContext

example :=
  @Yul.Program.RecursiveBridgeExecutableFrameWordSumLiveLayoutStackCheckResult.sourceStackHeadroom_of_weightedContext

example :=
  @Yul.Program.RecursiveBridgeExecutableFrameWordSumLiveLayoutStackCheckResult.sourceStackWeight_le_visible_frameWords_of_weightedContext

example :=
  @Yul.Program.RecursiveBridgeSourceDirectFrameWordSumLiveLayoutPoint

example :=
  @Yul.Program.RecursiveBridgeSourceDirectFrameWordSumLiveLayoutPoint.of_context

example :=
  @Yul.Program.RecursiveBridgeSourceDirectFrameWordSumLiveLayoutPoint.of_main

example :=
  @Yul.Program.RecursiveBridgeSourceDirectFrameWordSumLiveLayoutPoint.of_withStateRel

example :=
  @Yul.Program.RecursiveBridgeSourceDirectFrameWordSumLiveLayoutPoint.of_withStateRelLayout

example :=
  @Yul.Program.RecursiveBridgeSourceDirectFrameWordSumLiveLayoutPoint.of_regularBlockScopedOutcomeRel

example :=
  @Yul.Program.RecursiveBridgeSourceDirectFrameWordSumLiveLayoutPoint.of_regularStmtRunResultRel

example :=
  @Yul.Program.RecursiveBridgeSourceDirectFrameWordSumLiveLayoutPoint.of_regularBlockOpenResultRel

example :=
  @Yul.Program.RecursiveBridgeSourceDirectFrameWordSumLiveLayoutPoint.sourceStackHeadroom

example :=
  @Yul.Program.RecursiveBridgeSourceDirectFrameWordSumLiveLayoutPoint.point_sourceStackHeadroom

example :=
  @Yul.Program.RecursiveBridgeSourceDirectFrameWordSumLiveLayoutPoint.to_stack_headroom

example :=
  @Yul.Program.RecursiveBridgeSourceDirectFrameWordSumLiveLayoutPoint.point_sourceStackWeight_le_visible_frameWords

example :=
  @Yul.Program.RecursiveBridgeSourceDirectFrameWordSumLiveLayoutPoint.initial

example :=
  @Yul.Program.RecursiveBridgeActualBlockTraceSourceStackHeadroom.of_frameWordSumLiveLayoutPoints

example :=
  @Yul.Program.RecursiveBridgeActualSourceRunFrameStackHeadroom.toEVMStackHeadroomBound

example :=
  @Yul.Program.RecursiveBridgeActualSourceRunFrameWordSumLiveLayoutPoints

example :=
  @Yul.Program.RecursiveBridgeActualSourceRunFrameWordSumLiveLayoutPoints.toFrameStackHeadroom

example :=
  @Yul.Program.RecursiveBridgeActualSourceRunFrameWordSumLiveLayoutPoints.toEVMStackHeadroomPoints

example :=
  @Yul.Program.RecursiveBridgeActualSourceRunFrameWordSumLiveLayoutPoints.toEVMStackHeadroomBound

example :=
  @Yul.Program.RecursiveBridgeActualSourceRunFrameWordSumLiveLayoutPoints.toWeightPoints

example :=
  @Yul.Program.RecursiveBridgeActualSourceRunFrameWordSumLiveLayoutWeightPoints

example :=
  @Yul.Program.RecursiveBridgeActualSourceRunFrameWordSumLiveLayoutWeightPoints.toEVMStackHeadroomPoints

example :=
  @Yul.Program.RecursiveBridgeActualSourceRunFrameWordSumLiveLayoutWeightPoints.toEVMStackHeadroomBound

example :=
  @Yul.Program.RecursiveBridgeActualSourceRunFrameWordSumLiveLayoutPoints.of_runNResult_invariant

example :=
  @Yul.Program.RecursiveBridgeActualSourceRunFrameWordSumLiveLayoutPoints.of_runNResult_invariant_initial

example :=
  @Yul.Program.RecursiveBridgeExecutableFrameWordSumVisibleStackCheckResult.sourceStackHeadroom_of_weightedContext_layout_check

example :=
  @Yul.Program.recursiveBridgeExecutableFrameWordSumVisibleStackCheck?_sound

example :=
  @Yul.Program.recursiveBridgeExecutableFrameWordSumLiveLayoutStackCheck?_sound

example :=
  @Yul.Program.RecursiveBridgeSourceFrameWordSumVisibleResourceBound.checked

example :=
  @Yul.Program.RecursiveBridgeSourceFrameWordSumVisibleResourceBound.budget

example :=
  @Yul.Program.RecursiveBridgeSourceFrameWordSumVisibleResourceBound.sourceStackHeadroom_of_weightedContext

example :=
  @Yul.Program.RecursiveBridgeSourceFrameWordSumVisibleResourceBound.sourceStackHeadroom_of_weightedContext_layout_check

end FunctionFrameWordSumChecker

namespace LiveLayoutWidthChecker

/-!
The live-layout route now has an executable width-annotated checker that mirrors
`Checked.check?`.  These pins keep the computed max-live-layout-width boundary
visible while the public frame-word gate is being moved away from the coarse
global `16` visible-stack bound.
-/

example :=
  Functions.LiveLayout.Checked.LayoutWidthCheckResult

example :=
  Functions.LiveLayout.Checked.Block.widthCheck?

example :=
  Functions.LiveLayout.Checked.Stmt.widthCheck?

example :=
  Functions.LiveLayout.Checked.StmtList.widthCheck?

example :=
  Functions.LiveLayout.Checked.CaseList.widthCheck?

example :=
  Functions.LiveLayout.Checked.Default.widthCheck?

example :=
  Functions.LiveLayout.Checked.FunDef.maxLiveLayoutWidth?

example :=
  Functions.LiveLayout.Checked.FunList.maxLiveLayoutWidth?

example :=
  Functions.LiveLayout.Checked.Program.maxLiveLayoutWidth?

example :=
  @Functions.LiveLayout.Checked.Block.widthCheck?_sound

example :=
  @Functions.LiveLayout.Checked.Stmt.widthCheck?_sound

example :=
  @Functions.LiveLayout.Checked.StmtList.widthCheck?_sound

example :=
  @Functions.LiveLayout.Checked.CaseList.widthCheck?_sound

example :=
  @Functions.LiveLayout.Checked.Default.widthCheck?_sound

example :=
  @Functions.LiveLayout.Checked.FunDef.maxLiveLayoutWidth?_check?

example :=
  @Functions.LiveLayout.Checked.FunList.maxLiveLayoutWidth?_check?

example :=
  @Functions.LiveLayout.Checked.Program.maxLiveLayoutWidth?_check?

example :=
  @Functions.LiveLayout.Checked.Block.LayoutsBoundedBy

example :=
  @Functions.LiveLayout.Checked.Stmt.LayoutsBoundedBy

example :=
  @Functions.LiveLayout.Checked.StmtList.LayoutsBoundedBy

example :=
  @Functions.LiveLayout.Checked.CaseList.LayoutsBoundedBy

example :=
  @Functions.LiveLayout.Checked.Default.LayoutsBoundedBy

example :=
  @Functions.LiveLayout.Checked.Block.layoutsBoundedBy_layout_length_le

example :=
  @Functions.LiveLayout.Checked.Stmt.layoutsBoundedBy_layout_length_le

example :=
  @Functions.LiveLayout.Checked.StmtList.layoutsBoundedBy_layout_length_le

example :=
  @Functions.LiveLayout.Checked.CaseList.layoutsBoundedBy_layout_length_le

example :=
  @Functions.LiveLayout.Checked.Default.layoutsBoundedBy_layout_length_le

example :=
  @Functions.LiveLayout.Checked.Block.widthCheck?_layoutsBoundedBy

example :=
  @Functions.LiveLayout.Checked.Stmt.widthCheck?_layoutsBoundedBy

example :=
  @Functions.LiveLayout.Checked.StmtList.widthCheck?_layoutsBoundedBy

example :=
  @Functions.LiveLayout.Checked.CaseList.widthCheck?_layoutsBoundedBy

example :=
  @Functions.LiveLayout.Checked.Default.widthCheck?_layoutsBoundedBy

example :=
  @Functions.LiveLayout.Checked.Block.widthCheck?_layoutsBoundedBy_self

example :=
  @Functions.LiveLayout.Checked.Program.maxLiveLayoutWidth?_body_layoutsBoundedBy

end LiveLayoutWidthChecker

namespace SourceFrameWordSumBoundary

/-!
The no-internal-CALL imported-Yul route uses the executable exact
frame-word-sum plus live-layout checker.  Compile success exposes the lowered
object program, checked visible live-layout width, checked hidden frame words,
and the exact `visibleWords + frameWords + 17 <= 1024` capacity bound.
-/

example :=
  Yul.Program.compileLiveNoInternalCallCheckedAssemblyTargetBytecodeFeaturesSourceStaticExecutableAssemblyInferredBoundFrameWordSumLiveLayoutStackSafeNoReturnDataCopy?

example :=
  @Yul.Program.compileLiveNoInternalCallCheckedAssemblyTargetBytecodeFeaturesSourceStaticExecutableAssemblyInferredBoundFrameWordSumLiveLayoutStackSafeNoReturnDataCopy?_eq_some

example :=
  @Yul.Program.compileLiveNoInternalCallCheckedAssemblyTargetBytecodeFeaturesSourceStaticExecutableAssemblyInferredBoundFrameWordSumLiveLayoutStackSafeNoReturnDataCopy?_of_checks

example :=
  @Yul.Program.compileLiveNoInternalCallCheckedAssemblyTargetBytecodeFeaturesSourceStaticExecutableAssemblyInferredBoundFrameWordSumLiveLayoutStackSafeNoReturnDataCopy?_base

example :=
  @Yul.Program.compileLiveNoInternalCallCheckedAssemblyTargetBytecodeFeaturesSourceStaticExecutableAssemblyInferredBoundFrameWordSumLiveLayoutStackSafeNoReturnDataCopy?_stackSafeCompile

example :=
  @Yul.Program.compileLiveNoInternalCallCheckedAssemblyTargetBytecodeFeaturesSourceStaticExecutableAssemblyInferredBoundFrameWordSumLiveLayoutStackSafeNoReturnDataCopy?_sourceCheck

example :=
  @Yul.Program.compileLiveNoInternalCallCheckedAssemblyTargetBytecodeFeaturesSourceStaticExecutableAssemblyInferredBoundFrameWordSumLiveLayoutStackSafeNoReturnDataCopy?_sourceCheck_checked

example :=
  @Yul.Program.compileLiveNoInternalCallCheckedAssemblyTargetBytecodeFeaturesSourceStaticExecutableAssemblyInferredBoundFrameWordSumLiveLayoutStackSafeNoReturnDataCopy?_sourceFrameWordSumVisibleResourceBound

example :=
  @Yul.Program.compileLiveNoInternalCallCheckedAssemblyTargetBytecodeFeaturesSourceStaticExecutableAssemblyInferredBoundFrameWordSumLiveLayoutStackSafeNoReturnDataCopy?_sourceFrameWordSumLiveLayoutExactBound

example :=
  @Yul.Program.compileLiveNoInternalCallCheckedAssemblyTargetBytecodeFeaturesSourceStaticExecutableAssemblyInferredBoundFrameWordSumLiveLayoutStackSafeNoReturnDataCopy?_body_layoutsBoundedBy

example :=
  @Yul.Program.compileLiveNoInternalCallCheckedAssemblyTargetBytecodeFeaturesSourceStaticExecutableAssemblyInferredBoundFrameWordSumLiveLayoutStackSafeNoReturnDataCopy?_assemblyBoundCheck

example :=
  @Yul.Program.compileLiveNoInternalCallCheckedAssemblyTargetBytecodeFeaturesSourceStaticExecutableAssemblyInferredBoundFrameWordSumLiveLayoutStackSafeNoReturnDataCopy?_assemblyBoundCheck_checked

example :=
  @Yul.Program.compileLiveNoInternalCallCheckedAssemblyTargetBytecodeFeaturesSourceStaticExecutableAssemblyInferredBoundFrameWordSumLiveLayoutStackSafeNoReturnDataCopy?_actualEVMStackHeadroomBound

example :=
  @Yul.Program.liveLayoutStackSafe_actualEVMHeadroomPoints

example :=
  @Yul.Program.compileLiveNoInternalCallCheckedAssemblyTargetBytecodeFeaturesSourceStaticExecutableAssemblyInferredBoundFrameWordSumLiveLayoutStackSafeNoReturnDataCopy?_actualEVMStackHeadroomBound_of_sourceRunFrameWordSumLiveLayoutPoints

example :=
  @Yul.Program.compileLiveNoInternalCallCheckedAssemblyTargetBytecodeFeaturesSourceStaticExecutableAssemblyInferredBoundFrameWordSumLiveLayoutStackSafeNoReturnDataCopy?_actualEVMStackHeadroomBound_of_sourceRunFrameWordSumLiveLayoutWeightPoints

example :=
  @Yul.Program.compileLiveNoInternalCallCheckedAssemblyTargetBytecodeFeaturesSourceStaticExecutableAssemblyInferredBoundFrameWordSumLiveLayoutStackSafeNoReturnDataCopy?_actualEVMStackHeadroomBound_of_sourceRunFrameStackHeadroom

example
    {program : Yul.Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    (hCheckedCompileTarget :
      Yul.Program.compileLiveNoInternalCallCheckedAssemblyTargetBytecodeFeaturesSourceStaticExecutableAssemblyInferredBoundFrameWordSumStackSafeNoReturnDataCopy?
          program =
        some (asm, target)) :
    Yul.Program.RecursiveBridgeSourceFrameWordSumResourceBound program :=
  Yul.Program.compileLiveNoInternalCallCheckedAssemblyTargetBytecodeFeaturesSourceStaticExecutableAssemblyInferredBoundFrameWordSumStackSafeNoReturnDataCopy?_sourceFrameWordSumResourceBound
    hCheckedCompileTarget

example
    {program : Yul.Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    (hCheckedCompileTarget :
      Yul.Program.compileLiveNoInternalCallCheckedAssemblyTargetBytecodeFeaturesSourceStaticExecutableAssemblyInferredBoundFrameWordSumStackSafeNoReturnDataCopy?
          program =
        some (asm, target)) :
    ∃ lowerObj frameWords,
      program.toObjects? = some lowerObj ∧
        Functions.CallDepth.Program.maxActiveFrameWords?
            lowerObj.toFunctions =
          some frameWords ∧
        16 + frameWords + 17 ≤ 1024 :=
  Yul.Program.compileLiveNoInternalCallCheckedAssemblyTargetBytecodeFeaturesSourceStaticExecutableAssemblyInferredBoundFrameWordSumStackSafeNoReturnDataCopy?_sourceFrameWordSumExactBound
    hCheckedCompileTarget

example
    {program : Yul.Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    (hCheckedCompileTarget :
      Yul.Program.compileLiveNoInternalCallCheckedAssemblyTargetBytecodeFeaturesSourceStaticExecutableAssemblyInferredBoundFrameWordSumStackSafeNoReturnDataCopy?
          program =
        some (asm, target)) :
    _root_.EvmCompiler.Structured.StackResource.AssemblyBounds.inferProgramBoundCheckResult?
        asm 17 1024 =
      some
        (Yul.Program.compileLiveNoInternalCallCheckedAssemblyTargetBytecodeFeaturesSourceStaticExecutableAssemblyInferredBoundFrameWordSumStackSafeNoReturnDataCopy?_assemblyBoundCheck
          hCheckedCompileTarget) :=
  Yul.Program.compileLiveNoInternalCallCheckedAssemblyTargetBytecodeFeaturesSourceStaticExecutableAssemblyInferredBoundFrameWordSumStackSafeNoReturnDataCopy?_assemblyBoundCheck_checked
    hCheckedCompileTarget

example
    {program : Yul.Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    (hCheckedCompileTarget :
      Yul.Program.compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundFrameWordSumStackSafeNoReturnDataCopy?
          program =
        some (asm, target)) :
    Yul.Program.RecursiveBridgeSourceFrameWordSumResourceBound program :=
  Yul.Program.compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundFrameWordSumStackSafeNoReturnDataCopy?_sourceFrameWordSumResourceBound
    hCheckedCompileTarget

example
    {program : Yul.Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    (hCheckedCompileTarget :
      Yul.Program.compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundFrameWordSumStackSafeNoReturnDataCopy?
          program =
        some (asm, target)) :
    ∃ lowerObj frameWords,
      program.toObjects? = some lowerObj ∧
        Functions.CallDepth.Program.maxActiveFrameWords?
            lowerObj.toFunctions =
          some frameWords ∧
        16 + frameWords + 17 ≤ 1024 :=
  Yul.Program.compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundFrameWordSumStackSafeNoReturnDataCopy?_sourceFrameWordSumExactBound
    hCheckedCompileTarget

example
    {program : Yul.Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    (hCheckedCompileTarget :
      Yul.Program.compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundFrameWordSumStackSafeNoReturnDataCopy?
          program =
        some (asm, target)) :
    _root_.EvmCompiler.Structured.StackResource.AssemblyBounds.inferProgramBoundCheckResult?
        asm 17 1024 =
      some
        (Yul.Program.compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundFrameWordSumStackSafeNoReturnDataCopy?_assemblyBoundCheck
          hCheckedCompileTarget) :=
  Yul.Program.compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundFrameWordSumStackSafeNoReturnDataCopy?_assemblyBoundCheck_checked
    hCheckedCompileTarget

end SourceFrameWordSumBoundary

namespace LiveLayoutPreservationBoundary

/-!
Successful live-layout no-internal-CALL compilation is not just a checker
artifact: it is threaded through Functions, Objects, and the Yul source-lowered
adapter as an ordinary preservation theorem.  These pins keep that final
top-16 compile-around route visible next to the frame-word-sum stack gate.
-/

example :=
  @Functions.LiveLayout.SourceTarget.Program.compileLiveNoInternalCallChecked_preserves

example :=
  @Functions.LiveLayout.SourceTarget.Program.compileLiveNoInternalCallChecked_preserves_endPc

example :=
  @Objects.Source.Program.compile_live_noInternalCall_preserves_checked

example :=
  @Objects.Source.Program.compile_live_noInternalCall_preserves_checked_endPc

example :=
  @Yul.Program.compile_live_noInternalCall_source_preserves_checked

example :=
  @Yul.Program.compile_live_noInternalCall_source_preserves_checked_endPc

example :=
  @Yul.Program.compile_live_noInternalCall_source_preserves_checked_anyFuel

example :=
  @Yul.Program.compile_live_noInternalCall_source_preserves_checked_endPc_anyFuel

end LiveLayoutPreservationBoundary

namespace LiveLayoutRegressionBoundary

/-!
The exact live-layout route is the non-scratch compile-around path for many
ordinary "stack too deep" cases.  These regression pins show a deep local that
is outside the top-16 window before dead-prefix trimming, then accepted by the
checked live-layout lowering pipeline.
-/

theorem deadPrefixEntryWindowOk :
    Functions.LiveLayout.Layout.entryWindowOk?
      (List.replicate 17 "dead" ++ ["x"]) ["x"] = true := by
  native_decide

theorem deepVarInaccessibleBeforeTrim :
    Functions.LiveLayout.ExprAccess.expr? 0
      (List.replicate 17 "dead" ++ ["x"])
      (.var "x") = false := by
  native_decide

theorem deepVarAccessibleAfterTrim :
    Functions.LiveLayout.ExprAccess.expr? 0
      (Functions.LiveLayout.Layout.trimDeadPrefix
        (List.replicate 17 "dead" ++ ["x"]) ["x"])
      (.var "x") = true := by
  native_decide

theorem manyDeadProgram_checked :
    Functions.LiveLayout.Checked.Program.check?
      Functions.LiveLayout.Examples.manyDeadProgram = true := by
  native_decide

theorem manyDeadProgram_toLocals_accepts :
    (Functions.LiveLayout.Lower.Program.toLocals?
      Functions.LiveLayout.Examples.manyDeadProgram).isSome = true := by
  native_decide

theorem manyDeadProgram_toExpressions_accepts :
    (Functions.LiveLayout.Lower.Program.toExpressions?
      Functions.LiveLayout.Examples.manyDeadProgram).isSome = true := by
  native_decide

end LiveLayoutRegressionBoundary

namespace AdaptiveSpillBoundary

/-!
The adaptive atom route is the less conservative top-16 fallback: it first tries
ordinary stack compilation, then spills one stack local at a time only until the
same atom compiles.  The public wrapper hides generated spill plans and
expressions programs while keeping compile decomposition, no-CALL, and
source-run soundness visible independently of the broader spill-all route.
-/

example :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileFreshAtomWithAdaptiveSpill?

example :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileStmtListWithAdaptiveSpill?

example :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockOpenWithAdaptiveSpill?

example :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileFreshAtomWithAdaptiveSpill?_swap17Regression_accepts

example :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockOpenWithAdaptiveSpill?_deepLocalsRegression_accepts

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileFreshAtomWithAdaptiveSpill?_wellFormed

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileFreshAtomWithAdaptiveSpill?_of_compileFreshAtom?

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileFreshAtomWithAdaptiveSpill?_isSome_of_compileFreshAtomWithSpill?

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileFreshAtomWithAdaptiveSpill?_noCallCreate

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileFreshAtomWithAdaptiveSpill?_sourceScope_outEnv

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileFreshAtomWithAdaptiveSpill?_sound_of_source_run

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileFreshAtomWithAdaptiveSpill?_regular_storeDefined_of_source_run

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileFreshAtomWithAdaptiveSpill?_backendSafe

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileStmtListWithAdaptiveSpill?_wellFormed

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileStmtListWithAdaptiveSpill?_of_compileStmtList?

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileStmtListWithAdaptiveSpill?_noCallCreate

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileStmtListWithAdaptiveSpill?_sound_of_source_run

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileStmtListWithAdaptiveSpill?_backendSafe

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockOpenWithAdaptiveSpill?_wellFormed

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockOpenWithAdaptiveSpill?_of_compileBlockOpen?

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockOpenWithAdaptiveSpill?_noCallCreate

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockOpenWithAdaptiveSpill?_sound_of_source_run

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockOpenWithAdaptiveSpill?_backendSafe

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockOpenWithAdaptiveSpill?_expressionsBlock_sound_of_source_run

example :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileProgramBodyWithAdaptiveSpillExpressions?

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileProgramBodyWithAdaptiveSpillExpressions?_of_compileBlockOpen?

example :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileProgramBodyWithAdaptiveSpillChecked?

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileProgramBodyWithAdaptiveSpillChecked?_of_compileBlockOpen?

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileProgramBodyWithAdaptiveSpillChecked?_of_compileBlockOpen?_backendSafe_bounds

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileProgramBodyWithAdaptiveSpillChecked?_of_compileBlockOpen?_bounds

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileProgramBodyWithAdaptiveSpillChecked?_of_adaptiveFallback_bounds

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileProgramBodyWithAdaptiveSpillChecked?_eq_some

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileProgramBodyWithAdaptiveSpillExpressions?_noCallCreate

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileProgramBodyWithAdaptiveSpillChecked?_noCallCreate

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileProgramBodyWithAdaptiveSpill?_expressionsBlock_sound_of_privateScratchBoundary

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileProgramBodyWithAdaptiveSpill?_expressionsBlock_sound_of_initialState_privateScratchBoundary

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileProgramBodyWithAdaptiveSpill?_expressionsProgram_run_of_initialState_privateScratchBoundary

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileProgramBodyWithAdaptiveSpillChecked?_assembly_sound_of_initialState_privateScratchBoundary

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileProgramBodyWithAdaptiveSpillChecked?_assembly_sound_of_initialState_privateScratchBoundary_endPc

example :=
  Locals.Source.Program.compileCheckedWithAdaptiveSpill?

example :=
  @Locals.Source.Program.compileCheckedWithAdaptiveSpill?_eq_some

example :=
  @Locals.Source.Program.compileCheckedWithAdaptiveSpill?_components

example :=
  @Locals.Source.Program.compileCheckedWithAdaptiveSpill?_of_checked

example :=
  @Locals.Source.Program.compileCheckedWithAdaptiveSpill?_of_compileBlockOpen?

example :=
  @Locals.Source.Program.compileCheckedWithAdaptiveSpill?_of_compileBlockOpen?_bounds

example :=
  @Locals.Source.Program.compileCheckedWithAdaptiveSpill?_of_adaptiveFallback_bounds

example :=
  @Locals.Source.Program.compileCheckedWithAdaptiveSpill?_noCallCreate

example :=
  Locals.Source.Program.AdaptiveSpillOpenOutcomeRel

example :=
  Locals.Source.Program.AdaptiveSpillProgramOutcomeRel

example :=
  Locals.Source.Program.AdaptiveSpillObservableOutcomeRel

example :=
  @Locals.Source.Program.AdaptiveSpillObservableOutcomeRel.regular_inv

example :=
  @Locals.Source.Program.AdaptiveSpillObservableOutcomeRel.halt_inv

example :=
  @Locals.Source.Program.AdaptiveSpillObservableOutcomeRel.regular_observations

example :=
  @Locals.Source.Program.AdaptiveSpillObservableOutcomeRel.halt_observations

example :=
  @Locals.Source.Program.compileCheckedWithAdaptiveSpill?_openBlock_preserves

example :=
  @Locals.Source.Program.compileCheckedWithAdaptiveSpill?_openBlock_preserves_endPc

example :=
  @Locals.Source.Program.compileCheckedWithAdaptiveSpill?_preserves

example :=
  @Locals.Source.Program.compileCheckedWithAdaptiveSpill?_preserves_endPc

example :=
  @Locals.Source.Program.compileCheckedWithAdaptiveSpill?_observations

end AdaptiveSpillBoundary

namespace ConservativeSpillBoundary

/-!
The locals route remains conservative: recursively preserve lexical block
scopes, try the ordinary atom compiler first for atomic statements, and spill
every current stack local only when that atom would otherwise fail. The public
wrapper hides generated spill plans while still exposing checked component and
observation facts from compile success.
-/

example :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileFreshAtomWithConservativeSpill?

example :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileStmtListWithConservativeSpill?

example :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockOpenWithConservativeSpill?

example :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockStmtWithConservativeSpill?

example :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileStmtWithConservativeScopedSpill?

example :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileStmtListWithConservativeScopedSpill?

example :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockOpenWithConservativeScopedSpill?

example :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockStmtWithConservativeScopedSpill?

example :=
  @Structured.Preservation.ProcedurePreservation.compileChecked?_of_accepted_bounds

example :=
  @Structured.Preservation.machineState_eq_of_eraseControl_eq

example :=
  @Structured.Preservation.eraseControl_with_mload_of_eq

example :=
  @Structured.Preservation.eraseControl_with_mstore_of_eq

example :=
  Structured.Preservation.BasicInstr.mload_runnerSafe

example :=
  Structured.Preservation.BasicInstr.mstore_runnerSafe

example :=
  @Structured.Preservation.Code.FrameSafe.append

example :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.BackendSafe

example :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.CodeBackendSafe

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.codeBackendSafe_append

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.prependCode_backendSafe

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.seq_backendSafe

example :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.skip_backendSafe

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.seqList_backendSafe

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.spillStoreTopCode_runnerSafe

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.spillLoadCode_runnerSafe

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.spillStoreTopCode_frameSafe

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.spillLoadCode_frameSafe

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.spillStoreTopCode_backendSafe

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.spillLoadCode_backendSafe

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.spillAllStack?_backendSafe

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.stackOp_dup?_codeBackendSafe

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.stackOp_swap?_codeBackendSafe

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.stackAssignCode_backendSafe

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.basicOp_codeBackendSafe_of_basicOp?

example :=
  Locals.SourceLowering.StateRel.SpillScratch.pushCode_backendSafe

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.readCode?_backendSafe

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillExpr.compileCode?_backendSafe

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillExpr.compileSeqFullCode?_backendSafe

example :=
  @Locals.SourceLowering.PrimitiveSemantics.terminalRelSafe_of_haltKind?

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillAtomPlan.compile?_backendSafe_of_compileCode

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileFreshAtom?_backendSafe_of_compileCode

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileFreshAtomWithSpill?_backendSafe_of_compileCode

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileFreshAtomWithConservativeSpill?_backendSafe_of_compileCode

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileFreshAtom?_backendSafe

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileFreshAtomWithSpill?_backendSafe

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileFreshAtomWithConservativeSpill?_backendSafe

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileStmtWithConservativeSpill?_backendSafe

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileStmtListWithConservativeSpill?_backendSafe

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockOpenWithConservativeSpill?_backendSafe

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockStmtWithConservativeSpill?_backendSafe

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileStmtWithConservativeScopedSpill?_backendSafe

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileStmtListWithConservativeScopedSpill?_backendSafe

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockOpenWithConservativeScopedSpill?_backendSafe

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockStmtWithConservativeScopedSpill?_backendSafe

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.toExpressionsBlock_wf

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.toExpressionsBlock_callsResolved

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.toExpressionsBlock_structured_wf

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.toExpressionsBlock_structured_callsResolved

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.toExpressionsBlock_structured_backendSafe

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.toExpressionsProgram_wf

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.toExpressionsProgram_structured_wf

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.toExpressionsProgram_structured_backendSafe

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.toExpressionsProgram_structured_accepted_of_backendSafe

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.toExpressionsProgram_accepted_of_backendSafe

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.toExpressionsProgram_compileChecked?_of_backendSafe_bounds

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileFreshAtomWithConservativeSpill?_wellFormed

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileFreshAtomWithConservativeSpill?_of_compileFreshAtom?

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileFreshAtomWithConservativeSpill?_fallback

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileFreshAtomWithConservativeSpill?_fallback_some

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileFreshAtomWithConservativeSpill?_isSome_of_compileFreshAtomWithSpill?

example :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileFreshAtomWithConservativeSpill?_swap17Regression_accepts

example :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileProgramBodyWithConservativeSpillExpressions?_deepLocalsRegression_accepts

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileFreshAtomWithConservativeSpill?_noCallCreate

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileStmtListWithConservativeSpill?_noCallCreate

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockOpenWithConservativeSpill?_noCallCreate

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockStmtWithConservativeSpill?_noCallCreate

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileStmtWithConservativeScopedSpill?_noCallCreate

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileStmtListWithConservativeScopedSpill?_noCallCreate

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockOpenWithConservativeScopedSpill?_noCallCreate

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockStmtWithConservativeScopedSpill?_noCallCreate

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileProgramBodyWithConservativeSpillChecked?_noCallCreate

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileFreshAtomWithConservativeSpill?_sound_of_source_run

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileFreshAtomWithConservativeSpill?_regular_storeDefined_of_source_run

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileFreshAtomWithConservativeSpill?_sourceScope_outEnv

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileFreshAtomWithConservativeSpill?_regular_storeDefined_of_source_run_sourceOnly

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileStmtWithConservativeScopedSpill?_sourceScope_outEnv

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileStmtWithConservativeScopedSpill?_regular_storeDefined_of_source_run

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileStmtListWithConservativeScopedSpill?_regular_storeDefined_of_source_run

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockOpenWithConservativeScopedSpill?_regular_storeDefined_of_source_run

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockStmtWithConservativeScopedSpill?_regular_storeDefined_of_source_run

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileStmtListWithConservativeSpill?_wellFormed

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockOpenWithConservativeSpill?_wellFormed

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockStmtWithConservativeSpill?_wellFormed

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileStmtWithConservativeScopedSpill?_wellFormed

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileStmtListWithConservativeScopedSpill?_wellFormed

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockOpenWithConservativeScopedSpill?_wellFormed

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockStmtWithConservativeScopedSpill?_wellFormed

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileStmtListWithConservativeSpill?_of_compileStmtList?

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockOpenWithConservativeSpill?_of_compileBlockOpen?

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileStmtWithConservativeScopedSpill?_of_compileFreshAtom?

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileStmtListWithConservativeScopedSpill?_of_compileStmtList?

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockOpenWithConservativeScopedSpill?_of_compileBlockOpen?

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileProgramBodyWithConservativeSpillExpressions?_of_compileBlockOpen?

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileProgramBodyWithConservativeSpillChecked?_of_compileBlockOpen?

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileProgramBodyWithConservativeSpillChecked?_of_compileBlockOpen?_backendSafe_bounds

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileProgramBodyWithConservativeSpillChecked?_of_compileBlockOpen?_bounds

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileProgramBodyWithConservativeSpillChecked?_of_scopedFallback_bounds

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileProgramBodyWithConservativeSpillChecked?_eq_some

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockStmtWithConservativeSpill?_eq_some

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockStmtWithConservativeScopedSpill?_eq_some

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileStmtListWithConservativeSpill?_sound_of_source_run

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockOpenWithConservativeSpill?_sound_of_source_run

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockStmtWithConservativeSpill?_sound_of_source_run

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileStmtWithConservativeScopedSpill?_sound_of_source_run

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileStmtListWithConservativeScopedSpill?_sound_of_source_run

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockOpenWithConservativeScopedSpill?_sound_of_source_run

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockStmtWithConservativeScopedSpill?_sound_of_source_run

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockOpenWithConservativeSpill?_expressionsBlock_sound_of_source_run

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockOpenWithConservativeScopedSpill?_expressionsBlock_sound_of_source_run

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileProgramBodyWithConservativeSpill?_expressionsBlock_sound_of_privateScratchBoundary

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileProgramBodyWithConservativeSpill?_expressionsBlock_sound_of_initialState_privateScratchBoundary

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileProgramBodyWithConservativeSpill?_expressionsProgram_run_of_initialState_privateScratchBoundary

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileProgramBodyWithConservativeSpillChecked?_assembly_sound_of_initialState_privateScratchBoundary

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileProgramBodyWithConservativeSpillChecked?_assembly_sound_of_initialState_privateScratchBoundary_endPc

example :=
  Locals.Source.Program.compileCheckedWithConservativeSpill?

example :=
  @Locals.Source.Program.compileCheckedWithConservativeSpill?_eq_some

example :=
  @Locals.Source.Program.compileCheckedWithConservativeSpill?_components

example :=
  @Locals.Source.Program.compileCheckedWithConservativeSpill?_of_checked

example :=
  @Locals.Source.Program.compileCheckedWithConservativeSpill?_of_compileBlockOpen?

example :=
  @Locals.Source.Program.compileCheckedWithConservativeSpill?_of_compileBlockOpen?_bounds

example :=
  @Locals.Source.Program.compileCheckedWithConservativeSpill?_of_scopedFallback_bounds

example :=
  @Locals.Source.Program.compileCheckedWithConservativeSpill?_noCallCreate

example :=
  Locals.Source.Program.ConservativeSpillOpenOutcomeRel

example :=
  @Locals.Source.Program.ConservativeSpillOpenOutcomeRel.regular_inv

example :=
  @Locals.Source.Program.ConservativeSpillOpenOutcomeRel.halt_inv

example :=
  @Locals.Source.Program.compileCheckedWithConservativeSpill?_openBlock_preserves

example :=
  @Locals.Source.Program.compileCheckedWithConservativeSpill?_openBlock_preserves_endPc

example :=
  Locals.Source.Program.ConservativeSpillProgramOutcomeRel

example :=
  Locals.Source.Program.ConservativeSpillObservableOutcomeRel

example :=
  @Locals.Source.Program.ConservativeSpillProgramOutcomeRel.regular_inv

example :=
  @Locals.Source.Program.ConservativeSpillProgramOutcomeRel.halt_inv

example :=
  @Locals.Source.Program.ConservativeSpillProgramOutcomeRel.observations

example :=
  @Locals.Source.Program.compileCheckedWithConservativeSpill?_preserves

example :=
  @Locals.Source.Program.compileCheckedWithConservativeSpill?_preserves_endPc

example :=
  @Locals.Source.Program.compileCheckedWithConservativeSpill?_regular_result

example :=
  @Locals.Source.Program.compileCheckedWithConservativeSpill?_halt_result

example :=
  @Locals.Source.Program.compileCheckedWithConservativeSpill?_regular_sharedState

example :=
  @Locals.Source.Program.compileCheckedWithConservativeSpill?_regular_observations

example :=
  @Locals.Source.Program.compileCheckedWithConservativeSpill?_halt_sharedState

example :=
  @Locals.Source.Program.compileCheckedWithConservativeSpill?_halt_observations

example :=
  @Locals.Source.Program.compileCheckedWithConservativeSpill?_observations

end ConservativeSpillBoundary

namespace FunctionsConservativeSpillBoundary

/-!
The same conservative spill-all-on-atom-failure route is exposed one layer
above locals for top-level function-source bodies accepted by the executable
source-owned checker.  This keeps the wrapper honest: it rejects CALL while
covering nested non-CALL block/if/switch/for structure.
-/

example :=
  Functions.Source.Program.compileCheckedWithConservativeSpill?

example :=
  Functions.Source.Program.compileCheckedWithConservativeSpillAtomic?

example :=
  Functions.Source.Program.compileCheckedWithConservativeSpillSourceOwned?

example :=
  @Functions.Source.Program.compileCheckedWithConservativeSpill?_of_checked

example :=
  @Functions.Source.Program.compileCheckedWithConservativeSpill?_of_compileBlockOpen?

example :=
  @Functions.Source.Program.compileCheckedWithConservativeSpill?_of_compileBlockOpen?_bounds

example :=
  @Functions.Source.Program.compileCheckedWithConservativeSpill?_of_scopedFallback_bounds

example :=
  @Functions.Source.Program.compileCheckedWithConservativeSpillSourceOwned?_of_checked

example :=
  @Functions.Source.Program.compileCheckedWithConservativeSpillSourceOwned?_of_compileBlockOpen?

example :=
  @Functions.Source.Program.compileCheckedWithConservativeSpillSourceOwned?_of_compileBlockOpen?_bounds

example :=
  @Functions.Source.Program.compileCheckedWithConservativeSpillSourceOwned?_of_scopedFallback_bounds

def deepLocalsRegressionProgram : Functions.Program :=
  { functions := []
    body :=
      { stmts :=
          Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.deepLocalsRegressionNames.map
              (fun name =>
                Functions.Stmt.let_ name (.lit (EvmYul.UInt256.ofNat 1))) ++
            [Functions.Stmt.assign "x0" (.var "x16")] } }

theorem deepLocalsRegression_direct_toExpressions_rejects :
    deepLocalsRegressionProgram.toExpressions?.isSome = false := by
  native_decide

theorem deepLocalsRegression_sourceOwned_check_accepts :
    Functions.SourceLowering.SourceToLocals.Block.sourceOwned? []
        deepLocalsRegressionProgram.body =
      true := by
  native_decide

theorem deepLocalsRegression_conservative_spill_plan_accepts :
    (Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileProgramBodyWithConservativeSpillExpressions?
        Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.swap17RegressionRange
        deepLocalsRegressionProgram.toLocals).isSome =
      true := by
  native_decide

example :=
  @Functions.SourceLowering.SourceToLocals.Stmt.atomicSourceOwned?_sound

example :=
  @Functions.SourceLowering.SourceToLocals.StmtList.atomicSourceOwned?_sound

example :=
  @Functions.SourceLowering.SourceToLocals.Block.atomicSourceOwned?_sound

example :=
  @Functions.SourceLowering.SourceToLocals.Expr.sourceOwned?_sound

example :=
  @Functions.SourceLowering.SourceToLocals.ExprSeq.sourceOwned?_sound

example :=
  @Functions.SourceLowering.SourceToLocals.Block.sourceOwned?_sound

example :=
  @Functions.SourceLowering.SourceToLocals.Stmt.sourceOwned?_sound

example :=
  @Functions.SourceLowering.SourceToLocals.StmtList.sourceOwned?_sound

example :=
  @Functions.SourceLowering.SourceToLocals.CaseList.sourceOwned?_sound

example :=
  @Functions.SourceLowering.SourceToLocals.Default.sourceOwned?_sound

example :=
  @Functions.SourceLowering.SourceToLocals.sourceOwnedBlock_runOpen_toLocals_of_run

example :=
  @Functions.SourceLowering.SourceToLocals.sourceOwnedBlock_runScoped_toLocals_of_run

example :=
  @Functions.SourceLowering.SourceToLocals.sourceOwnedRunForLoop_toLocals_of_run

example :=
  @Functions.SourceLowering.SourceToLocals.sourceOwnedStmt_toLocals_stmt_run_of_run

example :=
  @Functions.SourceLowering.SourceToLocals.sourceOwnedStmtList_runOpen_toLocals_of_run

example :=
  @Functions.Source.Program.compileCheckedWithConservativeSpill?_eq_some

example :=
  @Functions.Source.Program.compileCheckedWithConservativeSpillAtomic?_eq_some

example :=
  @Functions.Source.Program.compileCheckedWithConservativeSpillSourceOwned?_eq_some

example :=
  @Functions.Source.Program.compileCheckedWithConservativeSpill?_components

example :=
  @Functions.Source.Program.compileCheckedWithConservativeSpill?_noCallCreate

example :=
  @Functions.Source.Program.compileCheckedWithConservativeSpillAtomic?_noCallCreate

example :=
  @Functions.Source.Program.compileCheckedWithConservativeSpillSourceOwned?_noCallCreate

example :=
  @Functions.Source.Program.run_toLocals_of_atomicSourceOwned

example :=
  @Functions.Source.Program.run_toLocals_of_sourceOwned

example :=
  @Functions.Source.Program.compileCheckedWithConservativeSpill?_preserves_of_atomicSourceOwned

example :=
  @Functions.Source.Program.compileCheckedWithConservativeSpillAtomic?_preserves

example :=
  @Functions.Source.Program.compileCheckedWithConservativeSpill?_preserves_of_sourceOwned

example :=
  @Functions.Source.Program.compileCheckedWithConservativeSpillSourceOwned?_preserves

example :=
  @Functions.Source.Program.compileCheckedWithConservativeSpill?_observations_of_atomicSourceOwned

example :=
  @Functions.Source.Program.compileCheckedWithConservativeSpillAtomic?_observations

example :=
  @Functions.Source.Program.compileCheckedWithConservativeSpill?_observations_of_sourceOwned

example :=
  @Functions.Source.Program.compileCheckedWithConservativeSpillSourceOwned?_observations

end FunctionsConservativeSpillBoundary

namespace FunctionsAdaptiveSpillBoundary

/-!
The adaptive spill route is also exposed one layer above locals for the
source-owned no-CALL Functions subset.  Generated spill plans and expressions
programs remain private: callers see executable compile success plus source
runs, and preservation delegates through the checked locals adaptive wrapper.
-/

example :=
  Functions.Source.Program.compileCheckedWithAdaptiveSpill?

example :=
  Functions.Source.Program.compileCheckedWithAdaptiveSpillAtomic?

example :=
  Functions.Source.Program.compileCheckedWithAdaptiveSpillSourceOwned?

example :=
  @Functions.Source.Program.compileCheckedWithAdaptiveSpill?_eq_some

example :=
  @Functions.Source.Program.compileCheckedWithAdaptiveSpill?_of_checked

example :=
  @Functions.Source.Program.compileCheckedWithAdaptiveSpill?_of_compileBlockOpen?

example :=
  @Functions.Source.Program.compileCheckedWithAdaptiveSpill?_of_compileBlockOpen?_bounds

example :=
  @Functions.Source.Program.compileCheckedWithAdaptiveSpill?_of_adaptiveFallback_bounds

example :=
  @Functions.Source.Program.compileCheckedWithAdaptiveSpillAtomic?_eq_some

example :=
  @Functions.Source.Program.compileCheckedWithAdaptiveSpillSourceOwned?_eq_some

example :=
  @Functions.Source.Program.compileCheckedWithAdaptiveSpillSourceOwned?_of_checked

example :=
  @Functions.Source.Program.compileCheckedWithAdaptiveSpillSourceOwned?_of_compileBlockOpen?

example :=
  @Functions.Source.Program.compileCheckedWithAdaptiveSpillSourceOwned?_of_compileBlockOpen?_bounds

example :=
  @Functions.Source.Program.compileCheckedWithAdaptiveSpillSourceOwned?_of_adaptiveFallback_bounds

example :=
  @Functions.Source.Program.compileCheckedWithAdaptiveSpill?_components

example :=
  FunctionsConservativeSpillBoundary.deepLocalsRegression_direct_toExpressions_rejects

example :=
  FunctionsConservativeSpillBoundary.deepLocalsRegression_sourceOwned_check_accepts

theorem deepLocalsRegression_adaptive_spill_plan_accepts :
    (Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileProgramBodyWithAdaptiveSpillExpressions?
        Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.swap17RegressionRange
        FunctionsConservativeSpillBoundary.deepLocalsRegressionProgram.toLocals).isSome =
      true := by
  native_decide

theorem deepLocalsRegression_adaptive_spill_block_plan_accepts :
    (Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockOpenWithAdaptiveSpill?
        Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.swap17RegressionRange
        [] [] []
        FunctionsConservativeSpillBoundary.deepLocalsRegressionProgram.toLocals.body).isSome =
      true := by
  native_decide

def deepLocalsRegressionAdaptivePlan :
    Locals.SourceLowering.StateRel.SpillScratch.SpillPlan :=
  (Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockOpenWithAdaptiveSpill?
      Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.swap17RegressionRange
      [] [] []
      FunctionsConservativeSpillBoundary.deepLocalsRegressionProgram.toLocals.body).get
    deepLocalsRegression_adaptive_spill_block_plan_accepts

theorem deepLocalsRegression_adaptive_spill_plan_eq :
    Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockOpenWithAdaptiveSpill?
        Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.swap17RegressionRange
        [] [] []
        FunctionsConservativeSpillBoundary.deepLocalsRegressionProgram.toLocals.body =
      some deepLocalsRegressionAdaptivePlan := by
  exact (Option.some_get deepLocalsRegression_adaptive_spill_block_plan_accepts).symm

theorem deepLocalsRegression_adaptive_spill_plan_bounds :
    Structured.Preservation.ProcedurePreservation.CompilationBounds
      (Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.toExpressionsProgram
        deepLocalsRegressionAdaptivePlan).toStructured := by
  exact
    Structured.Preservation.ProcedurePreservation.bounds_of_checked
      (by native_decide)

theorem deepLocalsRegression_adaptive_spill_checked_sourceOwned_accepts :
    Functions.Source.Program.compileCheckedWithAdaptiveSpillSourceOwned?
        Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.swap17RegressionRange
        FunctionsConservativeSpillBoundary.deepLocalsRegressionProgram =
      some
        (Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.toExpressionsProgram
          deepLocalsRegressionAdaptivePlan).compile := by
  exact
    Functions.Source.Program.compileCheckedWithAdaptiveSpillSourceOwned?_of_adaptiveFallback_bounds
      FunctionsConservativeSpillBoundary.deepLocalsRegression_sourceOwned_check_accepts
      deepLocalsRegression_adaptive_spill_plan_eq
      deepLocalsRegression_adaptive_spill_plan_bounds

example :=
  @Functions.Source.Program.compileCheckedWithAdaptiveSpill?_noCallCreate

example :=
  @Functions.Source.Program.compileCheckedWithAdaptiveSpillAtomic?_noCallCreate

example :=
  @Functions.Source.Program.compileCheckedWithAdaptiveSpillSourceOwned?_noCallCreate

example :=
  @Functions.Source.Program.compileCheckedWithAdaptiveSpill?_preserves_of_atomicSourceOwned

example :=
  @Functions.Source.Program.compileCheckedWithAdaptiveSpillAtomic?_preserves

example :=
  @Functions.Source.Program.compileCheckedWithAdaptiveSpill?_preserves_of_sourceOwned

example :=
  @Functions.Source.Program.compileCheckedWithAdaptiveSpillSourceOwned?_preserves

example :=
  @Functions.Source.Program.compileCheckedWithAdaptiveSpill?_observations_of_atomicSourceOwned

example :=
  @Functions.Source.Program.compileCheckedWithAdaptiveSpillAtomic?_observations

example :=
  @Functions.Source.Program.compileCheckedWithAdaptiveSpill?_observations_of_sourceOwned

example :=
  @Functions.Source.Program.compileCheckedWithAdaptiveSpillSourceOwned?_observations

end FunctionsAdaptiveSpillBoundary

namespace ObjectsYulConservativeSpillAdapterBoundary

/-!
The conservative scoped spill route now reaches the transparent Objects/Yul
source-lowered adapters too.  This is the broader fail-closed no-CALL spill
path: it supports source-owned non-CALL control through the executable checker,
while still hiding generated spill plans and expressions programs behind
compile success.
-/

example :=
  Objects.Source.Program.compileCheckedWithConservativeSpillSourceOwned?

example :=
  @Objects.Source.Program.compileCheckedWithConservativeSpillSourceOwned?_eq_some

example :=
  @Objects.Source.Program.compileCheckedWithConservativeSpillSourceOwned?_of_compileBlockOpen?

example :=
  @Objects.Source.Program.compileCheckedWithConservativeSpillSourceOwned?_of_compileBlockOpen?_bounds

example :=
  @Objects.Source.Program.compileCheckedWithConservativeSpillSourceOwned?_of_scopedFallback_bounds

example :=
  @Objects.Source.Program.compileCheckedWithConservativeSpillSourceOwned?_noCallCreate

example :=
  @Objects.Source.Program.compileCheckedWithConservativeSpillSourceOwned?_preserves

example :=
  @Objects.Source.Program.compileCheckedWithConservativeSpillSourceOwned?_observations

example :=
  Yul.Program.compileCheckedWithConservativeSpillSourceOwned?

example :=
  @Yul.Program.compileCheckedWithConservativeSpillSourceOwned?_eq_some

example :=
  @Yul.Program.compileCheckedWithConservativeSpillSourceOwned?_of_toObjects_compileBlockOpen?

example :=
  @Yul.Program.compileCheckedWithConservativeSpillSourceOwned?_of_toObjects_compileBlockOpen?_bounds

example :=
  @Yul.Program.compileCheckedWithConservativeSpillSourceOwned?_of_toObjects_scopedFallback_bounds

example :=
  @Yul.Program.compileCheckedWithConservativeSpillSourceOwned?_noCallCreate

example :=
  @Yul.Program.compileCheckedWithConservativeSpillSourceOwned?_source_preserves

example :=
  @Yul.Program.compileCheckedWithConservativeSpillSourceOwned?_source_observations

end ObjectsYulConservativeSpillAdapterBoundary

namespace ObjectsYulAdaptiveSpillAdapterBoundary

/-!
The adaptive spill compiler has now been lifted through the transparent
Objects/Yul source-lowered adapters.  This is a checked source-owned root route:
it compiles the lowered root body with private scratch spilling and proves
preservation for `SourceLowered.run` under the structured primitive semantics.
It is intentionally distinct from the preferred imported-Yul live-layout path.
-/

example :=
  Objects.Source.Program.compileCheckedWithAdaptiveSpillSourceOwned?

example :=
  @Objects.Source.Program.compileCheckedWithAdaptiveSpillSourceOwned?_eq_some

example :=
  @Objects.Source.Program.compileCheckedWithAdaptiveSpillSourceOwned?_of_compileBlockOpen?

example :=
  @Objects.Source.Program.compileCheckedWithAdaptiveSpillSourceOwned?_of_compileBlockOpen?_bounds

example :=
  @Objects.Source.Program.compileCheckedWithAdaptiveSpillSourceOwned?_of_adaptiveFallback_bounds

example :=
  @Objects.Source.Program.compileCheckedWithAdaptiveSpillSourceOwned?_noCallCreate

example :=
  @Objects.Source.Program.compileCheckedWithAdaptiveSpillSourceOwned?_preserves

example :=
  @Objects.Source.Program.compileCheckedWithAdaptiveSpillSourceOwned?_observations

example :=
  Yul.Program.compileCheckedWithAdaptiveSpillSourceOwned?

example :=
  @Yul.Program.compileCheckedWithAdaptiveSpillSourceOwned?_eq_some

example :=
  @Yul.Program.compileCheckedWithAdaptiveSpillSourceOwned?_of_toObjects_compileBlockOpen?

example :=
  @Yul.Program.compileCheckedWithAdaptiveSpillSourceOwned?_of_toObjects_compileBlockOpen?_bounds

example :=
  @Yul.Program.compileCheckedWithAdaptiveSpillSourceOwned?_of_toObjects_adaptiveFallback_bounds

example :=
  @Yul.Program.compileCheckedWithAdaptiveSpillSourceOwned?_noCallCreate

example :=
  @Yul.Program.compileCheckedWithAdaptiveSpillSourceOwned?_source_preserves

example :=
  @Yul.Program.compileCheckedWithAdaptiveSpillSourceOwned?_source_observations

end ObjectsYulAdaptiveSpillAdapterBoundary

namespace YulConservativeSpillTargetBoundary

/-!
The conservative scoped spill route now has the same concrete target/gas
boundary as the adaptive route.  Successful compilation is resolved through
assembly/bytecode checks, feature/source-static gates, no-RETURNDATACOPY,
no-CALL/CREATE, executable assembly stack bounds, source-lowered gas replay,
and imported/reference Yul replay without re-entering the old live-layout
top-16-rejecting target path.
-/

example :=
  Yul.Program.compileCheckedWithConservativeSpillSourceOwnedAssemblyTarget?

example :=
  @Yul.Program.compileCheckedWithConservativeSpillSourceOwnedAssemblyTarget?_eq_some

example :=
  @Yul.Program.compileCheckedWithConservativeSpillSourceOwnedAssemblyTarget?_of_compileCheckedWithConservativeSpillSourceOwned?

example :=
  @Yul.Program.compileCheckedWithConservativeSpillSourceOwnedAssemblyTarget?_of_toObjects_compileBlockOpen?

example :=
  Yul.Program.compileCheckedWithConservativeSpillSourceOwnedAssemblyTargetBytecode?

example :=
  @Yul.Program.compileCheckedWithConservativeSpillSourceOwnedAssemblyTargetBytecode?_eq_some

example :=
  Yul.Program.compileCheckedWithConservativeSpillSourceOwnedAssemblyTargetBytecodeFeatures?

example :=
  @Yul.Program.compileCheckedWithConservativeSpillSourceOwnedAssemblyTargetBytecodeFeatures?_eq_some

example :=
  Yul.Program.compileCheckedWithConservativeSpillSourceOwnedAssemblyTargetBytecodeFeaturesSourceStatic?

example :=
  @Yul.Program.compileCheckedWithConservativeSpillSourceOwnedAssemblyTargetBytecodeFeaturesSourceStatic?_eq_some

example :=
  Yul.Program.compileCheckedWithConservativeSpillSourceOwnedAssemblyTargetBytecodeFeaturesSourceStaticNoReturnDataCopy?

example :=
  @Yul.Program.compileCheckedWithConservativeSpillSourceOwnedAssemblyTargetBytecodeFeaturesSourceStaticNoReturnDataCopy?_eq_some

example :=
  @Yul.Program.compileCheckedWithConservativeSpillSourceOwnedAssemblyTargetBytecodeFeaturesSourceStaticNoReturnDataCopy?_compileConservative

example :=
  @Yul.Program.compileCheckedWithConservativeSpillSourceOwnedAssemblyTargetBytecodeFeaturesSourceStaticNoReturnDataCopy?_assemblyCompile

example :=
  @Yul.Program.compileCheckedWithConservativeSpillSourceOwnedAssemblyTargetBytecodeFeaturesSourceStaticNoReturnDataCopy?_jumpdestCorrect

example :=
  @Yul.Program.compileCheckedWithConservativeSpillSourceOwnedAssemblyTargetBytecodeFeaturesSourceStaticNoReturnDataCopy?_targetFitsDecodeWindow

example :=
  @Yul.Program.compileCheckedWithConservativeSpillSourceOwnedAssemblyTargetBytecodeFeaturesSourceStaticNoReturnDataCopy?_decodeSafety

example :=
  @Yul.Program.compileCheckedWithConservativeSpillSourceOwnedAssemblyTargetBytecodeFeaturesSourceStaticNoReturnDataCopy?_blockReplayNoReturnDataCopy

example :=
  @Yul.Program.compileCheckedWithConservativeSpillSourceOwnedAssemblyTargetBytecodeFeaturesSourceStaticNoReturnDataCopy?_noCallCreate

example :=
  @Yul.Program.compileCheckedWithConservativeSpillSourceOwnedAssemblyTargetBytecodeFeaturesSourceStaticNoReturnDataCopy?_blockReplayNoCallCreate

example :=
  @Yul.Program.compileCheckedWithConservativeSpillSourceOwnedAssemblyTargetBytecodeFeaturesSourceStaticNoReturnDataCopy?_blockPathChecks_of_core

example :=
  @Yul.Program.compileCheckedWithConservativeSpillSourceOwnedAssemblyTargetBytecodeFeaturesSourceStaticNoReturnDataCopy?_source_observations_targetFacts

example :=
  Yul.Program.compileCheckedWithConservativeSpillSourceOwnedAssemblyTargetBytecodeFeaturesSourceStaticAssemblyInferredBoundStackSafeNoReturnDataCopy?

example :=
  @Yul.Program.compileCheckedWithConservativeSpillSourceOwnedAssemblyTargetBytecodeFeaturesSourceStaticAssemblyInferredBoundStackSafeNoReturnDataCopy?_eq_some

example :=
  @Yul.Program.compileCheckedWithConservativeSpillSourceOwnedAssemblyTargetBytecodeFeaturesSourceStaticAssemblyInferredBoundStackSafeNoReturnDataCopy?_of_noReturnDataCopy

example :=
  @Yul.Program.compileCheckedWithConservativeSpillSourceOwnedAssemblyTargetBytecodeFeaturesSourceStaticAssemblyInferredBoundStackSafeNoReturnDataCopy?_base

example :=
  @Yul.Program.compileCheckedWithConservativeSpillSourceOwnedAssemblyTargetBytecodeFeaturesSourceStaticAssemblyInferredBoundStackSafeNoReturnDataCopy?_assemblyCompile

example :=
  @Yul.Program.compileCheckedWithConservativeSpillSourceOwnedAssemblyTargetBytecodeFeaturesSourceStaticAssemblyInferredBoundStackSafeNoReturnDataCopy?_assemblyBoundCheck

example :=
  @Yul.Program.compileCheckedWithConservativeSpillSourceOwnedAssemblyTargetBytecodeFeaturesSourceStaticAssemblyInferredBoundStackSafeNoReturnDataCopy?_assemblyBoundCheck_checked

example :=
  @Yul.Program.compileCheckedWithConservativeSpillSourceOwnedAssemblyTargetBytecodeFeaturesSourceStaticAssemblyInferredBoundStackSafeNoReturnDataCopy?_actualEVMStackHeadroomBound

example :=
  @Yul.Program.conservativeSpillStackSafe_actualEVMHeadroomPoints

example :=
  @Yul.Program.compileCheckedWithConservativeSpillSourceOwnedAssemblyTargetBytecodeFeaturesSourceStaticAssemblyInferredBoundStackSafeNoReturnDataCopy?_sourceLowered_sufficientGas_X

example :=
  @Yul.Program.compileCheckedWithConservativeSpillSourceOwnedAssemblyTargetBytecodeFeaturesSourceStaticAssemblyInferredBoundStackSafeNoReturnDataCopy?_referenceRun_sufficientGas_X

example :=
  @Yul.Program.compileCheckedWithConservativeSpillSourceOwnedAssemblyTargetBytecodeFeaturesSourceStaticAssemblyInferredBoundStackSafeNoReturnDataCopy?_runResult_sufficientGas_X

example :=
  Yul.Program.StackSafeOrConservativeSpillObservableOutcomeRel

example :=
  Yul.Program.compileCheckedStackSafeNoReturnDataCopyOrConservativeSpill?

example :=
  @Yul.Program.compileCheckedStackSafeNoReturnDataCopyOrConservativeSpill?_of_stackSafe

example :=
  @Yul.Program.compileCheckedStackSafeNoReturnDataCopyOrConservativeSpill?_of_conservativeSpill

example :=
  @Yul.Program.compileCheckedStackSafeNoReturnDataCopyOrConservativeSpill?_runResult_sufficientGas_X

example :=
  @Yul.Program.compileCheckedStackSafeNoReturnDataCopyOrConservativeSpill?_runResult_sufficientGas_no_out_of_gas_X

end YulConservativeSpillTargetBoundary

namespace YulAdaptiveSpillTargetBoundary

/-!
The source-lowered adaptive spill route now has a concrete runtime adapter
layer: successful compilation can be resolved to an assembly target, checked for
bytecode bridge, imported-feature/source-static, no-CALL/CREATE,
no-RETURNDATACOPY, executable assembly stack headroom, and then replayed by the
gas-aware EVM for every sufficiently large UInt256 gas value.  The imported
reference run is now connected through a source-only `SourceLowered.run` bridge,
so this boundary no longer falls back to the old top-16-rejecting
`compileChecked?` target path.
-/

example :=
  Yul.Program.StackSafeOrAdaptiveSpillObservableOutcomeRel

example :=
  Yul.Program.StackGuardedObservableOutcomeRel

example :=
  Yul.Program.StackGuardedPlannedPreallocObservableOutcomeRel

example :=
  @Yul.Program.StackGuardedObservableOutcomeRel.of_exact

example :=
  @Yul.Program.StackGuardedObservableOutcomeRel.of_adaptiveSpill

example :=
  @Yul.Program.StackGuardedObservableOutcomeRel.elim

example :=
  Yul.Program.StackGuardedNoReturnDataCopyFallbackScratchReady

example :=
  @Yul.Program.StackGuardedNoReturnDataCopyFallbackScratchReady.of_liveLayout

example :=
  @Yul.Program.StackGuardedNoReturnDataCopyFallbackScratchReady.of_scratchCheck

example :=
  Yul.Program.StackGuardedSufficientGasConclusion

example :=
  Yul.Program.StackGuardedNoOutOfGasConclusion

example :=
  Yul.Program.StackGuardedPlannedPreallocSufficientGasConclusion

example :=
  Yul.Program.StackGuardedPlannedPreallocNoOutOfGasConclusion

example :=
  Yul.Program.compileCheckedStackSafeNoReturnDataCopyOrAdaptiveSpill?

example :=
  Yul.Program.compileStackGuardedNoReturnDataCopyPlannedPrealloc?

example :=
  @Yul.Program.compileCheckedStackSafeNoReturnDataCopyOrAdaptiveSpill?_of_stackSafe

example :=
  @Yul.Program.compileCheckedStackSafeNoReturnDataCopyOrAdaptiveSpill?_of_adaptiveSpill

example :=
  @Yul.Program.compileCheckedStackSafeNoReturnDataCopyOrAdaptiveSpill?_runResult_sufficientGas_X

example :=
  @Yul.Program.compileCheckedStackSafeNoReturnDataCopyOrAdaptiveSpill?_runResult_sufficientGas_no_out_of_gas_X

example :=
  @Yul.Program.compileCheckedStackSafeNoReturnDataCopyOrAdaptiveSpill?_runResult_existsSourceRun_exprResultContracts_sufficientGas_X

example :=
  @Yul.Program.compileCheckedStackSafeNoReturnDataCopyOrAdaptiveSpill?_runResult_existsSourceRun_exprNoOutOfFuelContracts_sufficientGas_X

example :=
  @Yul.Program.compileCheckedStackSafeNoReturnDataCopyOrAdaptiveSpill?_runResult_existsSourceRun_exprNoOutOfFuelContracts_sufficientGas_no_out_of_gas_X

example :=
  Yul.Program.compileLiveNoInternalCallCheckedStackSafeNoReturnDataCopyOrAdaptiveSpill?

example :=
  @Yul.Program.compileLiveNoInternalCallCheckedStackSafeNoReturnDataCopyOrAdaptiveSpill?_of_liveLayout

example :=
  @Yul.Program.compileLiveNoInternalCallCheckedStackSafeNoReturnDataCopyOrAdaptiveSpill?_of_adaptiveFallback

example :=
  @Yul.Program.compileLiveNoInternalCallCheckedStackSafeNoReturnDataCopyOrAdaptiveSpill?_eq_some

example :=
  @Yul.Program.compileLiveNoInternalCallCheckedStackSafeNoReturnDataCopyOrAdaptiveSpill?_runResult_existsSourceRun_exprNoOutOfFuelContracts_sufficientGas_X

example :=
  @Yul.Program.compileLiveNoInternalCallCheckedStackSafeNoReturnDataCopyOrAdaptiveSpill?_runResult_existsSourceRun_exprNoOutOfFuelContracts_sufficientGas_no_out_of_gas_X

example :=
  @Yul.Program.compileLiveNoInternalCallCheckedStackSafeNoReturnDataCopyOrAdaptiveSpill?_runResult_existsSourceRun_exprNoOutOfFuelContracts_sufficientGas_X_of_liveLayoutOrScratchBoundary

example :=
  @Yul.Program.compileLiveNoInternalCallCheckedStackSafeNoReturnDataCopyOrAdaptiveSpill?_runResult_existsSourceRun_exprNoOutOfFuelContracts_sufficientGas_no_out_of_gas_X_of_liveLayoutOrScratchBoundary

example :=
  Yul.Program.compileStackGuardedNoReturnDataCopy?

example :=
  @Yul.Program.compileStackGuardedNoReturnDataCopy?_of_liveLayout

example :=
  @Yul.Program.compileStackGuardedNoReturnDataCopy?_of_adaptiveFallback

example :=
  @Yul.Program.compileStackGuardedNoReturnDataCopy?_eq_some

example :=
  @Yul.Program.compileStackGuardedNoReturnDataCopy?_runResult_existsSourceRun_exprNoOutOfFuelContracts_sufficientGas_X

example :=
  @Yul.Program.compileStackGuardedNoReturnDataCopy?_runResult_existsSourceRun_exprNoOutOfFuelContracts_sufficientGas_no_out_of_gas_X

example :=
  Yul.Program.compileStackGuardedSourceOwned?

example :=
  Yul.Program.StackGuardedSourceOwnedProgramOutcomeRel

example :=
  Yul.Program.StackGuardedSourceOwnedObservableOutcomeRel

example :=
  Yul.Program.StackGuardedSourceOwnedFallbackScratchReady

example :=
  @Yul.Program.StackGuardedSourceOwnedFallbackScratchReady.of_liveLayout

example :=
  @Yul.Program.StackGuardedSourceOwnedFallbackScratchReady.of_scratchCheck

example :=
  @Yul.Program.compileStackGuardedSourceOwned?_of_liveLayout

example :=
  @Yul.Program.compileStackGuardedSourceOwned?_of_adaptiveFallback

example :=
  @Yul.Program.compileStackGuardedSourceOwned?_eq_some

example :=
  @Yul.Program.compileStackGuardedSourceOwned?_noCallCreate

example :=
  @Yul.Program.compileStackGuardedSourceOwned?_source_preserves

example :=
  @Yul.Program.compileStackGuardedSourceOwned?_source_observations

abbrev AdaptiveSpillSoundConclusion
    (cfg : Yul.Reference.StateRelConfig)
    (range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange)
    (program : Yul.Program)
    (asm : Assembly.Program)
    (target : Assembly.TargetProgram)
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (initial : Yul.EVMState)
    (referenceResult : Yul.Reference.Result) : Prop :=
  ∃ sourceFuel : Nat,
  ∃ sourceOutcome : Objects.Source.Outcome,
  ∃ targetFuel targetOutcome gasBound,
    Yul.Reference.runResult sourceFuel.succ program (.Ok shared store) =
        .ok referenceResult ∧
      Yul.Program.RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg
          (Yul.Program.RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel
            cfg)
          (Yul.Program.RecursiveBridgeTerminalObservationContracts.canonicalRevertRel
            cfg)
          program (.Ok shared store) referenceResult sourceOutcome ∧
        Yul.Program.StackSafeOrAdaptiveSpillObservableOutcomeRel range
            sourceOutcome targetOutcome ∧
          Assembly.Accepted asm ∧
            Assembly.Bytecode.compileBytes? asm =
                some (Assembly.Bytecode.encodeTarget target) ∧
              Assembly.Bytecode.EncodingCorrect target
                (Assembly.Bytecode.encodeTarget target) ∧
                Assembly.Preservation.BlockTraceResult asm target targetFuel
                    (Yul.Program.canonicalEntryState initial) targetOutcome ∧
                  gasBound =
                    Assembly.GasAware.XStepTrace.XBlockTraceGasBudget asm
                      targetFuel (Yul.Program.canonicalEntryState initial)
                      targetOutcome ∧
                    ∀ gas,
                      gasBound ≤ gas →
                        gas < EvmYul.UInt256.size →
                          ∃ evmFuel result,
                            Assembly.GasAware.XStepTrace
                                (Assembly.GasAware.validJumps target) evmFuel
                                (Assembly.GasAware.installCodeAndGas target gas
                                  (Yul.Program.canonicalEntryState initial))
                                result ∧
                              EvmYul.EVM.X evmFuel
                                  (Assembly.GasAware.validJumps target)
                                  (Assembly.GasAware.installCodeAndGas target
                                    gas
                                    (Yul.Program.canonicalEntryState initial)) =
                                .ok result ∧
                                Assembly.GasAware.XResultAgrees targetOutcome
                                  result

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    {cfg : Yul.Reference.StateRelConfig}
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {program : Yul.Program}
    {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {initial : Yul.EVMState}
    {referenceResult : Yul.Reference.Result}
    (hExprNoSuccessfulOutOfFuel :
      Yul.Program.RecursiveBridgeExprNoOutOfFuelContracts cfg program)
    (hInitialCodeImageRel :
      Yul.Program.RecursiveBridgeInitialCodeImageRel cfg program target shared
        initial)
    (hSourceFuelRun :
      ∃ sourceFuel,
        Yul.Program.RecursiveBridgeSourceRun program shared store sourceFuel
          referenceResult)
    (hCompileTarget :
      Yul.Program.compileCheckedStackSafeNoReturnDataCopyOrAdaptiveSpill?
          range program =
        some (asm, target))
    (hBoundary :
      Locals.SourceLowering.StateRel.SpillScratch.PrivateScratchBoundary.scratchCheck?
          (Yul.Program.canonicalEntryState initial).toMachineState range [] [] [] =
        true)
    (hInitialPerm : initial.executionEnv.perm = true) :
    AdaptiveSpillSoundConclusion cfg range program asm target shared store
      initial referenceResult :=
  Yul.Program.compileCheckedStackSafeNoReturnDataCopyOrAdaptiveSpill?_runResult_existsSourceRun_exprNoOutOfFuelContracts_sufficientGas_X
    hSpec hExprNoSuccessfulOutOfFuel hInitialCodeImageRel
    hSourceFuelRun hCompileTarget hBoundary hInitialPerm

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    {cfg : Yul.Reference.StateRelConfig}
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {program : Yul.Program}
    {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {initial : Yul.EVMState}
    {referenceResult : Yul.Reference.Result}
    (hExprNoSuccessfulOutOfFuel :
      Yul.Program.RecursiveBridgeExprNoOutOfFuelContracts cfg program)
    (hInitialCodeImageRel :
      Yul.Program.RecursiveBridgeInitialCodeImageRel cfg program target shared
        initial)
    (hSourceFuelRun :
      ∃ sourceFuel,
        Yul.Program.RecursiveBridgeSourceRun program shared store sourceFuel
          referenceResult)
    (hCompileTarget :
      Yul.Program.compileLiveNoInternalCallCheckedStackSafeNoReturnDataCopyOrAdaptiveSpill?
          range program =
        some (asm, target))
    (hBoundary :
      Locals.SourceLowering.StateRel.SpillScratch.PrivateScratchBoundary.scratchCheck?
          (Yul.Program.canonicalEntryState initial).toMachineState range [] [] [] =
        true)
    (hInitialPerm : initial.executionEnv.perm = true) :
    AdaptiveSpillSoundConclusion cfg range program asm target shared store
      initial referenceResult :=
  Yul.Program.compileLiveNoInternalCallCheckedStackSafeNoReturnDataCopyOrAdaptiveSpill?_runResult_existsSourceRun_exprNoOutOfFuelContracts_sufficientGas_X
    hSpec hExprNoSuccessfulOutOfFuel hInitialCodeImageRel
    hSourceFuelRun hCompileTarget hBoundary hInitialPerm

abbrev AdaptiveSpillNoOutOfGasConclusion
    (cfg : Yul.Reference.StateRelConfig)
    (range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange)
    (program : Yul.Program)
    (asm : Assembly.Program)
    (target : Assembly.TargetProgram)
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (initial : Yul.EVMState)
    (referenceResult : Yul.Reference.Result) : Prop :=
  ∃ sourceFuel : Nat,
  ∃ sourceOutcome : Objects.Source.Outcome,
  ∃ targetFuel targetOutcome gasBound,
    Yul.Reference.runResult sourceFuel.succ program (.Ok shared store) =
        .ok referenceResult ∧
      Yul.Program.RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg
          (Yul.Program.RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel
            cfg)
          (Yul.Program.RecursiveBridgeTerminalObservationContracts.canonicalRevertRel
            cfg)
          program (.Ok shared store) referenceResult sourceOutcome ∧
        Yul.Program.StackSafeOrAdaptiveSpillObservableOutcomeRel range
            sourceOutcome targetOutcome ∧
          Assembly.Preservation.BlockTraceResult asm target targetFuel
              (Yul.Program.canonicalEntryState initial) targetOutcome ∧
            gasBound =
              Assembly.GasAware.XStepTrace.XBlockTraceGasBudget asm targetFuel
                (Yul.Program.canonicalEntryState initial) targetOutcome ∧
              ∀ gas,
                gasBound ≤ gas →
                  gas < EvmYul.UInt256.size →
                    ∃ evmFuel,
                      EvmYul.EVM.X evmFuel
                          (Assembly.GasAware.validJumps target)
                          (Assembly.GasAware.installCodeAndGas target gas
                            (Yul.Program.canonicalEntryState initial)) ≠
                        .error EvmYul.EVM.ExecutionException.OutOfGass

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    {cfg : Yul.Reference.StateRelConfig}
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {program : Yul.Program}
    {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {initial : Yul.EVMState}
    {referenceResult : Yul.Reference.Result}
    (hExprNoSuccessfulOutOfFuel :
      Yul.Program.RecursiveBridgeExprNoOutOfFuelContracts cfg program)
    (hInitialCodeImageRel :
      Yul.Program.RecursiveBridgeInitialCodeImageRel cfg program target shared
        initial)
    (hSourceFuelRun :
      ∃ sourceFuel,
        Yul.Program.RecursiveBridgeSourceRun program shared store sourceFuel
          referenceResult)
    (hCompileTarget :
      Yul.Program.compileCheckedStackSafeNoReturnDataCopyOrAdaptiveSpill?
          range program =
        some (asm, target))
    (hBoundary :
      Locals.SourceLowering.StateRel.SpillScratch.PrivateScratchBoundary.scratchCheck?
          (Yul.Program.canonicalEntryState initial).toMachineState range [] [] [] =
        true)
    (hInitialPerm : initial.executionEnv.perm = true) :
    AdaptiveSpillNoOutOfGasConclusion cfg range program asm target shared store
      initial referenceResult :=
  Yul.Program.compileCheckedStackSafeNoReturnDataCopyOrAdaptiveSpill?_runResult_existsSourceRun_exprNoOutOfFuelContracts_sufficientGas_no_out_of_gas_X
    hSpec hExprNoSuccessfulOutOfFuel hInitialCodeImageRel
    hSourceFuelRun hCompileTarget hBoundary hInitialPerm

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    {cfg : Yul.Reference.StateRelConfig}
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {program : Yul.Program}
    {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {initial : Yul.EVMState}
    {referenceResult : Yul.Reference.Result}
    (hExprNoSuccessfulOutOfFuel :
      Yul.Program.RecursiveBridgeExprNoOutOfFuelContracts cfg program)
    (hInitialCodeImageRel :
      Yul.Program.RecursiveBridgeInitialCodeImageRel cfg program target shared
        initial)
    (hSourceFuelRun :
      ∃ sourceFuel,
        Yul.Program.RecursiveBridgeSourceRun program shared store sourceFuel
          referenceResult)
    (hCompileTarget :
      Yul.Program.compileLiveNoInternalCallCheckedStackSafeNoReturnDataCopyOrAdaptiveSpill?
          range program =
        some (asm, target))
    (hBoundary :
      Locals.SourceLowering.StateRel.SpillScratch.PrivateScratchBoundary.scratchCheck?
          (Yul.Program.canonicalEntryState initial).toMachineState range [] [] [] =
        true)
    (hInitialPerm : initial.executionEnv.perm = true) :
    AdaptiveSpillNoOutOfGasConclusion cfg range program asm target shared store
      initial referenceResult :=
  Yul.Program.compileLiveNoInternalCallCheckedStackSafeNoReturnDataCopyOrAdaptiveSpill?_runResult_existsSourceRun_exprNoOutOfFuelContracts_sufficientGas_no_out_of_gas_X
    hSpec hExprNoSuccessfulOutOfFuel hInitialCodeImageRel
    hSourceFuelRun hCompileTarget hBoundary hInitialPerm

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    {cfg : Yul.Reference.StateRelConfig}
    {maxWords : Nat}
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {program : Yul.Program}
    {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {initial : Yul.EVMState}
    {referenceResult : Yul.Reference.Result}
    (hExprNoSuccessfulOutOfFuel :
      Yul.Program.RecursiveBridgeExprNoOutOfFuelContracts cfg program)
    (hInitialCodeImageRel :
      Yul.Program.RecursiveBridgeInitialCodeImageRel cfg program target shared
        initial)
    (hSourceFuelRun :
      ∃ sourceFuel,
        Yul.Program.RecursiveBridgeSourceRun program shared store sourceFuel
          referenceResult)
    (hCompileTarget :
      Yul.Program.compileStackGuardedNoReturnDataCopyPlannedPrealloc?
          maxWords program =
        some (range, asm, target))
    (hInitialMemory :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchInitialMemoryEmpty
        (Yul.Program.canonicalEntryState initial).toMachineState)
    (hInitialPerm : initial.executionEnv.perm = true) :
    Yul.Program.StackGuardedPlannedPreallocSufficientGasConclusion cfg range
      program asm target shared store initial referenceResult :=
  Yul.Program.compileStackGuardedNoReturnDataCopyPlannedPrealloc?_runResult_existsSourceRun_exprNoOutOfFuelContracts_sufficientGas_X
    hSpec hExprNoSuccessfulOutOfFuel hInitialCodeImageRel
    hSourceFuelRun hCompileTarget hInitialMemory hInitialPerm

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    {cfg : Yul.Reference.StateRelConfig}
    {maxWords : Nat}
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {program : Yul.Program}
    {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {initial : Yul.EVMState}
    {referenceResult : Yul.Reference.Result}
    (hExprNoSuccessfulOutOfFuel :
      Yul.Program.RecursiveBridgeExprNoOutOfFuelContracts cfg program)
    (hInitialCodeImageRel :
      Yul.Program.RecursiveBridgeInitialCodeImageRel cfg program target shared
        initial)
    (hSourceFuelRun :
      ∃ sourceFuel,
        Yul.Program.RecursiveBridgeSourceRun program shared store sourceFuel
          referenceResult)
    (hCompileTarget :
      Yul.Program.compileStackGuardedNoReturnDataCopyPlannedPrealloc?
          maxWords program =
        some (range, asm, target))
    (hInitialMemory :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchInitialMemoryEmpty
        (Yul.Program.canonicalEntryState initial).toMachineState)
    (hInitialPerm : initial.executionEnv.perm = true) :
    Yul.Program.StackGuardedPlannedPreallocNoOutOfGasConclusion cfg range
      program asm target shared store initial referenceResult :=
  Yul.Program.compileStackGuardedNoReturnDataCopyPlannedPrealloc?_runResult_existsSourceRun_exprNoOutOfFuelContracts_sufficientGas_no_out_of_gas_X
    hSpec hExprNoSuccessfulOutOfFuel hInitialCodeImageRel
    hSourceFuelRun hCompileTarget hInitialMemory hInitialPerm

example :=
  Yul.Program.compileCheckedWithAdaptiveSpillSourceOwnedAssemblyTarget?

example :=
  @Yul.Program.compileCheckedWithAdaptiveSpillSourceOwnedAssemblyTarget?_eq_some

example :=
  @Yul.Program.compileCheckedWithAdaptiveSpillSourceOwnedAssemblyTarget?_of_compileCheckedWithAdaptiveSpillSourceOwned?

example :=
  @Yul.Program.compileCheckedWithAdaptiveSpillSourceOwnedAssemblyTarget?_of_toObjects_compileBlockOpen?

example :=
  Yul.Program.compileCheckedWithAdaptiveSpillSourceOwnedAssemblyTargetBytecode?

example :=
  @Yul.Program.compileCheckedWithAdaptiveSpillSourceOwnedAssemblyTargetBytecode?_eq_some

example :=
  Yul.Program.compileCheckedWithAdaptiveSpillSourceOwnedAssemblyTargetBytecodeFeatures?

example :=
  @Yul.Program.compileCheckedWithAdaptiveSpillSourceOwnedAssemblyTargetBytecodeFeatures?_eq_some

example :=
  Yul.Program.compileCheckedWithAdaptiveSpillSourceOwnedAssemblyTargetBytecodeFeaturesSourceStatic?

example :=
  @Yul.Program.compileCheckedWithAdaptiveSpillSourceOwnedAssemblyTargetBytecodeFeaturesSourceStatic?_eq_some

example :=
  Yul.Program.compileCheckedWithAdaptiveSpillSourceOwnedAssemblyTargetBytecodeFeaturesSourceStaticNoReturnDataCopy?

example :=
  @Yul.Program.compileCheckedWithAdaptiveSpillSourceOwnedAssemblyTargetBytecodeFeaturesSourceStaticNoReturnDataCopy?_eq_some

example :=
  @Yul.Program.compileCheckedWithAdaptiveSpillSourceOwnedAssemblyTargetBytecodeFeaturesSourceStaticNoReturnDataCopy?_compileAdaptive

example :=
  @Yul.Program.compileCheckedWithAdaptiveSpillSourceOwnedAssemblyTargetBytecodeFeaturesSourceStaticNoReturnDataCopy?_assemblyCompile

example :=
  @Yul.Program.compileCheckedWithAdaptiveSpillSourceOwnedAssemblyTargetBytecodeFeaturesSourceStaticNoReturnDataCopy?_jumpdestCorrect

example :=
  @Yul.Program.compileCheckedWithAdaptiveSpillSourceOwnedAssemblyTargetBytecodeFeaturesSourceStaticNoReturnDataCopy?_targetFitsDecodeWindow

example :=
  @Yul.Program.compileCheckedWithAdaptiveSpillSourceOwnedAssemblyTargetBytecodeFeaturesSourceStaticNoReturnDataCopy?_decodeSafety

example :=
  @Yul.Program.compileCheckedWithAdaptiveSpillSourceOwnedAssemblyTargetBytecodeFeaturesSourceStaticNoReturnDataCopy?_blockReplayNoReturnDataCopy

example :=
  @Yul.Program.compileCheckedWithAdaptiveSpillSourceOwnedAssemblyTargetBytecodeFeaturesSourceStaticNoReturnDataCopy?_noCallCreate

example :=
  @Yul.Program.compileCheckedWithAdaptiveSpillSourceOwnedAssemblyTargetBytecodeFeaturesSourceStaticNoReturnDataCopy?_blockReplayNoCallCreate

example :=
  @Yul.Program.compileCheckedWithAdaptiveSpillSourceOwnedAssemblyTargetBytecodeFeaturesSourceStaticNoReturnDataCopy?_blockPathChecks_of_core

example :=
  @Yul.Program.compileCheckedWithAdaptiveSpillSourceOwnedAssemblyTargetBytecodeFeaturesSourceStaticNoReturnDataCopy?_source_observations_targetFacts

example :=
  Yul.Program.compileCheckedWithAdaptiveSpillSourceOwnedAssemblyTargetBytecodeFeaturesSourceStaticAssemblyInferredBoundStackSafeNoReturnDataCopy?

example :=
  @Yul.Program.compileCheckedWithAdaptiveSpillSourceOwnedAssemblyTargetBytecodeFeaturesSourceStaticAssemblyInferredBoundStackSafeNoReturnDataCopy?_eq_some

example :=
  @Yul.Program.compileCheckedWithAdaptiveSpillSourceOwnedAssemblyTargetBytecodeFeaturesSourceStaticAssemblyInferredBoundStackSafeNoReturnDataCopy?_of_noReturnDataCopy

example :=
  @Yul.Program.compileCheckedWithAdaptiveSpillSourceOwnedAssemblyTargetBytecodeFeaturesSourceStaticAssemblyInferredBoundStackSafeNoReturnDataCopy?_base

example :=
  @Yul.Program.compileCheckedWithAdaptiveSpillSourceOwnedAssemblyTargetBytecodeFeaturesSourceStaticAssemblyInferredBoundStackSafeNoReturnDataCopy?_assemblyCompile

example :=
  @Yul.Program.compileCheckedWithAdaptiveSpillSourceOwnedAssemblyTargetBytecodeFeaturesSourceStaticAssemblyInferredBoundStackSafeNoReturnDataCopy?_assemblyBoundCheck

example :=
  @Yul.Program.compileCheckedWithAdaptiveSpillSourceOwnedAssemblyTargetBytecodeFeaturesSourceStaticAssemblyInferredBoundStackSafeNoReturnDataCopy?_assemblyBoundCheck_checked

example :=
  @Yul.Program.compileCheckedWithAdaptiveSpillSourceOwnedAssemblyTargetBytecodeFeaturesSourceStaticAssemblyInferredBoundStackSafeNoReturnDataCopy?_actualEVMStackHeadroomBound

example :=
  @Yul.Program.adaptiveSpillStackSafe_actualEVMHeadroomPoints

example :=
  @Yul.Program.compileCheckedWithAdaptiveSpillSourceOwnedAssemblyTargetBytecodeFeaturesSourceStaticAssemblyInferredBoundStackSafeNoReturnDataCopy?_sourceLowered_sufficientGas_X

example :=
  @Yul.Program.sourceLowered_run_of_dispatcher_source_result_block_bridge

example :=
  @Yul.Program.compileCheckedWithAdaptiveSpillSourceOwnedAssemblyTargetBytecodeFeaturesSourceStaticAssemblyInferredBoundStackSafeNoReturnDataCopy?_referenceRun_sufficientGas_X

example :=
  @Yul.Program.compileCheckedWithAdaptiveSpillSourceOwnedAssemblyTargetBytecodeFeaturesSourceStaticAssemblyInferredBoundStackSafeNoReturnDataCopy?_runResult_sufficientGas_X

end YulAdaptiveSpillTargetBoundary

end
end StackGuardAudit
end EvmCompiler
