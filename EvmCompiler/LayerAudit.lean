import EvmCompiler.Assembly.GasAware
import EvmCompiler.Yul.Preservation
import EvmCompiler.Yul.RecursiveBridgeSupport

/-!
Current public theorem spine.

This module intentionally exposes only the preferred public proof roots for the
imported-Yul spine and the gas-aware assembly bridge. Solidity and
object/Yul-object interfaces live in their own modules; this audit file should
not keep stale theorem routes alive.

The main imported-Yul boundary is the CALL-open spine. It admits ordinary
`CALL` in the checked source/compile boundary and relates the Yul/target CALL
request plus every shared response at the primitive EVM boundary. The older
closed no-CALL gas-aware `EVM.X` route remains in its implementation module
while the open whole-program EVM runner is being composed, but it is no longer
exported from this public audit spine.
-/

namespace EvmCompiler
namespace LayerAudit

namespace AssemblyGasOracleBoundary

/--
Lowest public gas-oracle bridge.

This is the checked replacement shape for the old gasless-trace adequacy
premise: the assembly run itself is oracle-parametric, so `GAS` observations
are fixed before the bridge to gas-aware `EVM.X`.
-/
theorem compileWholeProgramResultToGasAwareEVMWithGasOracle
    {program : Assembly.Program}
    {target : Assembly.TargetProgram}
    {oracle : Assembly.GasParametric.GasOracle}
    {fuel gas cursor cursorFinal : Nat}
    {initial : Yul.EVMState}
    {targetResult : Assembly.StepResult}
    (hCompile : Assembly.compile? program = some target)
    (hDecodeWindow : Assembly.Bytecode.TargetFitsDecodeWindow target)
    (hJumpdestCorrect : Assembly.Bytecode.JumpdestCorrect target)
    (hRun :
      Assembly.GasParametric.sourceRunNResultWithGasOracle program oracle
          fuel cursor initial =
        .ok (targetResult, cursorFinal))
    (hTargetOracleForX :
      Assembly.GasAware.XOracleResultPreconditionAssumptions target initial
        gas oracle cursor targetResult cursorFinal) :
    Assembly.Accepted program ∧
      Assembly.Bytecode.compileBytes? program =
        some (Assembly.Bytecode.encodeTarget target) ∧
        Assembly.Bytecode.EncodingCorrect target
          (Assembly.Bytecode.encodeTarget target) ∧
          target.GasOpcodeBoundary ∧
            Assembly.GasParametric.BlockTraceResult program target oracle
              fuel cursor initial targetResult cursorFinal ∧
              Assembly.GasAware.TargetOracleResultRun target oracle cursor
                initial targetResult cursorFinal ∧
              hTargetOracleForX.gasBound ≤ gas ∧
                gas < EvmYul.UInt256.size ∧
                  ∃ result,
                    EvmYul.EVM.X hTargetOracleForX.evmFuel
                        (Assembly.GasAware.validJumps target)
                        (Assembly.GasAware.installCodeAndGas target gas
                          initial) =
                      .ok result ∧
                      Assembly.GasAware.XResultAgrees targetResult result :=
  Assembly.GasAware.compile_whole_program_result_X_withGasOracle
    hCompile hDecodeWindow hJumpdestCorrect hRun hTargetOracleForX

/--
Public lowered-Yul GAS-oracle bridge.

This composes the checked lowered-Yul compiler theorem with the oracle-parametric
assembly bytecode bridge. The old closed route asked for an `EVM.X` agreement
callback over a gasless block trace; this theorem exposes the stronger shape:
the source and compiled assembly first agree under the same explicit `GAS`
oracle and cursor, and only then is the remaining gas-aware `EVM.X` adequacy
package consumed for that oracle-parametric assembly result.
-/
theorem compileCheckedLoweredYulToGasAwareEVMWithGasOracle
    {program : Yul.Program}
    {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    {oracle : Assembly.GasParametric.GasOracle}
    {fuel gas cursor cursorFinal : Nat}
    {initial : Yul.EVMState}
    {outcome : Yul.Outcome}
    (hYulCompile : program.compileCheckedWithGasOracle? = some asm)
    (hAsmCompile : Assembly.compile? asm = some target)
    (hDecodeWindow : Assembly.Bytecode.TargetFitsDecodeWindow target)
    (hJumpdestCorrect : Assembly.Bytecode.JumpdestCorrect target)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hRun :
      Yul.Lowered.runWithGasOracle fuel program oracle cursor initial =
        .ok (outcome, cursorFinal))
    (hTargetOracleForX :
      ∀ {targetFuel targetOutcome},
        Assembly.GasParametric.sourceRunNResultWithGasOracle asm oracle
            targetFuel cursor initial =
          .ok (targetOutcome, cursorFinal) →
        Structured.Preservation.WholeProgramOutcomeRel outcome targetOutcome →
        Assembly.GasAware.XOracleResultPreconditionAssumptions target initial
          gas oracle cursor targetOutcome cursorFinal) :
    ∃ targetFuel targetOutcome,
      ∃ hTargetRun :
        Assembly.GasParametric.sourceRunNResultWithGasOracle asm oracle
            targetFuel cursor initial =
          .ok (targetOutcome, cursorFinal),
      ∃ hOutcomeRel :
        Structured.Preservation.WholeProgramOutcomeRel outcome targetOutcome,
        Assembly.Accepted asm ∧
          Assembly.Bytecode.compileBytes? asm =
            some (Assembly.Bytecode.encodeTarget target) ∧
          Assembly.Bytecode.EncodingCorrect target
            (Assembly.Bytecode.encodeTarget target) ∧
            target.GasOpcodeBoundary ∧
              Assembly.GasParametric.BlockTraceResult asm target oracle
                targetFuel cursor initial targetOutcome cursorFinal ∧
              Assembly.GasAware.TargetOracleResultRun target oracle cursor
                initial targetOutcome cursorFinal ∧
              (hTargetOracleForX
                  (targetFuel := targetFuel) (targetOutcome := targetOutcome)
                  hTargetRun hOutcomeRel).gasBound ≤ gas ∧
                gas < EvmYul.UInt256.size ∧
                  ∃ result,
                    EvmYul.EVM.X
                        (hTargetOracleForX
                          (targetFuel := targetFuel)
                          (targetOutcome := targetOutcome)
                          hTargetRun hOutcomeRel).evmFuel
                        (Assembly.GasAware.validJumps target)
                        (Assembly.GasAware.installCodeAndGas target gas
                          initial) =
                      .ok result ∧
                      Assembly.GasAware.XResultAgrees targetOutcome result := by
  obtain ⟨targetFuel, targetOutcome, hTargetRun, hOutcomeRel⟩ :=
    Yul.Program.compile_preserves_of_compileCheckedWithGasOracle
      hYulCompile hInitialPc hRun
  let hTargetOracleForX' :
      Assembly.GasAware.XOracleResultPreconditionAssumptions target initial
        gas oracle cursor targetOutcome cursorFinal :=
    hTargetOracleForX hTargetRun hOutcomeRel
  obtain
    ⟨hAccepted, hBytes, hEncoding, hGasBoundary, hTrace, hTargetOracleRun,
      hRunsAbove⟩ :=
    compileWholeProgramResultToGasAwareEVMWithGasOracle
      hAsmCompile hDecodeWindow hJumpdestCorrect hTargetRun
      hTargetOracleForX'
  refine
    ⟨targetFuel, targetOutcome, hTargetRun, hOutcomeRel, hAccepted, hBytes,
      hEncoding, hGasBoundary, hTrace, hTargetOracleRun, ?_⟩
  simpa [hTargetOracleForX'] using hRunsAbove

/--
Witness that a lowered-Yul source run used some concrete stream of `GAS`
answers.

The callback is still the unfinished lower replay boundary.  It should
eventually be produced by proving that a concrete gasful `EVM.X` run induces
the same `oracle` values at the dynamic `GAS` instructions.
-/
structure LoweredYulGasOracleRunWitness
    (program : Yul.Program) (asm : Assembly.Program)
    (target : Assembly.TargetProgram)
    (fuel gas cursor : Nat) (initial : Yul.EVMState) where
  oracle : Assembly.GasParametric.GasOracle
  cursorFinal : Nat
  outcome : Yul.Outcome
  sourceRun :
    Yul.Lowered.runWithGasOracle fuel program oracle cursor initial =
      .ok (outcome, cursorFinal)
  targetOracleForX :
    ∀ {targetFuel targetOutcome},
      Assembly.GasParametric.sourceRunNResultWithGasOracle asm oracle
          targetFuel cursor initial =
        .ok (targetOutcome, cursorFinal) →
      Structured.Preservation.WholeProgramOutcomeRel outcome targetOutcome →
      Assembly.GasAware.XOracleResultPreconditionAssumptions target initial
        gas oracle cursor targetOutcome cursorFinal

/--
Public lowered-Yul bridge with the `GAS` answers existentially exposed.

`oracle : Nat → Word` is the answer stream: at each dynamic `GAS` instruction,
the current cursor selects the word to push and then advances by one.  This
wrapper is the source-facing shape we want at the EVM boundary: for a concrete
installed gas amount, the source run may use some finite stream of `GAS`
answers, and the compiled bytecode agrees with that same stream.

The remaining callback is the still-unproved lower replay package: it must be
replaced by a theorem showing that a concrete gasful `EVM.X` execution induces
exactly this oracle stream for the `GAS` requests it performs.
-/
theorem compileCheckedLoweredYulToGasAwareEVMWithSomeGasOracle
    {program : Yul.Program}
    {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    {fuel gas cursor : Nat}
    {initial : Yul.EVMState}
    (hYulCompile : program.compileCheckedWithGasOracle? = some asm)
    (hAsmCompile : Assembly.compile? asm = some target)
    (hDecodeWindow : Assembly.Bytecode.TargetFitsDecodeWindow target)
    (hJumpdestCorrect : Assembly.Bytecode.JumpdestCorrect target)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hOracleRun :
      LoweredYulGasOracleRunWitness program asm target fuel gas cursor initial) :
    ∃ oracle cursorFinal outcome targetFuel targetOutcome,
      Yul.Lowered.runWithGasOracle fuel program oracle cursor initial =
        .ok (outcome, cursorFinal) ∧
      Assembly.GasParametric.sourceRunNResultWithGasOracle asm oracle
          targetFuel cursor initial =
        .ok (targetOutcome, cursorFinal) ∧
      Structured.Preservation.WholeProgramOutcomeRel outcome targetOutcome ∧
      Assembly.Accepted asm ∧
      Assembly.Bytecode.compileBytes? asm =
        some (Assembly.Bytecode.encodeTarget target) ∧
      Assembly.Bytecode.EncodingCorrect target
        (Assembly.Bytecode.encodeTarget target) ∧
      target.GasOpcodeBoundary ∧
      Assembly.GasParametric.BlockTraceResult asm target oracle targetFuel
        cursor initial targetOutcome cursorFinal ∧
      Assembly.GasAware.TargetOracleResultRun target oracle cursor initial
        targetOutcome cursorFinal ∧
      ∃ gasBound evmFuel result,
        gasBound ≤ gas ∧
        gas < EvmYul.UInt256.size ∧
        EvmYul.EVM.X evmFuel
            (Assembly.GasAware.validJumps target)
            (Assembly.GasAware.installCodeAndGas target gas initial) =
          .ok result ∧
        Assembly.GasAware.XResultAgrees targetOutcome result := by
  obtain ⟨targetFuel, targetOutcome, hTargetRun, hOutcomeRel⟩ :=
    Yul.Program.compile_preserves_of_compileCheckedWithGasOracle
      hYulCompile hInitialPc hOracleRun.sourceRun
  let hPreconditions :
      Assembly.GasAware.XOracleResultPreconditionAssumptions target initial
        gas hOracleRun.oracle cursor targetOutcome hOracleRun.cursorFinal :=
    hOracleRun.targetOracleForX hTargetRun hOutcomeRel
  obtain
    ⟨hAccepted, hBytes, hEncoding, hGasBoundary, hTrace, hTargetOracleRun,
      hGasLe, hGasFits, hXRun⟩ :=
    compileWholeProgramResultToGasAwareEVMWithGasOracle
      hAsmCompile hDecodeWindow hJumpdestCorrect hTargetRun hPreconditions
  rcases hXRun with ⟨result, hEVMRun, hAgrees⟩
  refine
    ⟨hOracleRun.oracle, hOracleRun.cursorFinal, hOracleRun.outcome,
      targetFuel, targetOutcome, hOracleRun.sourceRun, hTargetRun,
      hOutcomeRel, hAccepted, hBytes, hEncoding, hGasBoundary,
      hTrace, hTargetOracleRun, hPreconditions.gasBound,
      hPreconditions.evmFuel, result, hGasLe, hGasFits, hEVMRun, hAgrees⟩

end AssemblyGasOracleBoundary

namespace ImportedYulBoundary

/--
Main checked compile/source boundary for the imported-Yul spine.

This is CALL-open: it admits ordinary `CALL` and still excludes the external
families not yet handled by the open proof.
-/
noncomputable abbrev compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStatic? :=
  Yul.Program.compileCheckedAssemblyTargetBytecodeResourcesCALLFeaturesSourceStatic?

/--
Public top package for the main imported-Yul spine.  It keeps source validity,
CALL feature coverage, compile resources, the checked target, and the open-CALL
semantic contracts in one place without converting through the old closed
no-CALL package.
-/
abbrev recursiveBridgeTopAssumptions :=
  @Yul.Program.RecursiveBridgeTopAssumptions

/--
Open sequence frontier that the recursive CALL spine is being composed toward:
source execution is `YulOpen.execSeq`, target execution is `CompilerOpen`, and
responses are the same opaque response with a relation-preserving reentrant
mutation.
-/
abbrev recursiveBridgeOpenSeqLoweringFrontierAt :=
  @Yul.Reference.SourceBridgeFacts.CALLOpenSeqLoweringFrontierAt

/--
Admissibility predicate for an open external response: returned data/status are
unconstrained, and the opaque reentrant mutation must preserve related chain
state.
-/
abbrev recursiveBridgeOpenExternalResponsePreservesChainRel :=
  @Yul.Reference.SourceBridgeFacts.OpenExternalResponsePreservesChainRel

/--
Canonical CALL-spine response relation used by the open sequence frontier.
-/
abbrev recursiveBridgeRelationPreservingCallResponseRel :=
  @Yul.Reference.SourceBridgeFacts.SourceOpenSeqRelationPreservingCallResponseRel

/--
Adapter from the canonical relation-preserving response predicate to the local
per-CALL `OpenExternalResponseRel` needed by CALL-head continuations.
-/
abbrev recursiveBridgeRelationPreservingCallResponseToOpenExternalResponse :=
  @Yul.Reference.SourceBridgeFacts.SourceOpenSeqRelationPreservingCallResponseRel.to_openExternalResponseRel

/--
Weakening for exact open sequence soundness: an already checked proof can be
reused under a stricter per-call response relation.
-/
abbrev recursiveBridgeOpenSeqSoundExactMonoCallResponse :=
  @Yul.Reference.SourceBridgeFacts.SourceOpenResultSeqSoundAtExactHiddenCtx.mono_call_response

/--
Weakening for existential-target open sequence soundness, matching the public
frontier shape.
-/
abbrev recursiveBridgeOpenSeqSoundWhenMonoCallResponse :=
  @Yul.Reference.SourceBridgeFacts.SourceOpenResultSeqSoundWhenAtExactHiddenCtx.mono_call_response

/--
Weakening for checked exact-target open sequence lowering under a stricter
per-call response relation.
-/
abbrev recursiveBridgeCheckedOpenSeqExactMonoCallResponse :=
  @Yul.Reference.SourceBridgeFacts.CheckedOpenSeqLoweringSoundAtExactTargetWhenFreshNamesAtCompileFuelHiddenCtx.mono_call_response

/--
Weakening for checked open sequence lowering under a stricter per-call response
relation.
-/
abbrev recursiveBridgeCheckedOpenSeqWhenMonoCallResponse :=
  @Yul.Reference.SourceBridgeFacts.CheckedOpenSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx.mono_call_response

/--
Fuel-zero base for the open sequence spine: target failure is allowed only when
the source result is outside the allowed observation set.
-/
abbrev recursiveBridgeOpenSeqSoundWhenZero :=
  @Yul.Reference.SourceBridgeFacts.SourceOpenResultSeqSoundWhenAtExactHiddenCtx.zero

/--
Checked fuel-zero base for open sequence lowering.
-/
abbrev recursiveBridgeCheckedOpenSeqZero :=
  @Yul.Reference.SourceBridgeFacts.CheckedOpenSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx.zero

/--
Checked empty-sequence base for open sequence lowering under layout support.
-/
abbrev recursiveBridgeCheckedOpenSeqNilSupported :=
  @Yul.Reference.SourceBridgeFacts.CheckedOpenSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx.nil_of_supported

/--
Generic list-induction shell for the checked open sequence spine. Concrete
CALL-aware head constructors still have to supply its `hCons` premise.
-/
abbrev recursiveBridgeCheckedOpenSeqOfConsFrontier :=
  @Yul.Reference.SourceBridgeFacts.checkedOpenSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_of_cons_frontier_reserved_supported

/--
Specialized constructor for the public `CALLOpenSeqLoweringFrontierAt` shape.
-/
abbrev recursiveBridgeOpenSeqFrontierOfConsFrontier :=
  @Yul.Reference.SourceBridgeFacts.CALLOpenSeqLoweringFrontierAt.of_cons_frontier_reserved_supported

/--
Handler-aware typed-continuation frontier for the CALL-admitting recursive
spine.  This remains paired with the open sequence frontier while the recursive
CALL composition is completed.
-/
abbrev recursiveBridgeSeqKontFrontierAt :=
  @Yul.Reference.SourceBridgeFacts.CALLSeqKontFrontierAt

/--
Checked constructor for the public CALL top package.
-/
abbrev recursiveBridgeTopAssumptionsOfChecked :=
  @Yul.Program.RecursiveBridgeTopAssumptions.of_checkedCALLFeaturesSourceStatic

/--
The CALL spine's direct Yul-open-result/EVM-open-result boundary after a
generated argument prelude has produced the related post-argument state.
-/
abbrev recursiveBridgeOpenPrimitiveEVMResultRelOfArgStackPreludeCallKind :=
  @Yul.Program.RecursiveBridgeTopAssumptions.openPrimitiveEVMResultRel_of_argStackPrelude_callKind

/--
CALL expression-prelude contract that consumes completed `YulOpen.evalArgs`
evidence directly, instead of asking callers to route through closed
`EvmYul.Yul.evalArgs`.
-/
abbrev recursiveBridgeOpenPrimitiveCallExprOpenPreludeSoundAt :=
  @Yul.Reference.SourceBridgeFacts.OpenPrimitiveCallExprOpenPreludeSoundAt

/--
Checked lowerer wrapper for the open-argument CALL expression-prelude contract.
-/
abbrev recursiveBridgeLower1PrimOpenPrimitiveCallExprOpenPrelude :=
  @Yul.Reference.SourceBridgeFacts.lower1?_prim_openPrimitiveCallExprOpenPreludeSoundAt_of_lowerBound1?_preludeRegularAt_callKind

/--
CALL assignment statement-prelude contract that consumes completed
`YulOpen.evalArgs` evidence directly.
-/
abbrev recursiveBridgeOpenPrimitiveCallAssignStmtOpenPreludeSoundAt :=
  @Yul.Reference.SourceBridgeFacts.OpenPrimitiveCallAssignStmtOpenPreludeSoundAt

/--
CALL declaration statement-prelude contract that consumes completed
`YulOpen.evalArgs` evidence directly.
-/
abbrev recursiveBridgeOpenPrimitiveCallLetStmtOpenPreludeSoundAt :=
  @Yul.Reference.SourceBridgeFacts.OpenPrimitiveCallLetStmtOpenPreludeSoundAt

/--
Checked assignment lowering into the open-argument CALL statement-prelude
contract.
-/
abbrev recursiveBridgeLowerAssignPrimOpenPrimitiveCallStmtOpenPrelude :=
  @Yul.Reference.SourceBridgeFacts.toFunctionsListFuel?_assign_prim_openPrimitiveCallStmtOpenPreludeSoundAt_of_lowerBound1?_preludeRegularAt_callKind

/--
Checked declaration lowering into the open-argument CALL statement-prelude
contract.
-/
abbrev recursiveBridgeLowerLetPrimOpenPrimitiveCallStmtOpenPrelude :=
  @Yul.Reference.SourceBridgeFacts.toFunctionsListFuel?_let_prim_openPrimitiveCallStmtOpenPreludeSoundAt_of_lowerBound1?_preludeRegularAt_callKind

/--
CALL-safe checked assignment lowering into the open-argument CALL statement
boundary, with the open argument-domain proof constructed internally.
-/
abbrev recursiveBridgeCallSafeLowerAssignPrimOpenPrimitiveCallStmtOpenPrelude :=
  @Yul.Reference.SourceBridgeFacts.toFunctionsListFuel?_assign_prim_openPrimitiveCallStmtOpenPreludeSoundAt_of_callSafeCheckedAt_lowerBound1?_toStackSeq

/--
CALL-safe checked declaration lowering into the open-argument CALL statement
boundary, with the open argument-domain proof constructed internally.
-/
abbrev recursiveBridgeCallSafeLowerLetPrimOpenPrimitiveCallStmtOpenPrelude :=
  @Yul.Reference.SourceBridgeFacts.toFunctionsListFuel?_let_prim_openPrimitiveCallStmtOpenPreludeSoundAt_of_callSafeCheckedAt_lowerBound1?_toStackSeq

/--
CALL assignment sequence-prelude contract that consumes completed
`YulOpen.evalArgs` evidence directly, keeping the tail continuation at the
existing hidden-context sequence boundary.
-/
abbrev recursiveBridgeOpenPrimitiveCallAssignSeqOpenPreludeSoundAt :=
  @Yul.Reference.SourceBridgeFacts.OpenPrimitiveCallAssignSeqOpenPreludeSoundAt

/--
CALL declaration sequence-prelude contract that consumes completed
`YulOpen.evalArgs` evidence directly, keeping the tail continuation at the
existing hidden-context sequence boundary.
-/
abbrev recursiveBridgeOpenPrimitiveCallLetSeqOpenPreludeSoundAt :=
  @Yul.Reference.SourceBridgeFacts.OpenPrimitiveCallLetSeqOpenPreludeSoundAt

/--
Checked assignment sequence lowering into the open-argument CALL prelude
contract.
-/
abbrev recursiveBridgeLowerAssignPrimOpenPrimitiveCallSeqOpenPrelude :=
  @Yul.Reference.SourceBridgeFacts.toFunctionsListFuel?_assign_prim_openPrimitiveCallSeqOpenPreludeSoundAt_of_lowerBound1?_preludeRegularAt_callKind

/--
Checked declaration sequence lowering into the open-argument CALL prelude
contract.
-/
abbrev recursiveBridgeLowerLetPrimOpenPrimitiveCallSeqOpenPrelude :=
  @Yul.Reference.SourceBridgeFacts.toFunctionsListFuel?_let_prim_openPrimitiveCallSeqOpenPreludeSoundAt_of_lowerBound1?_preludeRegularAt_callKind

/--
CALL-safe checked assignment sequence lowering into the open-argument CALL
prelude contract, with the open argument-domain proof constructed internally.
-/
abbrev recursiveBridgeCallSafeLowerAssignPrimOpenPrimitiveCallSeqOpenPrelude :=
  @Yul.Reference.SourceBridgeFacts.toFunctionsListFuel?_assign_prim_openPrimitiveCallSeqOpenPreludeSoundAt_of_callSafeCheckedAt_lowerBound1?_toStackSeq

/--
CALL-safe checked declaration sequence lowering into the open-argument CALL
prelude contract, with the open argument-domain proof constructed internally.
-/
abbrev recursiveBridgeCallSafeLowerLetPrimOpenPrimitiveCallSeqOpenPrelude :=
  @Yul.Reference.SourceBridgeFacts.toFunctionsListFuel?_let_prim_openPrimitiveCallSeqOpenPreludeSoundAt_of_callSafeCheckedAt_lowerBound1?_toStackSeq

/--
Program-accepted assignment sequence lowering into the open-argument CALL
prelude contract, with the open argument-domain proof constructed internally.
-/
abbrev recursiveBridgeProgramAcceptedLowerAssignPrimOpenPrimitiveCallSeqOpenPrelude :=
  @Yul.Reference.SourceBridgeFacts.toFunctionsListFuel?_assign_prim_openPrimitiveCallSeqOpenPreludeSoundAt_of_programCALLAccepted_lowerBound1?_toStackSeq

/--
Program-accepted declaration sequence lowering into the open-argument CALL
prelude contract, with the open argument-domain proof constructed internally.
-/
abbrev recursiveBridgeProgramAcceptedLowerLetPrimOpenPrimitiveCallSeqOpenPrelude :=
  @Yul.Reference.SourceBridgeFacts.toFunctionsListFuel?_let_prim_openPrimitiveCallSeqOpenPreludeSoundAt_of_programCALLAccepted_lowerBound1?_toStackSeq

/--
Actual `YulOpen.execSeq` assignment-CALL head related to the emitted
compiler-open assignment sequence, after the generated argument prelude has
completed and with a real open tail.
-/
abbrev recursiveBridgeYulOpenExecSeqAssignCallCompilerOpenOpenSeqResult :=
  @Yul.Reference.SourceBridgeFacts.yulOpen_execSeq_assign_call_compilerOpen_openSeqOpenResultRel_of_arg_prelude_done_callKind

/--
Actual assignment-CALL sequence head with an abstract tail response relation,
so later tail calls are not forced to reuse the outer call's pre-state response
predicate.
-/
abbrev recursiveBridgeYulOpenExecSeqAssignCallCompilerOpenOpenSeqResultWithCallResponse :=
  @Yul.Reference.SourceBridgeFacts.yulOpen_execSeq_assign_call_compilerOpen_openSeqOpenResultRel_of_arg_prelude_done_callKind_with_callResponseRel

/--
Actual assignment-CALL sequence head specialized to the canonical
relation-preserving shared-response predicate.
-/
abbrev recursiveBridgeYulOpenExecSeqAssignCallCompilerOpenOpenSeqResultRelationPreserving :=
  @Yul.Reference.SourceBridgeFacts.yulOpen_execSeq_assign_call_compilerOpen_openSeqOpenResultRel_of_arg_prelude_done_callKind_relationPreserving

/--
Actual `YulOpen.execSeq` declaration-CALL head related to the emitted
compiler-open declaration sequence, after the generated argument prelude has
completed and with a real open tail.
-/
abbrev recursiveBridgeYulOpenExecSeqLetCallCompilerOpenOpenSeqResult :=
  @Yul.Reference.SourceBridgeFacts.yulOpen_execSeq_let_call_compilerOpen_openSeqOpenResultRel_of_arg_prelude_done_callKind

/--
Actual declaration-CALL sequence head with an abstract tail response relation,
matching the assignment-head hook above.
-/
abbrev recursiveBridgeYulOpenExecSeqLetCallCompilerOpenOpenSeqResultWithCallResponse :=
  @Yul.Reference.SourceBridgeFacts.yulOpen_execSeq_let_call_compilerOpen_openSeqOpenResultRel_of_arg_prelude_done_callKind_with_callResponseRel

/--
Actual declaration-CALL sequence head specialized to the canonical
relation-preserving shared-response predicate.
-/
abbrev recursiveBridgeYulOpenExecSeqLetCallCompilerOpenOpenSeqResultRelationPreserving :=
  @Yul.Reference.SourceBridgeFacts.yulOpen_execSeq_let_call_compilerOpen_openSeqOpenResultRel_of_arg_prelude_done_callKind_relationPreserving

/--
CALL-capable relation for lowered argument-expression evaluation before it is
wrapped into a generated prelude result.
-/
abbrev recursiveBridgeArgStackOpenArgsResultRelWith :=
  @Yul.Reference.SourceBridgeFacts.SourceArgStackOpenArgsResultRelWith

/--
Empty lowered-argument constructor for the CALL-capable argument-expression
relation.  This is the base case used by the generated-prelude spine.
-/
abbrev recursiveBridgeArgStackOpenArgsResultRelNil :=
  @EvmCompiler.Yul.Reference.SourceBridgeFacts.SourceArgStackOpenArgsResultRelWith.nil

/--
Completed lowered-argument constructor for the CALL-capable argument-expression
relation, from completed open Yul arguments and completed compiler-open lowered
arguments with matching values and related final states.
-/
abbrev recursiveBridgeArgStackOpenArgsResultRelDoneOkOfOpenParts :=
  @EvmCompiler.Yul.Reference.SourceBridgeFacts.SourceArgStackOpenArgsResultRelWith.done_ok_of_open_parts

/--
Response-relation weakening for lowered argument evaluation.  This keeps nested
CALL argument proofs composable when the outer spine changes the admissible
shared-response predicate by proof.
-/
abbrev recursiveBridgeArgStackOpenArgsResultRelMonoCallResponse :=
  @EvmCompiler.Yul.Reference.SourceBridgeFacts.SourceArgStackOpenArgsResultRelWith.mono_call_response

/--
CALL-capable generated-prelude result relation.  Unlike the older constant
response-predicate wrapper, this lets nested argument CALLs choose the response
relation from the suspended source/target call pair.
-/
abbrev recursiveBridgeArgStackPreludeOpenResultRelWith :=
  @Yul.Reference.SourceBridgeFacts.SourceArgStackPreludeOpenResultRelWith

/--
CALL-capable generated-prelude pre-result relation.  This is the suspension
bridge for CALLs reached while executing the generated argument prelude itself,
before the final generated argument readback.
-/
abbrev recursiveBridgeArgStackPreludeOpenPreDoneRelWith :=
  @Yul.Reference.SourceBridgeFacts.SourceArgStackPreludeOpenPreDoneRelWith

/--
Constructor from completed lowered-argument evaluation to the generated-prelude
pre-result relation when the generated prelude has already returned regularly.
-/
abbrev recursiveBridgeArgStackPreludeOpenPreDoneRelOfRegularArgs :=
  @Yul.Reference.SourceBridgeFacts.SourceArgStackPreludeOpenPreDoneRelWith.of_regular_args

/--
Completed generated-prelude pre-result constructor for the CALL-open spine,
from actual completed open argument evaluation, completed generated-prelude
execution, and a CALL-capable lowered-argument relation.
-/
abbrev recursiveBridgeArgStackPreludeOpenPreDoneRelDoneOkOfOpenParts :=
  @Yul.Reference.SourceBridgeFacts.SourceArgStackPreludeOpenPreDoneRelWith.done_ok_of_open_parts

/--
Completed generated-prelude pre-result constructor that builds the lowered
argument relation directly from completed open source/target argument runs.
-/
abbrev recursiveBridgeArgStackPreludeOpenPreDoneRelDoneOkOfCompletedOpenArgs :=
  @Yul.Reference.SourceBridgeFacts.SourceArgStackPreludeOpenPreDoneRelWith.done_ok_of_completed_open_args

/--
Response-relation weakening for the generated-prelude pre-result done relation,
threading the same proof through the final lowered-argument readback.
-/
abbrev recursiveBridgeArgStackPreludeOpenPreDoneRelMonoArgsCallResponse :=
  @Yul.Reference.SourceBridgeFacts.SourceArgStackPreludeOpenPreDoneRelWith.mono_args_call_response

/--
Empty generated-prelude base for the CALL-open pre-result relation.
-/
abbrev recursiveBridgeArgStackPreludeOpenPreDoneRelNilSucc :=
  @Yul.Reference.SourceBridgeFacts.SourceArgStackPreludeOpenPreDoneRelWith.nil_succ

/--
Adapter from a CALL-capable lowered argument-expression relation into the
generated-prelude wrapper when the prelude statements have already completed.
-/
abbrev recursiveBridgeArgStackPreludeOpenResultRelOfOpenArgsDonePre :=
  @Yul.Reference.SourceBridgeFacts.SourceArgStackPreludeOpenResultRel.With.of_args_result_rel_done_pre

/--
Completed generated-prelude constructor for the CALL-capable wrapper.  This is
the call-pair-dependent version of the open-parts theorem, so nested CALLs do
not collapse into a single global response predicate.
-/
abbrev recursiveBridgeArgStackPreludeOpenResultRelDoneOkOfOpenParts :=
  @Yul.Reference.SourceBridgeFacts.SourceArgStackPreludeOpenResultRel.With.done_ok_of_open_parts

/--
Adapter from a CALL-capable generated-prelude relation into the full
`SourceArgPreludeOpen.run` wrapper when the generated prelude itself may
suspend and resume before the final argument readback.
-/
abbrev recursiveBridgeArgStackPreludeOpenResultRelOfPreResultRel :=
  @Yul.Reference.SourceBridgeFacts.SourceArgStackPreludeOpenResultRel.With.of_pre_result_rel

/--
Source-side stack-order reversal for the CALL-capable generated-prelude result
relation, with an explicit adapter for the wrapped suspended source call.
-/
abbrev recursiveBridgeArgStackPreludeOpenResultRelReverseSource :=
  @Yul.Reference.SourceBridgeFacts.SourceArgStackPreludeOpenResultRel.With.reverse_source

/--
Response-relation weakening for the full generated-prelude open-result wrapper.
-/
abbrev recursiveBridgeArgStackPreludeOpenResultRelMonoCallResponse :=
  @Yul.Reference.SourceBridgeFacts.SourceArgStackPreludeOpenResultRel.With.mono_call_response

/--
Empty generated-prelude base for the full CALL-open wrapper around
`SourceArgPreludeOpen.run`.
-/
abbrev recursiveBridgeArgStackPreludeOpenResultRelNilSucc :=
  @Yul.Reference.SourceBridgeFacts.SourceArgStackPreludeOpenResultRel.With.nil_succ

/--
Named source-side open result for the CALL-family primitive after argument
evaluation has produced the stack values.
-/
abbrev recursiveBridgeYulPrimitiveOpenResultAfterArgs :=
  @Yul.Reference.SourceBridgeFacts.yulPrimitiveOpenResultAfterArgs

/--
Evaluator-shape equation exposing `YulOpen.evalValues` for canonical
CALL-family operations as the open argument bind consumed by the CALL proof.
-/
abbrev recursiveBridgeYulOpenEvalValuesCallToYulOperationBindReversedArgs :=
  @Yul.Reference.SourceBridgeFacts.yulOpen_toOpenResult_evalValues_call_toYulOperation_eq_bind_reversed_args

/--
Completed-argument primitive CALL relation used as the done branch of the
fully open generated-prelude proof.
-/
abbrev recursiveBridgeOpenPrimitiveCallExprOpenResultRelOfReversedArgsDone :=
  @Yul.Reference.SourceBridgeFacts.openPrimitiveCallExprOpenResultRel_of_reversed_args_done_toYulOperation

/--
Suspension-compatible generated-prelude bridge into the outer CALL-family
primitive. This is the helper that carries nested generated-prelude CALL
suspensions through the concrete primitive boundary.
-/
abbrev recursiveBridgeOpenPrimitiveCallExprOpenResultRelOfReversedArgPreludeRel :=
  @Yul.Reference.SourceBridgeFacts.openPrimitiveCallExprOpenResultRel_of_reversed_arg_prelude_rel_toYulOperation

/--
Actual `YulOpen.evalValues` wrapper for the suspension-compatible generated
prelude bridge into the outer CALL-family primitive.
-/
abbrev recursiveBridgeOpenPrimitiveCallExprOpenResultRelOfReversedArgPreludeRelEvalValues :=
  @Yul.Reference.SourceBridgeFacts.openPrimitiveCallExprOpenResultRel_of_reversed_arg_prelude_rel_toYulOperation_evalValues

/--
The corresponding Yul/EVM open-call site relation for generated CALL argument
preludes.
-/
abbrev recursiveBridgeOpenPrimitiveEVMCallSoundOfArgStackPrelude :=
  @Yul.Program.RecursiveBridgeTopAssumptions.openPrimitiveEVMCallSound_of_argStackPrelude

end ImportedYulBoundary

end LayerAudit
end EvmCompiler
