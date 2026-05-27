import EvmCompiler.Yul.RecursiveBridgeSupport
import Batteries.Data.RBMap.Lemmas

namespace EvmCompiler
namespace Yul

namespace World

/--
Checked compiler/source boundary for external account code.

This deliberately omits `RecursiveBridgeFeatureCoverage`: that checker still
rejects the CALL-family features whose world semantics are being proved here.
External compiled accounts should nevertheless carry checked lower resource
facts and source-static acceptedness/scoping facts, so the recursive CALL proof
can later unpack them from the world relation instead of asking the caller for
callee proof evidence.
-/
noncomputable def compileCheckedAssemblyTargetBytecodeResourcesSourceStatic?
    (program : Program) :
    Option (Assembly.Program × Assembly.TargetProgram) :=
  match Program.compileCheckedAssemblyTargetBytecodeResources? program with
  | none => none
  | some (asm, target) =>
      if Program.RecursiveBridgeSourceStaticFacts.checked? program then
        some (asm, target)
      else
        none

theorem compileCheckedAssemblyTargetBytecodeResourcesSourceStatic?_eq_some
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    (hCompileTarget :
      compileCheckedAssemblyTargetBytecodeResourcesSourceStatic? program =
        some (asm, target)) :
    Program.compileCheckedAssemblyTargetBytecodeResources? program =
        some (asm, target) ∧
      Program.RecursiveBridgeSourceStaticFacts program := by
  unfold compileCheckedAssemblyTargetBytecodeResourcesSourceStatic?
    at hCompileTarget
  cases hBase :
      Program.compileCheckedAssemblyTargetBytecodeResources? program with
  | none =>
      simp [hBase] at hCompileTarget
  | some pair =>
      rcases pair with ⟨asm', target'⟩
      simp [hBase] at hCompileTarget
      cases hFacts :
          Program.RecursiveBridgeSourceStaticFacts.checked? program <;>
        simp [hFacts] at hCompileTarget
      rcases hCompileTarget with ⟨rfl, rfl⟩
      exact
        ⟨by simp,
          Program.RecursiveBridgeSourceStaticFacts.of_checked?
            (by simpa using hFacts)⟩

theorem compileCheckedAssemblyTargetBytecodeResourcesSourceStatic?_compileChecked
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    (hCompileTarget :
      compileCheckedAssemblyTargetBytecodeResourcesSourceStatic? program =
        some (asm, target)) :
    Program.compileChecked? program = some asm := by
  rcases
      compileCheckedAssemblyTargetBytecodeResourcesSourceStatic?_eq_some
        hCompileTarget with
    ⟨hResources, _hStatic⟩
  rcases Program.compileCheckedAssemblyTargetBytecodeResources?_eq_some
      hResources with
    ⟨hBytecode, _hResources⟩
  rcases Program.compileCheckedAssemblyTargetBytecode?_eq_some hBytecode with
    ⟨hTarget, _hDecodeWindow, _hJumpdest⟩
  exact (Program.compileCheckedAssemblyTarget?_eq_some hTarget).1

theorem compileCheckedAssemblyTargetBytecodeResourcesSourceStatic?_assemblyCompile
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    (hCompileTarget :
      compileCheckedAssemblyTargetBytecodeResourcesSourceStatic? program =
        some (asm, target)) :
    Assembly.compile? asm = some target := by
  rcases
      compileCheckedAssemblyTargetBytecodeResourcesSourceStatic?_eq_some
        hCompileTarget with
    ⟨hResources, _hStatic⟩
  rcases Program.compileCheckedAssemblyTargetBytecodeResources?_eq_some
      hResources with
    ⟨hBytecode, _hResources⟩
  rcases Program.compileCheckedAssemblyTargetBytecode?_eq_some hBytecode with
    ⟨hTarget, _hDecodeWindow, _hJumpdest⟩
  exact (Program.compileCheckedAssemblyTarget?_eq_some hTarget).2

theorem sourceCompileAccepted_of_sourceAccepted_resources
    {program : Program}
    (hSource : Program.SourceAccepted program)
    (hResources : Program.RecursiveBridgeCompileResources program) :
    Program.SourceCompileAccepted program where
  source := hSource
  objects := by
    intro lowerObj hLower
    rcases hSource with
      ⟨_hWF, _hSupported, sourceObj, hSourceObj, hObjSourceAccepted⟩
    have hEq : sourceObj = lowerObj := by
      rw [hLower] at hSourceObj
      cases hSourceObj
      rfl
    cases hEq
    exact
      { source := hObjSourceAccepted
        functions :=
          { source := by
              simpa [Objects.Program.SourceAccepted,
                Functions.Inline.Program.SourceAccepted] using
                hObjSourceAccepted.2
            frameBound := hResources.functionFrameBound lowerObj hLower } }

/--
Concrete code-image relation for external worlds.

The relation is intentionally below the current feature-coverage checker: an
external account may contain CALL-family code while we are proving the
CALL-family bridge.  It still requires checked lowering, frame resources, and
source-static acceptedness/scoping facts for the emitted EVM code.
-/
noncomputable def CompiledCodeRel (contract : AstContract)
    (bytes : ByteArray) : Prop :=
  (∃ (program : Program) (asm : Assembly.Program)
      (target : Assembly.TargetProgram),
    program.contract = contract ∧
      compileCheckedAssemblyTargetBytecodeResourcesSourceStatic? program =
        some (asm, target) ∧
      bytes = Assembly.Bytecode.encodeTarget target) ∨
    (contract = default ∧ bytes = default)

theorem CompiledCodeRel.of_checked
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    (hCompile :
      compileCheckedAssemblyTargetBytecodeResourcesSourceStatic? program =
        some (asm, target)) :
    CompiledCodeRel program.contract
      (Assembly.Bytecode.encodeTarget target) := by
  exact Or.inl ⟨program, asm, target, rfl, hCompile, rfl⟩

theorem CompiledCodeRel.empty :
    CompiledCodeRel (default : AstContract) (default : ByteArray) := by
  exact Or.inr ⟨rfl, rfl⟩

theorem CompiledCodeRel.checked_or_empty
    {contract : AstContract} {bytes : ByteArray}
    (hCode : CompiledCodeRel contract bytes) :
      (∃ (program : Program) (asm : Assembly.Program)
        (target : Assembly.TargetProgram),
      program.contract = contract ∧
        compileCheckedAssemblyTargetBytecodeResourcesSourceStatic? program =
          some (asm, target) ∧
        bytes = Assembly.Bytecode.encodeTarget target) ∨
      (contract = default ∧ bytes = default) :=
  hCode

theorem CompiledCodeRel.checkedBytecodeResourcesSourceStatic_or_empty
    {contract : AstContract} {bytes : ByteArray}
    (hCode : CompiledCodeRel contract bytes) :
    (∃ (program : Program) (asm : Assembly.Program)
        (target : Assembly.TargetProgram),
      program.contract = contract ∧
        compileCheckedAssemblyTargetBytecodeResourcesSourceStatic? program =
          some (asm, target) ∧
        Program.RecursiveBridgeSourceStaticFacts program ∧
        Program.SourceAccepted program ∧
        Program.SourceCompileAccepted program ∧
        Program.compileChecked? program = some asm ∧
        Program.compileCheckedAssemblyTargetBytecode? program =
          some (asm, target) ∧
        _root_.EvmCompiler.Yul.Program.RecursiveBridgeCompileResources program ∧
        Assembly.Bytecode.TargetFitsDecodeWindow target ∧
        Assembly.Bytecode.JumpdestCorrect target ∧
        bytes = Assembly.Bytecode.encodeTarget target) ∨
      (contract = default ∧ bytes = default) := by
  rcases hCode with hChecked | hEmpty
  · rcases hChecked with
      ⟨program, asm, target, hContract, hCompile, hBytes⟩
    rcases
        compileCheckedAssemblyTargetBytecodeResourcesSourceStatic?_eq_some
          hCompile with
      ⟨hResourcesCompile, hStatic⟩
    rcases
        Program.compileCheckedAssemblyTargetBytecodeResources?_eq_some
          hResourcesCompile with
      ⟨hBytecode, hResources⟩
    rcases Program.compileCheckedAssemblyTargetBytecode?_eq_some
        hBytecode with
      ⟨_hTarget, hDecode, hJumpdest⟩
    have hSourceAccepted : Program.SourceAccepted program :=
      Program.sourceAccepted_of_sourceAcceptedCore_supported
        hStatic.sourceAcceptedCore hStatic.supported
    have hSourceCompileAccepted : Program.SourceCompileAccepted program :=
      sourceCompileAccepted_of_sourceAccepted_resources
        hSourceAccepted hResources
    have hCompileChecked : Program.compileChecked? program = some asm :=
      compileCheckedAssemblyTargetBytecodeResourcesSourceStatic?_compileChecked
        hCompile
    exact Or.inl
      ⟨program, asm, target, hContract, hCompile, hStatic,
        hSourceAccepted, hSourceCompileAccepted, hCompileChecked, hBytecode,
        hResources, hDecode, hJumpdest, hBytes⟩
  · exact Or.inr hEmpty

theorem CompiledCodeRel.checkedBytecodeResourcesSourceStatic_of_not_empty
    {contract : AstContract} {bytes : ByteArray}
    (hCode : CompiledCodeRel contract bytes)
    (hNotEmpty : ¬ (contract = default ∧ bytes = default)) :
    ∃ (program : Program) (asm : Assembly.Program)
        (target : Assembly.TargetProgram),
      program.contract = contract ∧
        compileCheckedAssemblyTargetBytecodeResourcesSourceStatic? program =
          some (asm, target) ∧
        Program.RecursiveBridgeSourceStaticFacts program ∧
        Program.SourceAccepted program ∧
        Program.SourceCompileAccepted program ∧
        Program.compileChecked? program = some asm ∧
        Program.compileCheckedAssemblyTargetBytecode? program =
          some (asm, target) ∧
        _root_.EvmCompiler.Yul.Program.RecursiveBridgeCompileResources program ∧
        Assembly.Bytecode.TargetFitsDecodeWindow target ∧
        Assembly.Bytecode.JumpdestCorrect target ∧
        bytes = Assembly.Bytecode.encodeTarget target := by
  rcases CompiledCodeRel.checkedBytecodeResourcesSourceStatic_or_empty
      hCode with hChecked | hEmpty
  · exact hChecked
  · exact False.elim (hNotEmpty hEmpty)

theorem installContract_ok_eq_self_of_code
    {program : Program} {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    (hCode : shared.executionEnv.code = program.contract) :
    Program.installContract program (.Ok shared store) = .Ok shared store := by
  cases shared with
  | mk state machine =>
      cases state with
      | mk accountMap sigma0 totalGasUsedInBlock transactionReceipts substate
          executionEnv blocks genesisBlockHeader createdAccounts =>
          cases executionEnv with
          | mk codeOwner sender source weiValue calldata code gasPrice header
              depth perm blobVersionedHashes codeBytes =>
              simp [Program.installContract] at hCode ⊢
              exact hCode.symm

theorem runResult_eq_callDispatcher_of_installed_contract
    {program : Program} {fuel : Nat}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    (hCode : shared.executionEnv.code = program.contract) :
    Reference.runResult fuel program (.Ok shared store) =
      match
        EvmYul.Yul.callDispatcher fuel (some program.contract)
          (.Ok shared store)
      with
      | .ok (state', _rets) => .ok (.regular state')
      | .error (.YulHalt state' value) => .ok (.yulHalt state' value)
      | .error (.Revert stateBeforeRevert) =>
          .ok (.revert stateBeforeRevert)
      | .error exception => .error exception := by
  rw [Reference.runResult, Program.run]
  rw [installContract_ok_eq_self_of_code hCode]
  rfl

theorem runResult_regular_of_installed_callDispatcher
    {program : Program} {fuel : Nat}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {state' : EvmYul.Yul.State} {rets : List EvmYul.UInt256}
    (hCode : shared.executionEnv.code = program.contract)
    (hCall :
      EvmYul.Yul.callDispatcher fuel (some program.contract)
          (.Ok shared store) =
        .ok (state', rets)) :
    Reference.runResult fuel program (.Ok shared store) =
      .ok (.regular state') := by
  rw [runResult_eq_callDispatcher_of_installed_contract hCode, hCall]

theorem installed_callDispatcher_regular_of_runResult
    {program : Program} {fuel : Nat}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {state' : EvmYul.Yul.State}
    (hCode : shared.executionEnv.code = program.contract)
    (hRun :
      Reference.runResult fuel program (.Ok shared store) =
        .ok (.regular state')) :
    ∃ rets : List EvmYul.UInt256,
      EvmYul.Yul.callDispatcher fuel (some program.contract)
          (.Ok shared store) =
        .ok (state', rets) := by
  rw [runResult_eq_callDispatcher_of_installed_contract hCode] at hRun
  cases hCall :
      EvmYul.Yul.callDispatcher fuel (some program.contract)
        (.Ok shared store) with
  | ok result =>
      rcases result with ⟨state, rets⟩
      simp [hCall] at hRun
      cases hRun
      exact ⟨rets, by simpa [hCall]⟩
  | error err =>
      cases err <;> simp [hCall] at hRun

theorem runResult_yulHalt_of_installed_callDispatcher
    {program : Program} {fuel : Nat}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {haltState : EvmYul.Yul.State} {value : EvmYul.UInt256}
    (hCode : shared.executionEnv.code = program.contract)
    (hCall :
      EvmYul.Yul.callDispatcher fuel (some program.contract)
          (.Ok shared store) =
        .error (.YulHalt haltState value)) :
    Reference.runResult fuel program (.Ok shared store) =
      .ok (.yulHalt haltState value) := by
  rw [runResult_eq_callDispatcher_of_installed_contract hCode, hCall]

theorem installed_callDispatcher_yulHalt_of_runResult
    {program : Program} {fuel : Nat}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {haltState : EvmYul.Yul.State} {value : EvmYul.UInt256}
    (hCode : shared.executionEnv.code = program.contract)
    (hRun :
      Reference.runResult fuel program (.Ok shared store) =
        .ok (.yulHalt haltState value)) :
    EvmYul.Yul.callDispatcher fuel (some program.contract)
        (.Ok shared store) =
      .error (.YulHalt haltState value) := by
  rw [runResult_eq_callDispatcher_of_installed_contract hCode] at hRun
  cases hCall :
      EvmYul.Yul.callDispatcher fuel (some program.contract)
        (.Ok shared store) with
  | ok result =>
      rcases result with ⟨state, rets⟩
      simp [hCall] at hRun
  | error err =>
      cases err <;> simp [hCall] at hRun ⊢
      case YulHalt haltState' value' =>
        exact hRun

theorem runResult_revert_of_installed_callDispatcher
    {program : Program} {fuel : Nat}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {revertState : EvmYul.Yul.State}
    (hCode : shared.executionEnv.code = program.contract)
    (hCall :
      EvmYul.Yul.callDispatcher fuel (some program.contract)
          (.Ok shared store) =
        .error (.Revert revertState)) :
    Reference.runResult fuel program (.Ok shared store) =
      .ok (.revert revertState) := by
  rw [runResult_eq_callDispatcher_of_installed_contract hCode, hCall]

theorem installed_callDispatcher_revert_of_runResult
    {program : Program} {fuel : Nat}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {revertState : EvmYul.Yul.State}
    (hCode : shared.executionEnv.code = program.contract)
    (hRun :
      Reference.runResult fuel program (.Ok shared store) =
        .ok (.revert revertState)) :
    EvmYul.Yul.callDispatcher fuel (some program.contract)
        (.Ok shared store) =
      .error (.Revert revertState) := by
  rw [runResult_eq_callDispatcher_of_installed_contract hCode] at hRun
  cases hCall :
      EvmYul.Yul.callDispatcher fuel (some program.contract)
        (.Ok shared store) with
  | ok result =>
      rcases result with ⟨state, rets⟩
      simp [hCall] at hRun
  | error err =>
      cases err <;> simp [hCall] at hRun ⊢
      case Revert revertState' =>
        exact hRun

theorem runResult_error_of_installed_callDispatcher
    {program : Program} {fuel : Nat}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {err : EvmYul.Yul.Exception}
    (hCode : shared.executionEnv.code = program.contract)
    (hCall :
      EvmYul.Yul.callDispatcher fuel (some program.contract)
          (.Ok shared store) =
        .error err)
    (hNotYulHalt : ∀ haltState value, err ≠ .YulHalt haltState value)
    (hNotRevert : ∀ revertState, err ≠ .Revert revertState) :
    Reference.runResult fuel program (.Ok shared store) = .error err := by
  rw [runResult_eq_callDispatcher_of_installed_contract hCode, hCall]
  cases err with
  | YulHalt haltState value =>
      exact (False.elim (hNotYulHalt haltState value rfl))
  | Revert revertState =>
      exact (False.elim (hNotRevert revertState rfl))
  | InvalidArguments => rfl
  | NotEncodableRLP => rfl
  | InvalidInstruction => rfl
  | OutOfFuel => rfl
  | StaticModeViolation => rfl
  | MissingContract msg => rfl
  | MissingContractFunction msg => rfl
  | InvalidExpression => rfl
  | UnknownIdentifier name => rfl
  | DuplicateDeclaration name => rfl
  | YulEXTCODESIZENotImplemented => rfl

theorem runResult_regular_ok_shape
    {program : Program} {fuel : Nat}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {state : EvmYul.Yul.State}
    (hRun :
      Reference.runResult fuel program (.Ok shared store) =
        .ok (.regular state))
    (hNotOutOfFuel : state ≠ .OutOfFuel) :
    ∃ finalShared finalStore,
      state = .Ok finalShared finalStore := by
  cases fuel with
  | zero =>
      simp [Reference.Imported.runResult_zero] at hRun
  | succ fuel =>
      rcases
          Reference.Imported.exists_exec_dispatcher_of_runResult_succ_ok
            fuel program (.Ok shared store) hRun with
        ⟨sourceResult, _hExec, hBody⟩
      cases sourceResult with
      | ok bodyState =>
          cases bodyState with
          | Ok finalShared _finalStore =>
              simp [Reference.Imported.dispatcherRunResultOfBody,
                Program.installContract, EvmYul.Yul.State.reviveJump,
                EvmYul.Yul.State.overwrite?, EvmYul.Yul.State.setStore]
                at hBody
              cases hBody
              exact ⟨finalShared, store, rfl⟩
          | OutOfFuel =>
              simp [Reference.Imported.dispatcherRunResultOfBody,
                Program.installContract, EvmYul.Yul.State.reviveJump,
                EvmYul.Yul.State.overwrite?, EvmYul.Yul.State.setStore]
                at hBody
              cases hBody
              exact False.elim (hNotOutOfFuel rfl)
          | Checkpoint jump =>
              cases jump <;>
                simp [Reference.Imported.dispatcherRunResultOfBody,
                  Program.installContract, EvmYul.Yul.State.reviveJump,
                  EvmYul.Yul.State.revive, EvmYul.Yul.State.overwrite?,
                  EvmYul.Yul.State.setStore] at hBody <;>
                cases hBody <;> exact ⟨_, store, rfl⟩
      | error err =>
          cases err <;>
            simp [Reference.Imported.dispatcherRunResultOfBody] at hBody

theorem compile_preserves_of_reference_source_runs_sourceStaticBoundary
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {outcomeRel : Reference.OutcomeRel}
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    {referenceFuel sourceFuel : Nat}
    {referenceInitial : Reference.State}
    {referenceResult : Reference.Result}
    {initial : EVMState}
    {sourceOutcome : Objects.Source.Outcome}
    (hReferenceRun :
      Reference.runResult referenceFuel program referenceInitial =
        .ok referenceResult)
    (hSourceRun :
      SourceLowered.run prim sourceFuel program initial =
        .ok sourceOutcome)
    (hOutcomeRel : outcomeRel referenceResult sourceOutcome)
    (hCompileBoundary :
      compileCheckedAssemblyTargetBytecodeResourcesSourceStatic? program =
        some (asm, target))
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = []) :
    ∃ targetFuel targetOutcome,
      Reference.runResult referenceFuel program referenceInitial =
        .ok referenceResult ∧
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      outcomeRel referenceResult sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Bytecode.TargetFitsDecodeWindow target ∧
      Assembly.Bytecode.JumpdestCorrect target := by
  rcases
      compileCheckedAssemblyTargetBytecodeResourcesSourceStatic?_eq_some
        hCompileBoundary with
    ⟨hResourcesCompile, hStatic⟩
  rcases Program.compileCheckedAssemblyTargetBytecodeResources?_eq_some
      hResourcesCompile with
    ⟨hBytecode, hResources⟩
  rcases Program.compileCheckedAssemblyTargetBytecode?_eq_some hBytecode with
    ⟨_hTarget, hDecode, hJumpdest⟩
  have hSourceAccepted : Program.SourceAccepted program :=
    Program.sourceAccepted_of_sourceAcceptedCore_supported
      hStatic.sourceAcceptedCore hStatic.supported
  have hSourceCompileAccepted : Program.SourceCompileAccepted program :=
    sourceCompileAccepted_of_sourceAccepted_resources
      hSourceAccepted hResources
  have hCompileChecked : Program.compileChecked? program = some asm :=
    compileCheckedAssemblyTargetBytecodeResourcesSourceStatic?_compileChecked
      hCompileBoundary
  rcases
      _root_.EvmCompiler.Yul.Program.compile_preserves_of_reference_source_runs_compileAccepted
        (prim := prim) hPrim (outcomeRel := outcomeRel)
        (program := program) (asm := asm)
        (referenceFuel := referenceFuel) (sourceFuel := sourceFuel)
        (referenceInitial := referenceInitial)
        (referenceResult := referenceResult) (initial := initial)
        (sourceOutcome := sourceOutcome)
        hReferenceRun hSourceRun hOutcomeRel hCompileChecked
        hSourceCompileAccepted hInitialPc hInitialStack with
    ⟨targetFuel, targetOutcome, hReferenceRun', hTargetRun, hOutcomeRel',
      hWholeRel⟩
  exact
    ⟨targetFuel, targetOutcome, hReferenceRun', hTargetRun, hOutcomeRel',
      hWholeRel, hDecode, hJumpdest⟩

theorem blockTraceResult_of_sourceStaticBoundary_runNResult
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    {targetFuel : Nat} {initial : EVMState}
    {targetOutcome : Assembly.StepResult}
    (hCompileBoundary :
      compileCheckedAssemblyTargetBytecodeResourcesSourceStatic? program =
        some (asm, target))
    (hTargetRun :
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome) :
    Assembly.Preservation.BlockTraceResult asm target targetFuel initial
      targetOutcome := by
  exact
    (Assembly.Preservation.compile_runN_result_block_trace_sound
      (hCompile :=
        compileCheckedAssemblyTargetBytecodeResourcesSourceStatic?_assemblyCompile
          hCompileBoundary)
      hTargetRun).2

theorem compile_preserves_of_reference_source_runs_sourceStaticBoundary_trace
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {outcomeRel : Reference.OutcomeRel}
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    {referenceFuel sourceFuel : Nat}
    {referenceInitial : Reference.State}
    {referenceResult : Reference.Result}
    {initial : EVMState}
    {sourceOutcome : Objects.Source.Outcome}
    (hReferenceRun :
      Reference.runResult referenceFuel program referenceInitial =
        .ok referenceResult)
    (hSourceRun :
      SourceLowered.run prim sourceFuel program initial =
        .ok sourceOutcome)
    (hOutcomeRel : outcomeRel referenceResult sourceOutcome)
    (hCompileBoundary :
      compileCheckedAssemblyTargetBytecodeResourcesSourceStatic? program =
        some (asm, target))
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = []) :
    ∃ targetFuel targetOutcome,
      Reference.runResult referenceFuel program referenceInitial =
        .ok referenceResult ∧
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      outcomeRel referenceResult sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Preservation.BlockTraceResult asm target targetFuel initial
        targetOutcome ∧
      Assembly.Bytecode.TargetFitsDecodeWindow target ∧
      Assembly.Bytecode.JumpdestCorrect target := by
  rcases
      compile_preserves_of_reference_source_runs_sourceStaticBoundary
        (prim := prim) hPrim (outcomeRel := outcomeRel)
        (program := program) (asm := asm) (target := target)
        (referenceFuel := referenceFuel) (sourceFuel := sourceFuel)
        (referenceInitial := referenceInitial)
        (referenceResult := referenceResult) (initial := initial)
        (sourceOutcome := sourceOutcome)
        hReferenceRun hSourceRun hOutcomeRel hCompileBoundary hInitialPc
        hInitialStack with
    ⟨targetFuel, targetOutcome, hReferenceRun', hTargetRun, hOutcomeRel',
      hWholeRel, hDecode, hJumpdest⟩
  exact
    ⟨targetFuel, targetOutcome, hReferenceRun', hTargetRun, hOutcomeRel',
      hWholeRel,
      blockTraceResult_of_sourceStaticBoundary_runNResult hCompileBoundary
        hTargetRun,
      hDecode, hJumpdest⟩

theorem compile_preserves_of_reference_source_runs_sourceStaticBoundary_XResult
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {outcomeRel : Reference.OutcomeRel}
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    {referenceFuel sourceFuel : Nat}
    {referenceInitial : Reference.State}
    {referenceResult : Reference.Result}
    {initial : EVMState}
    {sourceOutcome : Objects.Source.Outcome}
    (hReferenceRun :
      Reference.runResult referenceFuel program referenceInitial =
        .ok referenceResult)
    (hSourceRun :
      SourceLowered.run prim sourceFuel program initial =
        .ok sourceOutcome)
    (hOutcomeRel : outcomeRel referenceResult sourceOutcome)
    (hCompileBoundary :
      compileCheckedAssemblyTargetBytecodeResourcesSourceStatic? program =
        some (asm, target))
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = [])
    (hTargetGasForX :
      ∀ {targetFuel targetOutcome},
        Assembly.Preservation.BlockTraceResult asm target targetFuel initial
          targetOutcome →
        Assembly.GasAware.XResultPreconditionAssumptions target initial
          targetOutcome) :
    ∃ targetFuel targetOutcome evmFuel gasBound,
      Reference.runResult referenceFuel program referenceInitial =
        .ok referenceResult ∧
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      outcomeRel referenceResult sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Preservation.BlockTraceResult asm target targetFuel initial
        targetOutcome ∧
      (∀ gas,
        gasBound ≤ gas →
          gas < EvmYul.UInt256.size →
            ∃ result,
              EvmYul.EVM.X evmFuel (Assembly.GasAware.validJumps target)
                  (Assembly.GasAware.installCodeAndGas target gas initial) =
                .ok result ∧
              Assembly.GasAware.XResultAgrees targetOutcome result) ∧
      Assembly.Bytecode.TargetFitsDecodeWindow target ∧
      Assembly.Bytecode.JumpdestCorrect target := by
  rcases
      compile_preserves_of_reference_source_runs_sourceStaticBoundary_trace
        (prim := prim) hPrim (outcomeRel := outcomeRel)
        (program := program) (asm := asm) (target := target)
        (referenceFuel := referenceFuel) (sourceFuel := sourceFuel)
        (referenceInitial := referenceInitial)
        (referenceResult := referenceResult) (initial := initial)
        (sourceOutcome := sourceOutcome)
        hReferenceRun hSourceRun hOutcomeRel hCompileBoundary hInitialPc
        hInitialStack with
    ⟨targetFuel, targetOutcome, hReferenceRun', hTargetRun, hOutcomeRel',
      hWholeRel, hTrace, hDecode, hJumpdest⟩
  let hPreconditions := hTargetGasForX hTrace
  exact
    ⟨targetFuel, targetOutcome, hPreconditions.evmFuel,
      hPreconditions.gasBound, hReferenceRun', hTargetRun, hOutcomeRel',
      hWholeRel, hTrace, hPreconditions.runsAboveBound, hDecode, hJumpdest⟩

theorem compile_preserves_of_reference_source_runs_sourceStaticBoundary_installedGas_XResult
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {outcomeRel : Reference.OutcomeRel}
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    {referenceFuel sourceFuel gas : Nat}
    {referenceInitial : Reference.State}
    {referenceResult : Reference.Result}
    {rawInitial : EVMState}
    {sourceOutcome : Objects.Source.Outcome}
    (hReferenceRun :
      Reference.runResult referenceFuel program referenceInitial =
        .ok referenceResult)
    (hSourceRun :
      SourceLowered.run prim sourceFuel program
          (Assembly.GasAware.installCodeAndGas target gas rawInitial) =
        .ok sourceOutcome)
    (hOutcomeRel : outcomeRel referenceResult sourceOutcome)
    (hCompileBoundary :
      compileCheckedAssemblyTargetBytecodeResourcesSourceStatic? program =
        some (asm, target))
    (hInitialPc :
      (Assembly.GasAware.installCodeAndGas target gas rawInitial).pc =
        Assembly.Program.pcAfter [])
    (hInitialStack :
      (Assembly.GasAware.installCodeAndGas target gas rawInitial).stack = [])
    (hTargetGasForX :
      ∀ {targetFuel targetOutcome},
        Assembly.Preservation.BlockTraceResult asm target targetFuel
          (Assembly.GasAware.installCodeAndGas target gas rawInitial)
          targetOutcome →
        Assembly.GasAware.XResultPreconditionAssumptions target
          (Assembly.GasAware.installCodeAndGas target gas rawInitial)
          targetOutcome)
    (hGasBound :
      ∀ {targetFuel targetOutcome}
        (hTrace :
          Assembly.Preservation.BlockTraceResult asm target targetFuel
            (Assembly.GasAware.installCodeAndGas target gas rawInitial)
            targetOutcome),
        (hTargetGasForX hTrace).gasBound ≤ gas)
    (hUInt256 : gas < EvmYul.UInt256.size) :
    ∃ targetFuel targetOutcome evmFuel gasBound evmResult,
      Reference.runResult referenceFuel program referenceInitial =
        .ok referenceResult ∧
      Assembly.Source.runNResult asm targetFuel
          (Assembly.GasAware.installCodeAndGas target gas rawInitial) =
        .ok targetOutcome ∧
      outcomeRel referenceResult sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Preservation.BlockTraceResult asm target targetFuel
        (Assembly.GasAware.installCodeAndGas target gas rawInitial)
        targetOutcome ∧
      gasBound ≤ gas ∧
      EvmYul.EVM.X evmFuel (Assembly.GasAware.validJumps target)
          (Assembly.GasAware.installCodeAndGas target gas rawInitial) =
        .ok evmResult ∧
      Assembly.GasAware.XResultAgrees targetOutcome evmResult ∧
      Assembly.Bytecode.TargetFitsDecodeWindow target ∧
      Assembly.Bytecode.JumpdestCorrect target := by
  rcases
      compile_preserves_of_reference_source_runs_sourceStaticBoundary_trace
        (prim := prim) hPrim (outcomeRel := outcomeRel)
        (program := program) (asm := asm) (target := target)
        (referenceFuel := referenceFuel) (sourceFuel := sourceFuel)
        (referenceInitial := referenceInitial)
        (referenceResult := referenceResult)
        (initial := Assembly.GasAware.installCodeAndGas target gas rawInitial)
        (sourceOutcome := sourceOutcome)
        hReferenceRun hSourceRun hOutcomeRel hCompileBoundary hInitialPc
        hInitialStack with
    ⟨targetFuel, targetOutcome, hReferenceRun', hTargetRun, hOutcomeRel',
      hWholeRel, hTrace, hDecode, hJumpdest⟩
  let hPreconditions := hTargetGasForX hTrace
  have hGas : hPreconditions.gasBound ≤ gas :=
    hGasBound hTrace
  rcases hPreconditions.runsAtInstalledGas hGas hUInt256 with
    ⟨evmResult, hX, hAgree⟩
  exact
    ⟨targetFuel, targetOutcome, hPreconditions.evmFuel,
      hPreconditions.gasBound, evmResult, hReferenceRun', hTargetRun,
      hOutcomeRel', hWholeRel, hTrace, hGas, hX, hAgree, hDecode,
      hJumpdest⟩

theorem compile_preserves_of_installed_callDispatcher_regular_sourceStaticBoundary
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {outcomeRel : Reference.OutcomeRel}
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    {referenceFuel sourceFuel : Nat}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {state' : EvmYul.Yul.State} {rets : List EvmYul.UInt256}
    {initial : EVMState}
    {sourceOutcome : Objects.Source.Outcome}
    (hInstalled : shared.executionEnv.code = program.contract)
    (hCall :
      EvmYul.Yul.callDispatcher referenceFuel (some program.contract)
          (.Ok shared store) =
        .ok (state', rets))
    (hSourceRun :
      SourceLowered.run prim sourceFuel program initial =
        .ok sourceOutcome)
    (hOutcomeRel : outcomeRel (.regular state') sourceOutcome)
    (hCompileBoundary :
      compileCheckedAssemblyTargetBytecodeResourcesSourceStatic? program =
        some (asm, target))
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = []) :
    ∃ targetFuel targetOutcome,
      Reference.runResult referenceFuel program (.Ok shared store) =
        .ok (.regular state') ∧
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      outcomeRel (.regular state') sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Bytecode.TargetFitsDecodeWindow target ∧
      Assembly.Bytecode.JumpdestCorrect target := by
  exact
    compile_preserves_of_reference_source_runs_sourceStaticBoundary
      (prim := prim) hPrim (outcomeRel := outcomeRel)
      (program := program) (asm := asm) (target := target)
      (referenceFuel := referenceFuel) (sourceFuel := sourceFuel)
      (referenceInitial := .Ok shared store)
      (referenceResult := .regular state') (initial := initial)
      (sourceOutcome := sourceOutcome)
      (runResult_regular_of_installed_callDispatcher hInstalled hCall)
      hSourceRun hOutcomeRel hCompileBoundary hInitialPc hInitialStack

theorem compile_preserves_of_installed_callDispatcher_yulHalt_sourceStaticBoundary
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {outcomeRel : Reference.OutcomeRel}
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    {referenceFuel sourceFuel : Nat}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {haltState : EvmYul.Yul.State} {value : EvmYul.UInt256}
    {initial : EVMState}
    {sourceOutcome : Objects.Source.Outcome}
    (hInstalled : shared.executionEnv.code = program.contract)
    (hCall :
      EvmYul.Yul.callDispatcher referenceFuel (some program.contract)
          (.Ok shared store) =
        .error (.YulHalt haltState value))
    (hSourceRun :
      SourceLowered.run prim sourceFuel program initial =
        .ok sourceOutcome)
    (hOutcomeRel : outcomeRel (.yulHalt haltState value) sourceOutcome)
    (hCompileBoundary :
      compileCheckedAssemblyTargetBytecodeResourcesSourceStatic? program =
        some (asm, target))
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = []) :
    ∃ targetFuel targetOutcome,
      Reference.runResult referenceFuel program (.Ok shared store) =
        .ok (.yulHalt haltState value) ∧
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      outcomeRel (.yulHalt haltState value) sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Bytecode.TargetFitsDecodeWindow target ∧
      Assembly.Bytecode.JumpdestCorrect target := by
  exact
    compile_preserves_of_reference_source_runs_sourceStaticBoundary
      (prim := prim) hPrim (outcomeRel := outcomeRel)
      (program := program) (asm := asm) (target := target)
      (referenceFuel := referenceFuel) (sourceFuel := sourceFuel)
      (referenceInitial := .Ok shared store)
      (referenceResult := .yulHalt haltState value) (initial := initial)
      (sourceOutcome := sourceOutcome)
      (runResult_yulHalt_of_installed_callDispatcher hInstalled hCall)
      hSourceRun hOutcomeRel hCompileBoundary hInitialPc hInitialStack

theorem compile_preserves_of_installed_callDispatcher_revert_sourceStaticBoundary
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {outcomeRel : Reference.OutcomeRel}
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    {referenceFuel sourceFuel : Nat}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {revertState : EvmYul.Yul.State}
    {initial : EVMState}
    {sourceOutcome : Objects.Source.Outcome}
    (hInstalled : shared.executionEnv.code = program.contract)
    (hCall :
      EvmYul.Yul.callDispatcher referenceFuel (some program.contract)
          (.Ok shared store) =
        .error (.Revert revertState))
    (hSourceRun :
      SourceLowered.run prim sourceFuel program initial =
        .ok sourceOutcome)
    (hOutcomeRel : outcomeRel (.revert revertState) sourceOutcome)
    (hCompileBoundary :
      compileCheckedAssemblyTargetBytecodeResourcesSourceStatic? program =
        some (asm, target))
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = []) :
    ∃ targetFuel targetOutcome,
      Reference.runResult referenceFuel program (.Ok shared store) =
        .ok (.revert revertState) ∧
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      outcomeRel (.revert revertState) sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Bytecode.TargetFitsDecodeWindow target ∧
      Assembly.Bytecode.JumpdestCorrect target := by
  exact
    compile_preserves_of_reference_source_runs_sourceStaticBoundary
      (prim := prim) hPrim (outcomeRel := outcomeRel)
      (program := program) (asm := asm) (target := target)
      (referenceFuel := referenceFuel) (sourceFuel := sourceFuel)
      (referenceInitial := .Ok shared store)
      (referenceResult := .revert revertState) (initial := initial)
      (sourceOutcome := sourceOutcome)
      (runResult_revert_of_installed_callDispatcher hInstalled hCall)
      hSourceRun hOutcomeRel hCompileBoundary hInitialPc hInitialStack

theorem compile_preserves_of_installed_callDispatcher_regular_sourceStaticBoundary_XResult
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {outcomeRel : Reference.OutcomeRel}
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    {referenceFuel sourceFuel : Nat}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {state' : EvmYul.Yul.State} {rets : List EvmYul.UInt256}
    {initial : EVMState}
    {sourceOutcome : Objects.Source.Outcome}
    (hInstalled : shared.executionEnv.code = program.contract)
    (hCall :
      EvmYul.Yul.callDispatcher referenceFuel (some program.contract)
          (.Ok shared store) =
        .ok (state', rets))
    (hSourceRun :
      SourceLowered.run prim sourceFuel program initial =
        .ok sourceOutcome)
    (hOutcomeRel : outcomeRel (.regular state') sourceOutcome)
    (hCompileBoundary :
      compileCheckedAssemblyTargetBytecodeResourcesSourceStatic? program =
        some (asm, target))
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = [])
    (hTargetGasForX :
      ∀ {targetFuel targetOutcome},
        Assembly.Preservation.BlockTraceResult asm target targetFuel initial
          targetOutcome →
        Assembly.GasAware.XResultPreconditionAssumptions target initial
          targetOutcome) :
    ∃ targetFuel targetOutcome evmFuel gasBound,
      Reference.runResult referenceFuel program (.Ok shared store) =
        .ok (.regular state') ∧
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      outcomeRel (.regular state') sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Preservation.BlockTraceResult asm target targetFuel initial
        targetOutcome ∧
      (∀ gas,
        gasBound ≤ gas →
          gas < EvmYul.UInt256.size →
            ∃ result,
              EvmYul.EVM.X evmFuel (Assembly.GasAware.validJumps target)
                  (Assembly.GasAware.installCodeAndGas target gas initial) =
                .ok result ∧
              Assembly.GasAware.XResultAgrees targetOutcome result) ∧
      Assembly.Bytecode.TargetFitsDecodeWindow target ∧
      Assembly.Bytecode.JumpdestCorrect target := by
  exact
    compile_preserves_of_reference_source_runs_sourceStaticBoundary_XResult
      (prim := prim) hPrim (outcomeRel := outcomeRel)
      (program := program) (asm := asm) (target := target)
      (referenceFuel := referenceFuel) (sourceFuel := sourceFuel)
      (referenceInitial := .Ok shared store)
      (referenceResult := .regular state') (initial := initial)
      (sourceOutcome := sourceOutcome)
      (runResult_regular_of_installed_callDispatcher hInstalled hCall)
      hSourceRun hOutcomeRel hCompileBoundary hInitialPc hInitialStack
      hTargetGasForX

theorem compile_preserves_of_installed_callDispatcher_yulHalt_sourceStaticBoundary_XResult
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {outcomeRel : Reference.OutcomeRel}
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    {referenceFuel sourceFuel : Nat}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {haltState : EvmYul.Yul.State} {value : EvmYul.UInt256}
    {initial : EVMState}
    {sourceOutcome : Objects.Source.Outcome}
    (hInstalled : shared.executionEnv.code = program.contract)
    (hCall :
      EvmYul.Yul.callDispatcher referenceFuel (some program.contract)
          (.Ok shared store) =
        .error (.YulHalt haltState value))
    (hSourceRun :
      SourceLowered.run prim sourceFuel program initial =
        .ok sourceOutcome)
    (hOutcomeRel : outcomeRel (.yulHalt haltState value) sourceOutcome)
    (hCompileBoundary :
      compileCheckedAssemblyTargetBytecodeResourcesSourceStatic? program =
        some (asm, target))
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = [])
    (hTargetGasForX :
      ∀ {targetFuel targetOutcome},
        Assembly.Preservation.BlockTraceResult asm target targetFuel initial
          targetOutcome →
        Assembly.GasAware.XResultPreconditionAssumptions target initial
          targetOutcome) :
    ∃ targetFuel targetOutcome evmFuel gasBound,
      Reference.runResult referenceFuel program (.Ok shared store) =
        .ok (.yulHalt haltState value) ∧
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      outcomeRel (.yulHalt haltState value) sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Preservation.BlockTraceResult asm target targetFuel initial
        targetOutcome ∧
      (∀ gas,
        gasBound ≤ gas →
          gas < EvmYul.UInt256.size →
            ∃ result,
              EvmYul.EVM.X evmFuel (Assembly.GasAware.validJumps target)
                  (Assembly.GasAware.installCodeAndGas target gas initial) =
                .ok result ∧
              Assembly.GasAware.XResultAgrees targetOutcome result) ∧
      Assembly.Bytecode.TargetFitsDecodeWindow target ∧
      Assembly.Bytecode.JumpdestCorrect target := by
  exact
    compile_preserves_of_reference_source_runs_sourceStaticBoundary_XResult
      (prim := prim) hPrim (outcomeRel := outcomeRel)
      (program := program) (asm := asm) (target := target)
      (referenceFuel := referenceFuel) (sourceFuel := sourceFuel)
      (referenceInitial := .Ok shared store)
      (referenceResult := .yulHalt haltState value) (initial := initial)
      (sourceOutcome := sourceOutcome)
      (runResult_yulHalt_of_installed_callDispatcher hInstalled hCall)
      hSourceRun hOutcomeRel hCompileBoundary hInitialPc hInitialStack
      hTargetGasForX

theorem compile_preserves_of_installed_callDispatcher_revert_sourceStaticBoundary_XResult
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {outcomeRel : Reference.OutcomeRel}
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    {referenceFuel sourceFuel : Nat}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {revertState : EvmYul.Yul.State}
    {initial : EVMState}
    {sourceOutcome : Objects.Source.Outcome}
    (hInstalled : shared.executionEnv.code = program.contract)
    (hCall :
      EvmYul.Yul.callDispatcher referenceFuel (some program.contract)
          (.Ok shared store) =
        .error (.Revert revertState))
    (hSourceRun :
      SourceLowered.run prim sourceFuel program initial =
        .ok sourceOutcome)
    (hOutcomeRel : outcomeRel (.revert revertState) sourceOutcome)
    (hCompileBoundary :
      compileCheckedAssemblyTargetBytecodeResourcesSourceStatic? program =
        some (asm, target))
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = [])
    (hTargetGasForX :
      ∀ {targetFuel targetOutcome},
        Assembly.Preservation.BlockTraceResult asm target targetFuel initial
          targetOutcome →
        Assembly.GasAware.XResultPreconditionAssumptions target initial
          targetOutcome) :
    ∃ targetFuel targetOutcome evmFuel gasBound,
      Reference.runResult referenceFuel program (.Ok shared store) =
        .ok (.revert revertState) ∧
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      outcomeRel (.revert revertState) sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Preservation.BlockTraceResult asm target targetFuel initial
        targetOutcome ∧
      (∀ gas,
        gasBound ≤ gas →
          gas < EvmYul.UInt256.size →
            ∃ result,
              EvmYul.EVM.X evmFuel (Assembly.GasAware.validJumps target)
                  (Assembly.GasAware.installCodeAndGas target gas initial) =
                .ok result ∧
              Assembly.GasAware.XResultAgrees targetOutcome result) ∧
      Assembly.Bytecode.TargetFitsDecodeWindow target ∧
      Assembly.Bytecode.JumpdestCorrect target := by
  exact
    compile_preserves_of_reference_source_runs_sourceStaticBoundary_XResult
      (prim := prim) hPrim (outcomeRel := outcomeRel)
      (program := program) (asm := asm) (target := target)
      (referenceFuel := referenceFuel) (sourceFuel := sourceFuel)
      (referenceInitial := .Ok shared store)
      (referenceResult := .revert revertState) (initial := initial)
      (sourceOutcome := sourceOutcome)
      (runResult_revert_of_installed_callDispatcher hInstalled hCall)
      hSourceRun hOutcomeRel hCompileBoundary hInitialPc hInitialStack
      hTargetGasForX

theorem compile_preserves_of_installed_callDispatcher_regular_sourceStaticBoundary_installedGas_XResult
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {outcomeRel : Reference.OutcomeRel}
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    {referenceFuel sourceFuel gas : Nat}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {state' : EvmYul.Yul.State} {rets : List EvmYul.UInt256}
    {rawInitial : EVMState}
    {sourceOutcome : Objects.Source.Outcome}
    (hInstalled : shared.executionEnv.code = program.contract)
    (hCall :
      EvmYul.Yul.callDispatcher referenceFuel (some program.contract)
          (.Ok shared store) =
        .ok (state', rets))
    (hSourceRun :
      SourceLowered.run prim sourceFuel program
          (Assembly.GasAware.installCodeAndGas target gas rawInitial) =
        .ok sourceOutcome)
    (hOutcomeRel : outcomeRel (.regular state') sourceOutcome)
    (hCompileBoundary :
      compileCheckedAssemblyTargetBytecodeResourcesSourceStatic? program =
        some (asm, target))
    (hInitialPc :
      (Assembly.GasAware.installCodeAndGas target gas rawInitial).pc =
        Assembly.Program.pcAfter [])
    (hInitialStack :
      (Assembly.GasAware.installCodeAndGas target gas rawInitial).stack = [])
    (hTargetGasForX :
      ∀ {targetFuel targetOutcome},
        Assembly.Preservation.BlockTraceResult asm target targetFuel
          (Assembly.GasAware.installCodeAndGas target gas rawInitial)
          targetOutcome →
        Assembly.GasAware.XResultPreconditionAssumptions target
          (Assembly.GasAware.installCodeAndGas target gas rawInitial)
          targetOutcome)
    (hGasBound :
      ∀ {targetFuel targetOutcome}
        (hTrace :
          Assembly.Preservation.BlockTraceResult asm target targetFuel
            (Assembly.GasAware.installCodeAndGas target gas rawInitial)
            targetOutcome),
        (hTargetGasForX hTrace).gasBound ≤ gas)
    (hUInt256 : gas < EvmYul.UInt256.size) :
    ∃ targetFuel targetOutcome evmFuel gasBound evmResult,
      Reference.runResult referenceFuel program (.Ok shared store) =
        .ok (.regular state') ∧
      Assembly.Source.runNResult asm targetFuel
          (Assembly.GasAware.installCodeAndGas target gas rawInitial) =
        .ok targetOutcome ∧
      outcomeRel (.regular state') sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Preservation.BlockTraceResult asm target targetFuel
        (Assembly.GasAware.installCodeAndGas target gas rawInitial)
        targetOutcome ∧
      gasBound ≤ gas ∧
      EvmYul.EVM.X evmFuel (Assembly.GasAware.validJumps target)
          (Assembly.GasAware.installCodeAndGas target gas rawInitial) =
        .ok evmResult ∧
      Assembly.GasAware.XResultAgrees targetOutcome evmResult ∧
      Assembly.Bytecode.TargetFitsDecodeWindow target ∧
      Assembly.Bytecode.JumpdestCorrect target := by
  exact
    compile_preserves_of_reference_source_runs_sourceStaticBoundary_installedGas_XResult
      (prim := prim) hPrim (outcomeRel := outcomeRel)
      (program := program) (asm := asm) (target := target)
      (referenceFuel := referenceFuel) (sourceFuel := sourceFuel)
      (gas := gas) (referenceInitial := .Ok shared store)
      (referenceResult := .regular state') (rawInitial := rawInitial)
      (sourceOutcome := sourceOutcome)
      (runResult_regular_of_installed_callDispatcher hInstalled hCall)
      hSourceRun hOutcomeRel hCompileBoundary hInitialPc hInitialStack
      hTargetGasForX hGasBound hUInt256

theorem compile_preserves_of_installed_callDispatcher_yulHalt_sourceStaticBoundary_installedGas_XResult
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {outcomeRel : Reference.OutcomeRel}
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    {referenceFuel sourceFuel gas : Nat}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {haltState : EvmYul.Yul.State} {value : EvmYul.UInt256}
    {rawInitial : EVMState}
    {sourceOutcome : Objects.Source.Outcome}
    (hInstalled : shared.executionEnv.code = program.contract)
    (hCall :
      EvmYul.Yul.callDispatcher referenceFuel (some program.contract)
          (.Ok shared store) =
        .error (.YulHalt haltState value))
    (hSourceRun :
      SourceLowered.run prim sourceFuel program
          (Assembly.GasAware.installCodeAndGas target gas rawInitial) =
        .ok sourceOutcome)
    (hOutcomeRel : outcomeRel (.yulHalt haltState value) sourceOutcome)
    (hCompileBoundary :
      compileCheckedAssemblyTargetBytecodeResourcesSourceStatic? program =
        some (asm, target))
    (hInitialPc :
      (Assembly.GasAware.installCodeAndGas target gas rawInitial).pc =
        Assembly.Program.pcAfter [])
    (hInitialStack :
      (Assembly.GasAware.installCodeAndGas target gas rawInitial).stack = [])
    (hTargetGasForX :
      ∀ {targetFuel targetOutcome},
        Assembly.Preservation.BlockTraceResult asm target targetFuel
          (Assembly.GasAware.installCodeAndGas target gas rawInitial)
          targetOutcome →
        Assembly.GasAware.XResultPreconditionAssumptions target
          (Assembly.GasAware.installCodeAndGas target gas rawInitial)
          targetOutcome)
    (hGasBound :
      ∀ {targetFuel targetOutcome}
        (hTrace :
          Assembly.Preservation.BlockTraceResult asm target targetFuel
            (Assembly.GasAware.installCodeAndGas target gas rawInitial)
            targetOutcome),
        (hTargetGasForX hTrace).gasBound ≤ gas)
    (hUInt256 : gas < EvmYul.UInt256.size) :
    ∃ targetFuel targetOutcome evmFuel gasBound evmResult,
      Reference.runResult referenceFuel program (.Ok shared store) =
        .ok (.yulHalt haltState value) ∧
      Assembly.Source.runNResult asm targetFuel
          (Assembly.GasAware.installCodeAndGas target gas rawInitial) =
        .ok targetOutcome ∧
      outcomeRel (.yulHalt haltState value) sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Preservation.BlockTraceResult asm target targetFuel
        (Assembly.GasAware.installCodeAndGas target gas rawInitial)
        targetOutcome ∧
      gasBound ≤ gas ∧
      EvmYul.EVM.X evmFuel (Assembly.GasAware.validJumps target)
          (Assembly.GasAware.installCodeAndGas target gas rawInitial) =
        .ok evmResult ∧
      Assembly.GasAware.XResultAgrees targetOutcome evmResult ∧
      Assembly.Bytecode.TargetFitsDecodeWindow target ∧
      Assembly.Bytecode.JumpdestCorrect target := by
  exact
    compile_preserves_of_reference_source_runs_sourceStaticBoundary_installedGas_XResult
      (prim := prim) hPrim (outcomeRel := outcomeRel)
      (program := program) (asm := asm) (target := target)
      (referenceFuel := referenceFuel) (sourceFuel := sourceFuel)
      (gas := gas) (referenceInitial := .Ok shared store)
      (referenceResult := .yulHalt haltState value)
      (rawInitial := rawInitial)
      (sourceOutcome := sourceOutcome)
      (runResult_yulHalt_of_installed_callDispatcher hInstalled hCall)
      hSourceRun hOutcomeRel hCompileBoundary hInitialPc hInitialStack
      hTargetGasForX hGasBound hUInt256

theorem compile_preserves_of_installed_callDispatcher_revert_sourceStaticBoundary_installedGas_XResult
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {outcomeRel : Reference.OutcomeRel}
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    {referenceFuel sourceFuel gas : Nat}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {revertState : EvmYul.Yul.State}
    {rawInitial : EVMState}
    {sourceOutcome : Objects.Source.Outcome}
    (hInstalled : shared.executionEnv.code = program.contract)
    (hCall :
      EvmYul.Yul.callDispatcher referenceFuel (some program.contract)
          (.Ok shared store) =
        .error (.Revert revertState))
    (hSourceRun :
      SourceLowered.run prim sourceFuel program
          (Assembly.GasAware.installCodeAndGas target gas rawInitial) =
        .ok sourceOutcome)
    (hOutcomeRel : outcomeRel (.revert revertState) sourceOutcome)
    (hCompileBoundary :
      compileCheckedAssemblyTargetBytecodeResourcesSourceStatic? program =
        some (asm, target))
    (hInitialPc :
      (Assembly.GasAware.installCodeAndGas target gas rawInitial).pc =
        Assembly.Program.pcAfter [])
    (hInitialStack :
      (Assembly.GasAware.installCodeAndGas target gas rawInitial).stack = [])
    (hTargetGasForX :
      ∀ {targetFuel targetOutcome},
        Assembly.Preservation.BlockTraceResult asm target targetFuel
          (Assembly.GasAware.installCodeAndGas target gas rawInitial)
          targetOutcome →
        Assembly.GasAware.XResultPreconditionAssumptions target
          (Assembly.GasAware.installCodeAndGas target gas rawInitial)
          targetOutcome)
    (hGasBound :
      ∀ {targetFuel targetOutcome}
        (hTrace :
          Assembly.Preservation.BlockTraceResult asm target targetFuel
            (Assembly.GasAware.installCodeAndGas target gas rawInitial)
            targetOutcome),
        (hTargetGasForX hTrace).gasBound ≤ gas)
    (hUInt256 : gas < EvmYul.UInt256.size) :
    ∃ targetFuel targetOutcome evmFuel gasBound evmResult,
      Reference.runResult referenceFuel program (.Ok shared store) =
        .ok (.revert revertState) ∧
      Assembly.Source.runNResult asm targetFuel
          (Assembly.GasAware.installCodeAndGas target gas rawInitial) =
        .ok targetOutcome ∧
      outcomeRel (.revert revertState) sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Preservation.BlockTraceResult asm target targetFuel
        (Assembly.GasAware.installCodeAndGas target gas rawInitial)
        targetOutcome ∧
      gasBound ≤ gas ∧
      EvmYul.EVM.X evmFuel (Assembly.GasAware.validJumps target)
          (Assembly.GasAware.installCodeAndGas target gas rawInitial) =
        .ok evmResult ∧
      Assembly.GasAware.XResultAgrees targetOutcome evmResult ∧
      Assembly.Bytecode.TargetFitsDecodeWindow target ∧
      Assembly.Bytecode.JumpdestCorrect target := by
  exact
    compile_preserves_of_reference_source_runs_sourceStaticBoundary_installedGas_XResult
      (prim := prim) hPrim (outcomeRel := outcomeRel)
      (program := program) (asm := asm) (target := target)
      (referenceFuel := referenceFuel) (sourceFuel := sourceFuel)
      (gas := gas) (referenceInitial := .Ok shared store)
      (referenceResult := .revert revertState)
      (rawInitial := rawInitial)
      (sourceOutcome := sourceOutcome)
      (runResult_revert_of_installed_callDispatcher hInstalled hCall)
      hSourceRun hOutcomeRel hCompileBoundary hInitialPc hInitialStack
      hTargetGasForX hGasBound hUInt256

theorem wholeProgramOutcomeRel_regular_running
    {source : Objects.Source.State} {targetOutcome : Assembly.StepResult}
    (hRel :
      SourceLowered.WholeProgramOutcomeRel
        (Functions.Source.Outcome.regular source) targetOutcome) :
    ∃ target, targetOutcome = .running target := by
  rcases hRel with ⟨direct, hBlock, hStructured⟩
  cases direct with
  | mk directState directMode =>
      cases targetOutcome with
      | running target => exact ⟨target, rfl⟩
      | halted halt =>
          cases directMode <;>
            simp [Functions.SourceDirect.BlockScopedOutcomeRel,
              Functions.SourceDirect.StmtOutcomeRel,
              Structured.Preservation.WholeProgramOutcomeRel,
              Functions.Source.Outcome.regular,
              Locals.Source.Outcome.regular] at hBlock hStructured

theorem wholeProgramOutcomeRel_halt_halted
    {kind : Assembly.HaltKind} {source : Objects.Source.State}
    {targetOutcome : Assembly.StepResult}
    (hRel :
      SourceLowered.WholeProgramOutcomeRel
        (Functions.Source.Outcome.halt kind source) targetOutcome) :
    ∃ halt, targetOutcome = .halted halt ∧ halt.kind = kind := by
  rcases hRel with ⟨direct, hBlock, hStructured⟩
  cases direct with
  | mk directState directMode =>
      cases targetOutcome with
      | running target =>
          cases directMode <;>
            simp [Functions.SourceDirect.BlockScopedOutcomeRel,
              Functions.SourceDirect.StmtOutcomeRel,
              Structured.Preservation.WholeProgramOutcomeRel,
              Functions.Source.Outcome.halt,
              Locals.Source.Outcome.halt] at hBlock hStructured
      | halted halt =>
          cases directMode <;>
            simp [Functions.SourceDirect.BlockScopedOutcomeRel,
              Functions.SourceDirect.StmtOutcomeRel,
              Structured.Preservation.WholeProgramOutcomeRel,
              Functions.Source.Outcome.halt,
              Locals.Source.Outcome.halt] at hBlock hStructured
          · rename_i directKind
            rcases hStructured with ⟨hKind, _hState⟩
            exact ⟨halt, rfl, by simpa [hBlock] using hKind.symm⟩

theorem wholeProgramOutcomeRel_brk_false
    {source : Objects.Source.State} {targetOutcome : Assembly.StepResult}
    (hRel :
      SourceLowered.WholeProgramOutcomeRel
        (Functions.Source.Outcome.brk source) targetOutcome) :
    False := by
  rcases hRel with ⟨direct, hBlock, hStructured⟩
  cases direct with
  | mk directState directMode =>
      cases targetOutcome <;> cases directMode <;>
        simp [Functions.SourceDirect.BlockScopedOutcomeRel,
          Functions.SourceDirect.StmtOutcomeRel,
          Structured.Preservation.WholeProgramOutcomeRel,
          Functions.Source.Outcome.brk,
          Locals.Source.Outcome.brk] at hBlock hStructured

theorem wholeProgramOutcomeRel_cont_false
    {source : Objects.Source.State} {targetOutcome : Assembly.StepResult}
    (hRel :
      SourceLowered.WholeProgramOutcomeRel
        (Functions.Source.Outcome.cont source) targetOutcome) :
    False := by
  rcases hRel with ⟨direct, hBlock, hStructured⟩
  cases direct with
  | mk directState directMode =>
      cases targetOutcome <;> cases directMode <;>
        simp [Functions.SourceDirect.BlockScopedOutcomeRel,
          Functions.SourceDirect.StmtOutcomeRel,
          Structured.Preservation.WholeProgramOutcomeRel,
          Functions.Source.Outcome.cont,
          Locals.Source.Outcome.cont] at hBlock hStructured

theorem wholeProgramOutcomeRel_leave_false
    {source : Objects.Source.State} {targetOutcome : Assembly.StepResult}
    (hRel :
      SourceLowered.WholeProgramOutcomeRel
        (Functions.Source.Outcome.leave source) targetOutcome) :
    False := by
  rcases hRel with ⟨direct, hBlock, hStructured⟩
  cases direct with
  | mk directState directMode =>
      cases targetOutcome <;> cases directMode <;>
        simp [Functions.SourceDirect.BlockScopedOutcomeRel,
          Functions.SourceDirect.StmtOutcomeRel,
          Structured.Preservation.WholeProgramOutcomeRel,
          Functions.Source.Outcome.leave,
          Locals.Source.Outcome.leave] at hBlock hStructured

theorem dispatcherOutcomeRel_regular_whole_running
    {cfg : Reference.StateRelConfig}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {program : Program} {referenceInitial final : Reference.State}
    {sourceOutcome : Objects.Source.Outcome}
    {targetOutcome : Assembly.StepResult}
    (hOutcomeRel :
      Program.RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg
        terminalRel revertRel program referenceInitial (.regular final)
        sourceOutcome)
    (hWhole :
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome) :
    ∃ bodyState target,
      final =
        EvmYul.Yul.State.setStore
          (EvmYul.Yul.State.overwrite?
            (EvmYul.Yul.State.reviveJump bodyState)
            (Program.installContract program referenceInitial))
          (Program.installContract program referenceInitial) ∧
      Reference.SourceBridgeFacts.SourceOkOutcomeRel cfg [] bodyState
        sourceOutcome ∧
      targetOutcome = .running target := by
  rcases hOutcomeRel with ⟨bodyState, hFinal, hSourceRel⟩
  cases hSourceRel with
  | regular hRel =>
      rcases wholeProgramOutcomeRel_regular_running hWhole with
        ⟨target, hTarget⟩
      exact
        ⟨bodyState, target, hFinal,
          Reference.SourceBridgeFacts.SourceOkOutcomeRel.regular hRel,
          hTarget⟩
  | brk hRel =>
      exact False.elim (wholeProgramOutcomeRel_brk_false hWhole)
  | cont hRel =>
      exact False.elim (wholeProgramOutcomeRel_cont_false hWhole)
  | leave hRel =>
      exact False.elim (wholeProgramOutcomeRel_leave_false hWhole)

theorem dispatcherOutcomeRel_yulHalt_whole_halted
    {cfg : Reference.StateRelConfig}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {program : Program} {referenceInitial haltState : Reference.State}
    {value : Word} {sourceOutcome : Objects.Source.Outcome}
    {targetOutcome : Assembly.StepResult}
    (hOutcomeRel :
      Program.RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg
        terminalRel revertRel program referenceInitial (.yulHalt haltState value)
        sourceOutcome)
    (hWhole :
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome) :
    ∃ kind compiler halt,
      terminalRel kind value haltState compiler ∧
      sourceOutcome = Functions.Source.Outcome.halt kind compiler ∧
      targetOutcome = .halted halt ∧
      halt.kind = kind := by
  rcases hOutcomeRel with ⟨kind, compiler, hTerminal, rfl⟩
  rcases wholeProgramOutcomeRel_halt_halted hWhole with
    ⟨halt, hTarget, hKind⟩
  exact ⟨kind, compiler, halt, hTerminal, rfl, hTarget, hKind⟩

theorem dispatcherOutcomeRel_revert_whole_halted
    {cfg : Reference.StateRelConfig}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {program : Program} {referenceInitial revertState : Reference.State}
    {sourceOutcome : Objects.Source.Outcome}
    {targetOutcome : Assembly.StepResult}
    (hOutcomeRel :
      Program.RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg
        terminalRel revertRel program referenceInitial (.revert revertState)
        sourceOutcome)
    (hWhole :
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome) :
    ∃ compiler halt,
      revertRel revertState compiler ∧
      sourceOutcome = Functions.Source.Outcome.halt .revert compiler ∧
      targetOutcome = .halted halt ∧
      halt.kind = .revert := by
  rcases hOutcomeRel with ⟨compiler, hRevert, rfl⟩
  rcases wholeProgramOutcomeRel_halt_halted hWhole with
    ⟨halt, hTarget, hKind⟩
  exact ⟨compiler, halt, hRevert, rfl, hTarget, hKind⟩

noncomputable def codeImageRel : Reference.CodeImageRel :=
  CompiledCodeRel

structure CompiledAccountRel (yul : EvmYul.Account .Yul)
    (evm : EvmYul.Account .EVM) : Prop where
  nonce : yul.nonce = evm.nonce
  balance : yul.balance = evm.balance
  storage : yul.storage = evm.storage
  tstorage : yul.tstorage = evm.tstorage
  codeEmpty : (yul.code == default) = evm.code.isEmpty
  codeBytes : yul.codeBytes = evm.code
  code : CompiledCodeRel yul.code evm.code

theorem CompiledAccountRel.codeRel
    {yul : EvmYul.Account .Yul} {evm : EvmYul.Account .EVM}
    (hAccount : CompiledAccountRel yul evm) :
    codeImageRel yul.code evm.code :=
  hAccount.code

theorem CompiledAccountRel.emptyAccount
    {yul : EvmYul.Account .Yul} {evm : EvmYul.Account .EVM}
    (hAccount : CompiledAccountRel yul evm) :
    EvmYul.Account.emptyAccount yul =
      EvmYul.Account.emptyAccount evm := by
  simp [EvmYul.Account.emptyAccount, hAccount.nonce, hAccount.balance,
    hAccount.codeEmpty]

theorem CompiledAccountRel.with_balance
    {yul : EvmYul.Account .Yul} {evm : EvmYul.Account .EVM}
    (hAccount : CompiledAccountRel yul evm)
    (balance : EvmYul.UInt256) :
    CompiledAccountRel
      { yul with balance := balance }
      { evm with balance := balance } := by
  exact
    { nonce := hAccount.nonce
      balance := rfl
      storage := hAccount.storage
      tstorage := hAccount.tstorage
      codeEmpty := hAccount.codeEmpty
      codeBytes := hAccount.codeBytes
      code := hAccount.code }

theorem CompiledAccountRel.update_storage
    {yul : EvmYul.Account .Yul} {evm : EvmYul.Account .EVM}
    (hAccount : CompiledAccountRel yul evm)
    (slot value : EvmYul.UInt256) :
    CompiledAccountRel
      (EvmYul.Account.updateStorage yul slot value)
      (EvmYul.Account.updateStorage evm slot value) := by
  unfold EvmYul.Account.updateStorage
  by_cases hZero : (value == default) = true
  · simp [hZero]
    exact
      { nonce := hAccount.nonce
        balance := hAccount.balance
        storage := by simp [hAccount.storage]
        tstorage := hAccount.tstorage
        codeEmpty := hAccount.codeEmpty
        codeBytes := hAccount.codeBytes
        code := hAccount.code }
  · simp [hZero]
    exact
      { nonce := hAccount.nonce
        balance := hAccount.balance
        storage := by simp [hAccount.storage]
        tstorage := hAccount.tstorage
        codeEmpty := hAccount.codeEmpty
        codeBytes := hAccount.codeBytes
        code := hAccount.code }

theorem CompiledAccountRel.update_transientStorage
    {yul : EvmYul.Account .Yul} {evm : EvmYul.Account .EVM}
    (hAccount : CompiledAccountRel yul evm)
    (slot value : EvmYul.UInt256) :
    CompiledAccountRel
      (EvmYul.Account.updateTransientStorage yul slot value)
      (EvmYul.Account.updateTransientStorage evm slot value) := by
  unfold EvmYul.Account.updateTransientStorage
  by_cases hZero : (value == default) = true
  · simp [hZero]
    exact
      { nonce := hAccount.nonce
        balance := hAccount.balance
        storage := hAccount.storage
        tstorage := by simp [hAccount.tstorage]
        codeEmpty := hAccount.codeEmpty
        codeBytes := hAccount.codeBytes
        code := hAccount.code }
  · simp [hZero]
    exact
      { nonce := hAccount.nonce
        balance := hAccount.balance
        storage := hAccount.storage
        tstorage := by simp [hAccount.tstorage]
        codeEmpty := hAccount.codeEmpty
        codeBytes := hAccount.codeBytes
        code := hAccount.code }

theorem CompiledAccountRel.default_with_balance
    (balance : EvmYul.UInt256) :
    CompiledAccountRel
      { (default : EvmYul.Account .Yul) with balance := balance }
      { (default : EvmYul.Account .EVM) with balance := balance } := by
  exact
    { nonce := rfl
      balance := rfl
      storage := rfl
      tstorage := rfl
      codeEmpty := by
        change ((default : AstContract) == default) =
          ByteArray.isEmpty (default : ByteArray)
        native_decide
      codeBytes := rfl
      code := CompiledCodeRel.empty }

theorem CompiledAccountRel.checkedCodeResourcesSourceStatic_of_yul_code_ne_default
    {yul : EvmYul.Account .Yul} {evm : EvmYul.Account .EVM}
    (hAccount : CompiledAccountRel yul evm)
    (hCodeNondefault : yul.code ≠ default) :
    ∃ (program : Program) (asm : Assembly.Program)
        (target : Assembly.TargetProgram),
      program.contract = yul.code ∧
        compileCheckedAssemblyTargetBytecodeResourcesSourceStatic? program =
          some (asm, target) ∧
        Program.RecursiveBridgeSourceStaticFacts program ∧
        Program.SourceAccepted program ∧
        Program.SourceCompileAccepted program ∧
        Program.compileChecked? program = some asm ∧
        Program.compileCheckedAssemblyTargetBytecode? program =
          some (asm, target) ∧
        _root_.EvmCompiler.Yul.Program.RecursiveBridgeCompileResources program ∧
        Assembly.Bytecode.TargetFitsDecodeWindow target ∧
        Assembly.Bytecode.JumpdestCorrect target ∧
        evm.code = Assembly.Bytecode.encodeTarget target := by
  exact
    CompiledCodeRel.checkedBytecodeResourcesSourceStatic_of_not_empty
      hAccount.code
      (by
        intro hEmpty
        exact hCodeNondefault hEmpty.1)

theorem CompiledAccountRel.evm_code_isEmpty_of_yul_code_default
    {yul : EvmYul.Account .Yul} {evm : EvmYul.Account .EVM}
    (hAccount : CompiledAccountRel yul evm)
    (hCodeDefault : yul.code = default) :
    evm.code.isEmpty = true := by
  have hDefaultBeq :
      ((default : AstContract) == default) = true := by
    native_decide
  simpa [hCodeDefault, hDefaultBeq] using hAccount.codeEmpty.symm

theorem byteArray_eq_default_of_isEmpty
    {bytes : ByteArray} (hEmpty : bytes.isEmpty = true) :
    bytes = default := by
  apply ByteArray.ext
  apply Array.ext
  · simpa [ByteArray.isEmpty] using hEmpty
  · intro i _hBytes hDefault
    have hDefaultSize : (default : ByteArray).data.size = 0 := rfl
    omega

theorem CompiledAccountRel.evm_code_eq_default_of_yul_code_default
    {yul : EvmYul.Account .Yul} {evm : EvmYul.Account .EVM}
    (hAccount : CompiledAccountRel yul evm)
    (hCodeDefault : yul.code = default) :
    evm.code = default :=
  byteArray_eq_default_of_isEmpty
    (hAccount.evm_code_isEmpty_of_yul_code_default hCodeDefault)

inductive CompiledToExecuteRel :
    EvmYul.ToExecute .Yul → EvmYul.ToExecute .EVM → Prop
  | precompiled (precompiled : EvmYul.PrecompiledContract) :
      CompiledToExecuteRel
        (EvmYul.ToExecute.Precompiled precompiled)
        (EvmYul.ToExecute.Precompiled precompiled)
  | code {contract : AstContract} {bytes : ByteArray}
      (hCode : CompiledCodeRel contract bytes) :
      CompiledToExecuteRel
        (EvmYul.ToExecute.Code contract)
        (EvmYul.ToExecute.Code bytes)

structure CompiledAccountMapRel (yul : EvmYul.AccountMap .Yul)
    (evm : EvmYul.AccountMap .EVM) : Prop where
  yul_to_evm :
    ∀ addr yulAccount,
      yul.find? addr = some yulAccount →
        ∃ evmAccount,
          evm.find? addr = some evmAccount ∧
            CompiledAccountRel yulAccount evmAccount
  evm_to_yul :
    ∀ addr evmAccount,
      evm.find? addr = some evmAccount →
        ∃ yulAccount,
          yul.find? addr = some yulAccount ∧
            CompiledAccountRel yulAccount evmAccount

def accountMapRel : Reference.AccountMapRel :=
  CompiledAccountMapRel

theorem CompiledAccountMapRel.find_yul
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    {addr : EvmYul.AccountAddress} {yulAccount : EvmYul.Account .Yul}
    (hFind : yul.find? addr = some yulAccount) :
    ∃ evmAccount,
      evm.find? addr = some evmAccount ∧
        CompiledAccountRel yulAccount evmAccount :=
  hWorld.yul_to_evm addr yulAccount hFind

theorem CompiledAccountMapRel.checkedCodeResourcesSourceStatic_of_find_yul_ne_default
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    {addr : EvmYul.AccountAddress} {yulAccount : EvmYul.Account .Yul}
    (hFind : yul.find? addr = some yulAccount)
    (hCodeNondefault : yulAccount.code ≠ default) :
    ∃ (evmAccount : EvmYul.Account .EVM)
      (program : Program) (asm : Assembly.Program)
      (target : Assembly.TargetProgram),
      evm.find? addr = some evmAccount ∧
        CompiledAccountRel yulAccount evmAccount ∧
        program.contract = yulAccount.code ∧
        compileCheckedAssemblyTargetBytecodeResourcesSourceStatic? program =
          some (asm, target) ∧
        Program.RecursiveBridgeSourceStaticFacts program ∧
        Program.SourceAccepted program ∧
        Program.SourceCompileAccepted program ∧
        Program.compileChecked? program = some asm ∧
        Program.compileCheckedAssemblyTargetBytecode? program =
          some (asm, target) ∧
        _root_.EvmCompiler.Yul.Program.RecursiveBridgeCompileResources program ∧
        Assembly.Bytecode.TargetFitsDecodeWindow target ∧
        Assembly.Bytecode.JumpdestCorrect target ∧
        evmAccount.code = Assembly.Bytecode.encodeTarget target := by
  rcases hWorld.find_yul hFind with
    ⟨evmAccount, hFindEvm, hAccount⟩
  rcases
      hAccount.checkedCodeResourcesSourceStatic_of_yul_code_ne_default
        hCodeNondefault with
    ⟨program, asm, target, hContract, hCompile, hStatic,
      hSourceAccepted, hSourceCompileAccepted, hCompileChecked, hBytecode,
      hResources, hDecode, hJumpdest, hBytes⟩
  exact
    ⟨evmAccount, program, asm, target, hFindEvm, hAccount, hContract,
      hCompile, hStatic, hSourceAccepted, hSourceCompileAccepted,
      hCompileChecked, hBytecode, hResources, hDecode, hJumpdest, hBytes⟩

theorem CompiledAccountMapRel.evm_code_isEmpty_of_find_yul_default
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    {addr : EvmYul.AccountAddress} {yulAccount : EvmYul.Account .Yul}
    (hFind : yul.find? addr = some yulAccount)
    (hCodeDefault : yulAccount.code = default) :
    ∃ evmAccount,
      evm.find? addr = some evmAccount ∧
        CompiledAccountRel yulAccount evmAccount ∧
        evmAccount.code.isEmpty = true := by
  rcases hWorld.find_yul hFind with
    ⟨evmAccount, hFindEvm, hAccount⟩
  exact
    ⟨evmAccount, hFindEvm, hAccount,
      hAccount.evm_code_isEmpty_of_yul_code_default hCodeDefault⟩

theorem CompiledAccountMapRel.find_evm
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    {addr : EvmYul.AccountAddress} {evmAccount : EvmYul.Account .EVM}
    (hFind : evm.find? addr = some evmAccount) :
    ∃ yulAccount,
      yul.find? addr = some yulAccount ∧
        CompiledAccountRel yulAccount evmAccount :=
  hWorld.evm_to_yul addr evmAccount hFind

theorem CompiledAccountMapRel.empty :
    CompiledAccountMapRel
      (∅ : EvmYul.AccountMap .Yul)
      (∅ : EvmYul.AccountMap .EVM) := by
  refine
    { yul_to_evm := ?_
      evm_to_yul := ?_ }
  · intro _addr _yulAccount hFind
    rcases Batteries.RBMap.find?_some_mem_toList hFind with
      ⟨_, hMem, _⟩
    simp at hMem
  · intro _addr _evmAccount hFind
    rcases Batteries.RBMap.find?_some_mem_toList hFind with
      ⟨_, hMem, _⟩
    simp at hMem

theorem accountMap_isEmpty_false_of_find?
    {τ : EvmYul.OperationType}
    {accountMap : EvmYul.AccountMap τ}
    {addr : EvmYul.AccountAddress} {account : EvmYul.Account τ}
    (hFind : accountMap.find? addr = some account) :
    accountMap.isEmpty = false := by
  cases hEmpty : accountMap.isEmpty
  · rfl
  · have hListEmpty : accountMap.toList = [] := by
      simpa [Batteries.RBMap.isEmpty] using
        (Batteries.RBSet.isEmpty_iff_toList_eq_nil
          (t := (accountMap : Batteries.RBSet _ _))).mp hEmpty
    rcases Batteries.RBMap.find?_some_mem_toList hFind with
      ⟨_, hMem, _⟩
    simp [hListEmpty] at hMem

theorem accountMap_exists_find?_of_isEmpty_false
    {τ : EvmYul.OperationType}
    {accountMap : EvmYul.AccountMap τ}
    (hEmpty : accountMap.isEmpty = false) :
    ∃ addr account, accountMap.find? addr = some account := by
  have hListNe : accountMap.toList ≠ [] := by
    intro hNil
    have hEmptyTrue : accountMap.isEmpty = true := by
      simpa [Batteries.RBMap.isEmpty] using
        (Batteries.RBSet.isEmpty_iff_toList_eq_nil
          (t := (accountMap : Batteries.RBSet _ _))).mpr hNil
    simp [hEmpty] at hEmptyTrue
  cases hList : accountMap.toList with
  | nil => exact False.elim (hListNe hList)
  | cons entry _tail =>
      rcases entry with ⟨addr, account⟩
      refine ⟨addr, account, ?_⟩
      rw [Batteries.RBMap.find?_some]
      exact ⟨addr, by simp [hList], by simp⟩

theorem CompiledAccountMapRel.isEmpty_eq
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm) :
    yul.isEmpty = evm.isEmpty := by
  cases hYul : yul.isEmpty
  · cases hEvm : evm.isEmpty
    · rfl
    · rcases accountMap_exists_find?_of_isEmpty_false hYul with
        ⟨addr, yulAccount, hFindYul⟩
      rcases hWorld.find_yul hFindYul with
        ⟨evmAccount, hFindEvm, _hAccount⟩
      have hEvmFalse :=
        accountMap_isEmpty_false_of_find? hFindEvm
      simp [hEvm] at hEvmFalse
  · cases hEvm : evm.isEmpty
    · rcases accountMap_exists_find?_of_isEmpty_false hEvm with
        ⟨addr, evmAccount, hFindEvm⟩
      rcases hWorld.find_evm hFindEvm with
        ⟨yulAccount, hFindYul, _hAccount⟩
      have hYulFalse :=
        accountMap_isEmpty_false_of_find? hFindYul
      simp [hYul] at hYulFalse
    · rfl

theorem CompiledAccountMapRel.if_empty_parent
    {yulParent yulChild : EvmYul.AccountMap .Yul}
    {evmParent evmChild : EvmYul.AccountMap .EVM}
    (hParent : CompiledAccountMapRel yulParent evmParent)
    (hChild : CompiledAccountMapRel yulChild evmChild)
    (hEmpty : yulChild.isEmpty = evmChild.isEmpty) :
    CompiledAccountMapRel
      (if yulChild.isEmpty then
        yulParent
      else
        yulChild)
      (if evmChild.isEmpty then
        evmParent
      else
        evmChild) := by
  cases hEvm : evmChild.isEmpty
  · have hYul : yulChild.isEmpty = false := by
      simpa [hEvm] using hEmpty
    simp [hYul]
    exact hChild
  · have hYul : yulChild.isEmpty = true := by
      simpa [hEvm] using hEmpty
    simp [hYul]
    exact hParent

theorem CompiledAccountMapRel.not_find_yul_of_not_find_evm
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    {addr : EvmYul.AccountAddress}
    (hFind : evm.find? addr = none) :
    yul.find? addr = none := by
  cases hYul : yul.find? addr with
  | none => rfl
  | some yulAccount =>
      rcases hWorld.find_yul hYul with ⟨evmAccount, hEvm, _⟩
      simp [hFind] at hEvm

theorem CompiledAccountMapRel.not_find_evm_of_not_find_yul
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    {addr : EvmYul.AccountAddress}
    (hFind : yul.find? addr = none) :
    evm.find? addr = none := by
  cases hEvm : evm.find? addr with
  | none => rfl
  | some evmAccount =>
      rcases hWorld.find_evm hEvm with ⟨yulAccount, hYul, _⟩
      simp [hFind] at hYul

theorem CompiledAccountMapRel.balance_at
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    (addr : EvmYul.AccountAddress) :
    (yul.find? addr |>.elim ⟨0⟩ (·.balance)) =
      (evm.find? addr |>.elim ⟨0⟩ (·.balance)) := by
  cases hYul : yul.find? addr with
  | none =>
      have hEvm := hWorld.not_find_evm_of_not_find_yul hYul
      simp [hEvm]
  | some yulAccount =>
      rcases hWorld.find_yul hYul with
        ⟨evmAccount, hEvm, hAccount⟩
      simp [hEvm, hAccount.balance]

theorem CompiledAccountMapRel.storage_at
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    (addr : EvmYul.AccountAddress) (slot : EvmYul.UInt256) :
    (yul.find? addr |>.option ⟨0⟩
        (EvmYul.Account.lookupStorage (k := slot))) =
      (evm.find? addr |>.option ⟨0⟩
        (EvmYul.Account.lookupStorage (k := slot))) := by
  cases hYul : yul.find? addr with
  | none =>
      have hEvm := hWorld.not_find_evm_of_not_find_yul hYul
      rw [hEvm]
      rfl
  | some yulAccount =>
      rcases hWorld.find_yul hYul with
        ⟨evmAccount, hEvm, hAccount⟩
      rw [hEvm]
      exact
        congrArg (fun storage =>
          Batteries.RBMap.findD storage slot (⟨0⟩ : EvmYul.UInt256))
          hAccount.storage

theorem CompiledAccountMapRel.transientStorage_at
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    (addr : EvmYul.AccountAddress) (slot : EvmYul.UInt256) :
    (yul.find? addr |>.option ⟨0⟩
        (EvmYul.Account.lookupTransientStorage (k := slot))) =
      (evm.find? addr |>.option ⟨0⟩
        (EvmYul.Account.lookupTransientStorage (k := slot))) := by
  cases hYul : yul.find? addr with
  | none =>
      have hEvm := hWorld.not_find_evm_of_not_find_yul hYul
      rw [hEvm]
      rfl
  | some yulAccount =>
      rcases hWorld.find_yul hYul with
        ⟨evmAccount, hEvm, hAccount⟩
      rw [hEvm]
      exact
        congrArg (fun storage =>
          Batteries.RBMap.findD storage slot (⟨0⟩ : EvmYul.UInt256))
          hAccount.tstorage

theorem CompiledAccountMapRel.insert
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    (addr : EvmYul.AccountAddress)
    {yulAccount : EvmYul.Account .Yul} {evmAccount : EvmYul.Account .EVM}
    (hAccount : CompiledAccountRel yulAccount evmAccount) :
    CompiledAccountMapRel
      (yul.insert addr yulAccount)
      (evm.insert addr evmAccount) := by
  refine
    { yul_to_evm := ?_
      evm_to_yul := ?_ }
  · intro query foundYul hFind
    rw [Batteries.RBMap.find?_insert] at hFind ⊢
    split at hFind <;> rename_i hCmp
    · cases hFind
      exact ⟨evmAccount, by simp [hCmp], hAccount⟩
    · rcases hWorld.find_yul hFind with
        ⟨foundEvm, hFoundEvm, hFoundAccount⟩
      exact ⟨foundEvm, by simp [hCmp, hFoundEvm], hFoundAccount⟩
  · intro query foundEvm hFind
    rw [Batteries.RBMap.find?_insert] at hFind ⊢
    split at hFind <;> rename_i hCmp
    · cases hFind
      exact ⟨yulAccount, by simp [hCmp], hAccount⟩
    · rcases hWorld.find_evm hFind with
        ⟨foundYul, hFoundYul, hFoundAccount⟩
      exact ⟨foundYul, by simp [hCmp, hFoundYul], hFoundAccount⟩

theorem accountAddress_eq_of_compare_eq {a b : EvmYul.AccountAddress}
    (h : compare a b = Ordering.eq) : a = b := by
  apply Fin.ext
  change compare a.val b.val = Ordering.eq at h
  exact compare_eq_iff_eq.1 h

theorem CompiledAccountMapRel.insert_insert_distinct_comm
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    {a b : EvmYul.AccountAddress}
    (hAB : compare a b ≠ Ordering.eq)
    (hBA : compare b a ≠ Ordering.eq)
    {yulA : EvmYul.Account .Yul} {evmA : EvmYul.Account .EVM}
    {yulB : EvmYul.Account .Yul} {evmB : EvmYul.Account .EVM}
    (hA : CompiledAccountRel yulA evmA)
    (hB : CompiledAccountRel yulB evmB) :
    CompiledAccountMapRel
      ((yul.insert a yulA).insert b yulB)
      ((evm.insert b evmB).insert a evmA) := by
  refine
    { yul_to_evm := ?_
      evm_to_yul := ?_ }
  · intro query foundYul hFind
    rw [Batteries.RBMap.find?_insert] at hFind
    split at hFind <;> rename_i hQueryB
    · have hQueryEq : query = b := accountAddress_eq_of_compare_eq hQueryB
      subst query
      cases hFind
      refine ⟨evmB, ?_, hB⟩
      rw [Batteries.RBMap.find?_insert]
      simp [hBA, Batteries.RBMap.find?_insert]
    · rw [Batteries.RBMap.find?_insert] at hFind
      split at hFind <;> rename_i hQueryA
      · have hQueryEq : query = a := accountAddress_eq_of_compare_eq hQueryA
        subst query
        cases hFind
        refine ⟨evmA, ?_, hA⟩
        rw [Batteries.RBMap.find?_insert]
        simp
      · rcases hWorld.find_yul hFind with
          ⟨foundEvm, hFoundEvm, hFoundAccount⟩
        refine ⟨foundEvm, ?_, hFoundAccount⟩
        rw [Batteries.RBMap.find?_insert]
        simp [hQueryA, Batteries.RBMap.find?_insert, hQueryB, hFoundEvm]
  · intro query foundEvm hFind
    rw [Batteries.RBMap.find?_insert] at hFind
    split at hFind <;> rename_i hQueryA
    · have hQueryEq : query = a := accountAddress_eq_of_compare_eq hQueryA
      subst query
      cases hFind
      refine ⟨yulA, ?_, hA⟩
      rw [Batteries.RBMap.find?_insert]
      simp [hAB, Batteries.RBMap.find?_insert]
    · rw [Batteries.RBMap.find?_insert] at hFind
      split at hFind <;> rename_i hQueryB
      · have hQueryEq : query = b := accountAddress_eq_of_compare_eq hQueryB
        subst query
        cases hFind
        refine ⟨yulB, ?_, hB⟩
        rw [Batteries.RBMap.find?_insert]
        simp
      · rcases hWorld.find_evm hFind with
          ⟨foundYul, hFoundYul, hFoundAccount⟩
        refine ⟨foundYul, ?_, hFoundAccount⟩
        rw [Batteries.RBMap.find?_insert]
        simp [hQueryB, Batteries.RBMap.find?_insert, hQueryA, hFoundYul]

theorem CompiledAccountMapRel.selfdestructAccountMap
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    (source target : EvmYul.AccountAddress) (created : Bool) :
    CompiledAccountMapRel
      (EvmYul.selfdestructAccountMap yul source target created)
      (EvmYul.selfdestructAccountMap evm source target created) := by
  unfold EvmYul.selfdestructAccountMap
  cases hYulSource : yul.find? source with
  | none =>
      have hEvmSource := hWorld.not_find_evm_of_not_find_yul hYulSource
      simp [hEvmSource]
      exact hWorld
  | some yulSource =>
      rcases hWorld.find_yul hYulSource with
        ⟨evmSource, hEvmSource, hSourceRel⟩
      simp [hEvmSource]
      cases hYulTarget : yul.find? target with
      | none =>
          have hEvmTarget := hWorld.not_find_evm_of_not_find_yul hYulTarget
          simp [hEvmTarget, ← hSourceRel.balance]
          by_cases hZero :
              (yulSource.balance == (⟨0⟩ : EvmYul.UInt256)) = true
          · simpa [hZero] using hWorld
          · have hNonzero :
                (yulSource.balance == (⟨0⟩ : EvmYul.UInt256)) = false := by
              cases hBal :
                  (yulSource.balance == (⟨0⟩ : EvmYul.UInt256)) <;>
                simp [hBal] at hZero ⊢
            simpa [hNonzero] using
              (hWorld.insert target
                (CompiledAccountRel.default_with_balance yulSource.balance)).insert
                source (hSourceRel.with_balance (⟨0⟩ : EvmYul.UInt256))
      | some yulTarget =>
          rcases hWorld.find_yul hYulTarget with
            ⟨evmTarget, hEvmTarget, hTargetRel⟩
          simp [hEvmTarget]
          by_cases hDistinct : target ≠ source
          · simp [hDistinct]
            have hTargetBalance :
                CompiledAccountRel
                  { yulTarget with
                    balance := yulTarget.balance + yulSource.balance }
                  { evmTarget with
                    balance := evmTarget.balance + evmSource.balance } := by
              rw [← hTargetRel.balance, ← hSourceRel.balance]
              exact hTargetRel.with_balance
                (yulTarget.balance + yulSource.balance)
            exact
              (hWorld.insert target hTargetBalance).insert source
                (hSourceRel.with_balance (⟨0⟩ : EvmYul.UInt256))
          · have hEq : target = source := by
              by_contra hEq
              exact hDistinct hEq
            subst target
            cases created
            · simpa using hWorld
            · simpa using
                (hWorld.insert source
                  (hTargetRel.with_balance
                    (⟨0⟩ : EvmYul.UInt256))).insert source
                  (hSourceRel.with_balance (⟨0⟩ : EvmYul.UInt256))

theorem CompiledAccountMapRel.increaseBalance
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    (addr : EvmYul.AccountAddress) (amount : EvmYul.UInt256) :
    CompiledAccountMapRel
      (EvmYul.AccountMap.increaseBalance .Yul yul addr amount)
      (EvmYul.AccountMap.increaseBalance .EVM evm addr amount) := by
  unfold EvmYul.AccountMap.increaseBalance
  cases hYul : yul.find? addr with
  | none =>
      cases hEvm : evm.find? addr with
      | none =>
          exact hWorld.insert addr
            (CompiledAccountRel.default_with_balance amount)
      | some evmAccount =>
          rcases hWorld.find_evm hEvm with ⟨_, hYulFound, _⟩
          simp [hYul] at hYulFound
  | some yulAccount =>
      rcases hWorld.find_yul hYul with
        ⟨evmAccount, hEvmFound, hAccount⟩
      cases hEvm : evm.find? addr with
      | none =>
          simp [hEvm] at hEvmFound
      | some evmAccount' =>
          have hSame : evmAccount = evmAccount' :=
            Option.some.inj (hEvmFound.symm.trans hEvm)
          subst evmAccount'
          have hIncreased :
              CompiledAccountRel
                { yulAccount with balance := yulAccount.balance + amount }
                { evmAccount with balance := evmAccount.balance + amount } := by
            rw [← hAccount.balance]
            exact hAccount.with_balance (yulAccount.balance + amount)
          exact hWorld.insert addr hIncreased

theorem CompiledAccountMapRel.updateStorage_at
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    (addr : EvmYul.AccountAddress) (slot value : EvmYul.UInt256) :
    CompiledAccountMapRel
      (match yul.find? addr with
      | none => yul
      | some account =>
          yul.insert addr (EvmYul.Account.updateStorage account slot value))
      (match evm.find? addr with
      | none => evm
      | some account =>
          evm.insert addr (EvmYul.Account.updateStorage account slot value)) := by
  cases hYul : yul.find? addr with
  | none =>
      have hEvm := hWorld.not_find_evm_of_not_find_yul hYul
      simp [hEvm, hWorld]
  | some yulAccount =>
      rcases hWorld.find_yul hYul with
        ⟨evmAccount, hEvm, hAccount⟩
      simp [hEvm]
      exact hWorld.insert addr (hAccount.update_storage slot value)

theorem CompiledAccountMapRel.updateTransientStorage_at
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    (addr : EvmYul.AccountAddress) (slot value : EvmYul.UInt256) :
    CompiledAccountMapRel
      (match yul.find? addr with
      | none => yul
      | some account =>
          yul.insert addr
            (EvmYul.Account.updateTransientStorage account slot value))
      (match evm.find? addr with
      | none => evm
      | some account =>
          evm.insert addr
            (EvmYul.Account.updateTransientStorage account slot value)) := by
  cases hYul : yul.find? addr with
  | none =>
      have hEvm := hWorld.not_find_evm_of_not_find_yul hYul
      simp [hEvm, hWorld]
  | some yulAccount =>
      rcases hWorld.find_yul hYul with
        ⟨evmAccount, hEvm, hAccount⟩
      simp [hEvm]
      exact hWorld.insert addr (hAccount.update_transientStorage slot value)

theorem CompiledAccountMapRel.decreaseBalance_of_yul
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    {addr : EvmYul.AccountAddress} {amount : EvmYul.UInt256}
    {yulAfter : EvmYul.AccountMap .Yul}
    (hDecrease :
      EvmYul.AccountMap.decreaseBalance .Yul yul addr amount =
        some yulAfter) :
    ∃ evmAfter,
      EvmYul.AccountMap.decreaseBalance .EVM evm addr amount =
          some evmAfter ∧
        CompiledAccountMapRel yulAfter evmAfter := by
  unfold EvmYul.AccountMap.decreaseBalance at hDecrease ⊢
  cases hYul : yul.find? addr with
  | none =>
      simp [hYul] at hDecrease
  | some yulAccount =>
      rcases hWorld.find_yul hYul with
        ⟨evmAccount, hEvmFound, hAccount⟩
      simp [hYul] at hDecrease
      by_cases hTooSmall : yulAccount.balance < amount
      · simp [hTooSmall] at hDecrease
      · have hEvmEnough : ¬ evmAccount.balance < amount := by
          simpa [← hAccount.balance] using hTooSmall
        refine
          ⟨evm.insert addr
              { evmAccount with balance := evmAccount.balance - amount },
            ?_, ?_⟩
        · simp [hEvmFound, hEvmEnough]
        · simp [hTooSmall] at hDecrease
          subst yulAfter
          have hDecreased :
              CompiledAccountRel
                { yulAccount with balance := yulAccount.balance - amount }
                { evmAccount with balance := evmAccount.balance - amount } := by
            rw [← hAccount.balance]
            exact hAccount.with_balance (yulAccount.balance - amount)
          exact hWorld.insert addr hDecreased

/--
Account-map part of the EVM `Θ` CALL prelude.

This deliberately mirrors EVM order instead of `AccountMap.transferBalance`:
the recipient is credited/materialized first, missing recipients are
materialized only for nonzero value, and the sender is debited afterward.
-/
abbrev callRecipientCredit {τ : EvmYul.OperationType}
    (accountMap : EvmYul.AccountMap τ)
    (recipient : EvmYul.AccountAddress)
    (value : EvmYul.UInt256) : EvmYul.AccountMap τ :=
  EvmYul.Yul.callRecipientCredit accountMap recipient value

abbrev callSourceDebit {τ : EvmYul.OperationType}
    (accountMap : EvmYul.AccountMap τ)
    (source : EvmYul.AccountAddress)
    (value : EvmYul.UInt256) : EvmYul.AccountMap τ :=
  EvmYul.Yul.callSourceDebit accountMap source value

abbrev callTransferUnchecked {τ : EvmYul.OperationType}
    (accountMap : EvmYul.AccountMap τ)
    (source recipient : EvmYul.AccountAddress)
    (value : EvmYul.UInt256) : EvmYul.AccountMap τ :=
  EvmYul.Yul.callTransferUnchecked accountMap source recipient value

def evmCallTransfer (evm : EvmYul.AccountMap .EVM)
    (source recipient : EvmYul.AccountAddress)
    (value : EvmYul.UInt256) : EvmYul.AccountMap .EVM :=
  callTransferUnchecked evm source recipient value

theorem evmCallTransfer_eq_thetaCallTransfer
    (evm : EvmYul.AccountMap .EVM)
    (source recipient : EvmYul.AccountAddress)
    (value : EvmYul.UInt256) :
    evmCallTransfer evm source recipient value =
      EvmYul.EVM.thetaCallTransfer evm source recipient value := by
  unfold evmCallTransfer callTransferUnchecked
    EvmYul.Yul.callTransferUnchecked EvmYul.Yul.callSourceDebit
    EvmYul.Yul.callRecipientCredit EvmYul.EVM.thetaCallTransfer
    EvmYul.EVM.thetaCallSourceDebit EvmYul.EVM.thetaCallRecipientCredit
  cases evm.find? recipient with
  | none =>
      by_cases hValue : (value != (⟨0⟩ : EvmYul.UInt256)) = true
      · simp [hValue]
        split <;> simp_all
      · simp [hValue]
        split <;> simp_all
  | some _account =>
      simp
      split <;> simp_all

theorem callRecipientCredit_isEmpty_false_of_parent_false
    {τ : EvmYul.OperationType}
    {accountMap : EvmYul.AccountMap τ}
    (recipient : EvmYul.AccountAddress)
    (value : EvmYul.UInt256)
    (hParent : accountMap.isEmpty = false) :
    (callRecipientCredit accountMap recipient value).isEmpty = false := by
  unfold callRecipientCredit EvmYul.Yul.callRecipientCredit
  cases hRecipient : accountMap.find? recipient with
  | none =>
      by_cases hValue :
          (value != (⟨0⟩ : EvmYul.UInt256)) = true
      · have hFind :
            (accountMap.insert recipient
                { (default : EvmYul.Account τ) with balance := value }).find?
              recipient =
                some { (default : EvmYul.Account τ) with balance := value } := by
          simp [Batteries.RBMap.find?_insert]
        simpa [hRecipient, hValue] using
          accountMap_isEmpty_false_of_find? hFind
      · simp [hValue, hParent]
  | some account =>
      have hFind :
          (accountMap.insert recipient
              { account with balance := account.balance + value }).find?
            recipient =
              some { account with balance := account.balance + value } := by
        simp [Batteries.RBMap.find?_insert]
      simpa [hRecipient] using accountMap_isEmpty_false_of_find? hFind

theorem callSourceDebit_isEmpty_false_of_parent_false
    {τ : EvmYul.OperationType}
    {accountMap : EvmYul.AccountMap τ}
    (source : EvmYul.AccountAddress)
    (value : EvmYul.UInt256)
    (hParent : accountMap.isEmpty = false) :
    (callSourceDebit accountMap source value).isEmpty = false := by
  unfold callSourceDebit EvmYul.Yul.callSourceDebit
  cases hSource : accountMap.find? source with
  | none =>
      simp [hParent]
  | some account =>
      have hFind :
          (accountMap.insert source
              { account with balance := account.balance - value }).find?
            source =
              some { account with balance := account.balance - value } := by
        simp [Batteries.RBMap.find?_insert]
      simpa [hSource] using accountMap_isEmpty_false_of_find? hFind

theorem callTransferUnchecked_isEmpty_false_of_parent_false
    {τ : EvmYul.OperationType}
    {accountMap : EvmYul.AccountMap τ}
    (source recipient : EvmYul.AccountAddress)
    (value : EvmYul.UInt256)
    (hParent : accountMap.isEmpty = false) :
    (callTransferUnchecked accountMap source recipient value).isEmpty =
      false := by
  unfold callTransferUnchecked EvmYul.Yul.callTransferUnchecked
  exact
    callSourceDebit_isEmpty_false_of_parent_false source value
      (callRecipientCredit_isEmpty_false_of_parent_false recipient value
        hParent)

theorem CompiledAccountMapRel.callTransferUnchecked_preserve
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    (source recipient : EvmYul.AccountAddress)
    (value : EvmYul.UInt256) :
    CompiledAccountMapRel
      (callTransferUnchecked yul source recipient value)
      (callTransferUnchecked evm source recipient value) := by
  have hRecipientIncreased :
      CompiledAccountMapRel
        (callRecipientCredit yul recipient value)
        (callRecipientCredit evm recipient value) := by
    unfold callRecipientCredit EvmYul.Yul.callRecipientCredit
    cases hRecipientYul : yul.find? recipient with
    | none =>
        have hRecipientEvm :=
          hWorld.not_find_evm_of_not_find_yul hRecipientYul
        by_cases hValue :
            (value != (⟨0⟩ : EvmYul.UInt256)) = true
        · simp [hRecipientEvm, hValue]
          exact hWorld.insert recipient
            (CompiledAccountRel.default_with_balance value)
        · simp [hRecipientEvm, hValue]
          exact hWorld
    | some yulRecipientAccount =>
        rcases hWorld.find_yul hRecipientYul with
          ⟨evmRecipientAccount, hRecipientEvm, hRecipientRel⟩
        simp [hRecipientEvm]
        have hIncreased :
            CompiledAccountRel
              { yulRecipientAccount with
                balance := yulRecipientAccount.balance + value }
              { evmRecipientAccount with
                balance := evmRecipientAccount.balance + value } := by
          rw [← hRecipientRel.balance]
          exact hRecipientRel.with_balance
            (yulRecipientAccount.balance + value)
        exact hWorld.insert recipient hIncreased
  change
    CompiledAccountMapRel
      (callSourceDebit (callRecipientCredit yul recipient value) source value)
      (callSourceDebit (callRecipientCredit evm recipient value) source value)
  unfold callSourceDebit EvmYul.Yul.callSourceDebit
  cases hSourceYul :
      (callRecipientCredit yul recipient value).find? source with
  | none =>
      have hSourceEvm :=
        hRecipientIncreased.not_find_evm_of_not_find_yul hSourceYul
      rw [hSourceEvm]
      exact hRecipientIncreased
  | some yulSourceAccount =>
      rcases hRecipientIncreased.find_yul hSourceYul with
        ⟨evmSourceAccount, hSourceEvm, hSourceRel⟩
      rw [hSourceEvm]
      have hDecreased :
          CompiledAccountRel
            { yulSourceAccount with
              balance := yulSourceAccount.balance - value }
            { evmSourceAccount with
              balance := evmSourceAccount.balance - value } := by
        rw [← hSourceRel.balance]
        exact hSourceRel.with_balance
          (yulSourceAccount.balance - value)
      exact hRecipientIncreased.insert source hDecreased

theorem CompiledAccountMapRel.callTransferAccountMap?_of_yul
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    {source recipient : EvmYul.AccountAddress}
    {value : EvmYul.UInt256}
    {yulAfter : EvmYul.AccountMap .Yul}
    (hTransfer :
      EvmYul.Yul.callTransferAccountMap? yul source recipient value =
        some yulAfter) :
    CompiledAccountMapRel yulAfter
      (evmCallTransfer evm source recipient value) := by
  by_cases hEnough :
      value ≤ (yul.find? source |>.option ⟨0⟩ (·.balance))
  · have hUnchecked :
        EvmYul.Yul.callTransferAccountMap? yul source recipient value =
          some (World.callTransferUnchecked yul source recipient value) := by
      simp [EvmYul.Yul.callTransferAccountMap?, hEnough,
        World.callTransferUnchecked]
    rw [hTransfer] at hUnchecked
    cases hUnchecked
    simpa [evmCallTransfer] using
      hWorld.callTransferUnchecked_preserve source recipient value
  · simp [EvmYul.Yul.callTransferAccountMap?, hEnough] at hTransfer

theorem CompiledAccountMapRel.callTransferEnough_iff
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    (source : EvmYul.AccountAddress)
    (value : EvmYul.UInt256) :
    (value ≤ (yul.find? source |>.option ⟨0⟩ (·.balance))) ↔
      value ≤ (evm.find? source |>.option ⟨0⟩ (·.balance)) := by
  have hBalance :
      (yul.find? source |>.option ⟨0⟩ (·.balance)) =
        (evm.find? source |>.option ⟨0⟩ (·.balance)) := by
    cases hYul : yul.find? source with
    | none =>
        have hEvm := hWorld.not_find_evm_of_not_find_yul hYul
        simp [Option.option, hEvm]
    | some yulAccount =>
        rcases hWorld.find_yul hYul with
          ⟨evmAccount, hEvm, hAccount⟩
        simp [Option.option, hEvm, hAccount.balance]
  rw [hBalance]

theorem CompiledAccountMapRel.callTransferAccountMap?_of_evm_enough
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    {source recipient : EvmYul.AccountAddress}
    {value : EvmYul.UInt256}
    (hEnough :
      value ≤ (evm.find? source |>.option ⟨0⟩ (·.balance))) :
    ∃ yulAfter,
      EvmYul.Yul.callTransferAccountMap? yul source recipient value =
          some yulAfter ∧
        CompiledAccountMapRel yulAfter
          (evmCallTransfer evm source recipient value) := by
  have hYulEnough :
      value ≤ (yul.find? source |>.option ⟨0⟩ (·.balance)) :=
    (hWorld.callTransferEnough_iff source value).mpr hEnough
  refine
    ⟨callTransferUnchecked yul source recipient value, ?_, ?_⟩
  · simp [EvmYul.Yul.callTransferAccountMap?, hYulEnough,
      callTransferUnchecked]
  · simpa [evmCallTransfer] using
      hWorld.callTransferUnchecked_preserve source recipient value

theorem CompiledAccountMapRel.callTransferAccountMap?_of_evm_enough_find_yul_nonempty
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    {source recipient : EvmYul.AccountAddress}
    {value : EvmYul.UInt256}
    {yulRecipient : EvmYul.Account .Yul}
    (hFindRecipient : yul.find? recipient = some yulRecipient)
    (hEnough :
      value ≤ (evm.find? source |>.option ⟨0⟩ (·.balance))) :
    ∃ yulAfter,
      EvmYul.Yul.callTransferAccountMap? yul source recipient value =
          some yulAfter ∧
        yulAfter.isEmpty = false ∧
        (evmCallTransfer evm source recipient value).isEmpty = false ∧
        CompiledAccountMapRel yulAfter
          (evmCallTransfer evm source recipient value) := by
  rcases
      hWorld.callTransferAccountMap?_of_evm_enough
        (source := source) (recipient := recipient) hEnough with
    ⟨yulAfter, hTransfer, hTransferRel⟩
  rcases hWorld.find_yul hFindRecipient with
    ⟨evmRecipient, hFindEvmRecipient, _hRecipientRel⟩
  have hEvmParentNonempty : evm.isEmpty = false :=
    accountMap_isEmpty_false_of_find? hFindEvmRecipient
  have hEvmTransferNonempty :
      (evmCallTransfer evm source recipient value).isEmpty = false := by
    simpa [evmCallTransfer] using
      callTransferUnchecked_isEmpty_false_of_parent_false
        source recipient value hEvmParentNonempty
  have hYulTransferNonempty : yulAfter.isEmpty = false := by
    simpa [hEvmTransferNonempty] using
      hTransferRel.isEmpty_eq
  exact
    ⟨yulAfter, hTransfer, hYulTransferNonempty,
      hEvmTransferNonempty, hTransferRel⟩

theorem CompiledAccountMapRel.ordinaryCall_nondefault_transferCheckedFacts
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    {source recipient : EvmYul.AccountAddress}
    {value : EvmYul.UInt256}
    {yulRecipient : EvmYul.Account .Yul}
    (hFindRecipient : yul.find? recipient = some yulRecipient)
    (hCodeNondefault : yulRecipient.code ≠ default)
    (hEnough :
      value ≤ (evm.find? source |>.option ⟨0⟩ (·.balance))) :
    ∃ (yulAfter : EvmYul.AccountMap .Yul)
      (evmRecipient : EvmYul.Account .EVM)
      (program : Program) (asm : Assembly.Program)
      (target : Assembly.TargetProgram),
      EvmYul.Yul.callTransferAccountMap? yul source recipient value =
          some yulAfter ∧
        yulAfter.isEmpty = false ∧
        (evmCallTransfer evm source recipient value).isEmpty = false ∧
        CompiledAccountMapRel yulAfter
          (evmCallTransfer evm source recipient value) ∧
        evm.find? recipient = some evmRecipient ∧
        CompiledAccountRel yulRecipient evmRecipient ∧
        program.contract = yulRecipient.code ∧
        compileCheckedAssemblyTargetBytecodeResourcesSourceStatic? program =
          some (asm, target) ∧
        Program.RecursiveBridgeSourceStaticFacts program ∧
        Program.SourceAccepted program ∧
        Program.SourceCompileAccepted program ∧
        Program.compileChecked? program = some asm ∧
        Program.compileCheckedAssemblyTargetBytecode? program =
          some (asm, target) ∧
        _root_.EvmCompiler.Yul.Program.RecursiveBridgeCompileResources program ∧
        Assembly.Bytecode.TargetFitsDecodeWindow target ∧
        Assembly.Bytecode.JumpdestCorrect target ∧
        evmRecipient.code = Assembly.Bytecode.encodeTarget target := by
  rcases
      hWorld.callTransferAccountMap?_of_evm_enough_find_yul_nonempty
        hFindRecipient hEnough with
    ⟨yulAfter, hTransfer, hYulNonempty, hEvmNonempty, hTransferRel⟩
  rcases
      hWorld.checkedCodeResourcesSourceStatic_of_find_yul_ne_default
        hFindRecipient hCodeNondefault with
    ⟨evmRecipient, program, asm, target, hFindEvm, hAccount,
      hContract, hCompile, hStatic, hSourceAccepted,
      hSourceCompileAccepted, hCompileChecked, hBytecode, hResources,
      hDecode, hJumpdest, hBytes⟩
  exact
    ⟨yulAfter, evmRecipient, program, asm, target, hTransfer,
      hYulNonempty, hEvmNonempty, hTransferRel, hFindEvm, hAccount,
      hContract, hCompile, hStatic, hSourceAccepted,
      hSourceCompileAccepted, hCompileChecked, hBytecode, hResources,
      hDecode, hJumpdest, hBytes⟩

theorem CompiledAccountMapRel.of_empty_child_to_empty_parent
    {yulChild : EvmYul.AccountMap .Yul}
    {evmChild evmParent : EvmYul.AccountMap .EVM}
    (hChild : CompiledAccountMapRel yulChild evmChild)
    (hChildEmpty : evmChild.isEmpty = true)
    (hParentEmpty : evmParent.isEmpty = true) :
    CompiledAccountMapRel yulChild evmParent := by
  refine
    { yul_to_evm := ?_
      evm_to_yul := ?_ }
  · intro addr yulAccount hFindYul
    rcases hChild.find_yul hFindYul with
      ⟨evmAccount, hFindEvmChild, _hAccount⟩
    have hNonempty :=
      accountMap_isEmpty_false_of_find? hFindEvmChild
    simp [hChildEmpty] at hNonempty
  · intro addr evmAccount hFindEvmParent
    have hNonempty :=
      accountMap_isEmpty_false_of_find? hFindEvmParent
    simp [hParentEmpty] at hNonempty

theorem CompiledAccountMapRel.callTransferAccountMap?_of_evm_enough_merge
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    {source recipient : EvmYul.AccountAddress}
    {value : EvmYul.UInt256}
    (hEnough :
      value ≤ (evm.find? source |>.option ⟨0⟩ (·.balance))) :
    ∃ yulAfter,
      EvmYul.Yul.callTransferAccountMap? yul source recipient value =
          some yulAfter ∧
        CompiledAccountMapRel yulAfter
          (if (evmCallTransfer evm source recipient value).isEmpty then
            evm
          else
            evmCallTransfer evm source recipient value) := by
  rcases
      hWorld.callTransferAccountMap?_of_evm_enough
        (source := source) (recipient := recipient) hEnough with
    ⟨yulAfter, hTransfer, hTransferRel⟩
  refine ⟨yulAfter, hTransfer, ?_⟩
  cases hEmpty :
      (evmCallTransfer evm source recipient value).isEmpty
  · simpa [hEmpty] using hTransferRel
  · have hParentEmpty : evm.isEmpty = true := by
      cases hParent : evm.isEmpty
      · have hTransferNonempty :
            (evmCallTransfer evm source recipient value).isEmpty = false := by
          simpa [evmCallTransfer] using
            callTransferUnchecked_isEmpty_false_of_parent_false
              source recipient value hParent
        simp [hEmpty] at hTransferNonempty
      · rfl
    simp
    exact
      CompiledAccountMapRel.of_empty_child_to_empty_parent
        hTransferRel hEmpty hParentEmpty

theorem CompiledAccountMapRel.callTransferAccountMap?_none_of_evm_not_enough
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    {source recipient : EvmYul.AccountAddress}
    {value : EvmYul.UInt256}
    (hNotEnough :
      ¬ value ≤ (evm.find? source |>.option ⟨0⟩ (·.balance))) :
    EvmYul.Yul.callTransferAccountMap? yul source recipient value = none := by
  have hYulNotEnough :
      ¬ value ≤ (yul.find? source |>.option ⟨0⟩ (·.balance)) := by
    intro hYulEnough
    exact hNotEnough
      ((hWorld.callTransferEnough_iff source value).mp hYulEnough)
  simp [EvmYul.Yul.callTransferAccountMap?, hYulNotEnough]

theorem CompiledAccountMapRel.callTransferAccountMap?_none_iff_evm_not_enough
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    {source recipient : EvmYul.AccountAddress}
    {value : EvmYul.UInt256} :
    EvmYul.Yul.callTransferAccountMap? yul source recipient value = none ↔
      ¬ value ≤ (evm.find? source |>.option ⟨0⟩ (·.balance)) := by
  constructor
  · intro hNone hEnough
    rcases hWorld.callTransferAccountMap?_of_evm_enough
        (source := source) (recipient := recipient) hEnough with
      ⟨yulAfter, hSome, _hRel⟩
    simp [hNone] at hSome
  · intro hNotEnough
    exact hWorld.callTransferAccountMap?_none_of_evm_not_enough hNotEnough

theorem CompiledAccountMapRel.selfbalance
    {yul : EvmYul.State .Yul} {evm : EvmYul.State .EVM}
    (hWorld : CompiledAccountMapRel yul.accountMap evm.accountMap)
    (hOwner : yul.executionEnv.codeOwner = evm.executionEnv.codeOwner) :
    EvmYul.State.selfbalance yul = EvmYul.State.selfbalance evm := by
  unfold EvmYul.State.selfbalance
  rw [hOwner]
  exact hWorld.balance_at evm.executionEnv.codeOwner

theorem CompiledAccountMapRel.balance
    {yul : EvmYul.State .Yul} {evm : EvmYul.State .EVM}
    {address : Word}
    (hWorld : CompiledAccountMapRel yul.accountMap evm.accountMap) :
    (EvmYul.State.balance yul address).2 =
      (EvmYul.State.balance evm address).2 := by
  simpa [EvmYul.State.balance] using
    hWorld.balance_at (EvmYul.AccountAddress.ofUInt256 address)

theorem CompiledAccountMapRel.sload
    {yul : EvmYul.State .Yul} {evm : EvmYul.State .EVM}
    {slot : Word}
    (hWorld : CompiledAccountMapRel yul.accountMap evm.accountMap)
    (hOwner : yul.executionEnv.codeOwner = evm.executionEnv.codeOwner) :
    (EvmYul.State.sload yul slot).2 =
      (EvmYul.State.sload evm slot).2 := by
  unfold EvmYul.State.sload EvmYul.State.lookupAccount
  rw [hOwner]
  exact hWorld.storage_at evm.executionEnv.codeOwner slot

theorem CompiledAccountMapRel.sstore_accountMap
    {yul : EvmYul.State .Yul} {evm : EvmYul.State .EVM}
    {slot value : Word}
    (hWorld : CompiledAccountMapRel yul.accountMap evm.accountMap)
    (_hSigma : yul.σ₀ = evm.σ₀)
    (hOwner : yul.executionEnv.codeOwner = evm.executionEnv.codeOwner)
    (_hSubstate : yul.substate = evm.substate) :
    CompiledAccountMapRel
      (EvmYul.State.sstore yul slot value).accountMap
      (EvmYul.State.sstore evm slot value).accountMap := by
  unfold EvmYul.State.sstore EvmYul.State.lookupAccount
    EvmYul.State.setAccount EvmYul.State.addAccessedStorageKey
  rw [hOwner]
  cases hYul : yul.accountMap.find? evm.executionEnv.codeOwner with
  | none =>
      have hEvm := hWorld.not_find_evm_of_not_find_yul hYul
      simp [Option.option, hYul, hEvm]
      exact hWorld
  | some yulAccount =>
      rcases hWorld.find_yul hYul with ⟨evmAccount, hEvm, hAccount⟩
      simp [Option.option, hYul, hEvm]
      exact hWorld.insert evm.executionEnv.codeOwner
        (hAccount.update_storage slot value)

theorem CompiledAccountMapRel.sstore_substate
    {yul : EvmYul.State .Yul} {evm : EvmYul.State .EVM}
    {slot value : Word}
    (hWorld : CompiledAccountMapRel yul.accountMap evm.accountMap)
    (hSigma : yul.σ₀ = evm.σ₀)
    (hOwner : yul.executionEnv.codeOwner = evm.executionEnv.codeOwner)
    (hSubstate : yul.substate = evm.substate) :
    (EvmYul.State.sstore yul slot value).substate =
      (EvmYul.State.sstore evm slot value).substate := by
  unfold EvmYul.State.sstore EvmYul.State.lookupAccount
    EvmYul.State.setAccount EvmYul.State.addAccessedStorageKey
  rw [hOwner]
  cases hYul : yul.accountMap.find? evm.executionEnv.codeOwner with
  | none =>
      have hEvm := hWorld.not_find_evm_of_not_find_yul hYul
      simp [Option.option, hYul, hEvm, hSubstate]
  | some yulAccount =>
      rcases hWorld.find_yul hYul with ⟨evmAccount, hEvm, hAccount⟩
      simp [Option.option, Batteries.RBMap.find!, hYul, hEvm, hSigma,
        hSubstate, hAccount.storage]

theorem CompiledAccountMapRel.tload
    {yul : EvmYul.State .Yul} {evm : EvmYul.State .EVM}
    {slot : Word}
    (hWorld : CompiledAccountMapRel yul.accountMap evm.accountMap)
    (hOwner : yul.executionEnv.codeOwner = evm.executionEnv.codeOwner) :
    (EvmYul.State.tload yul slot).2 =
      (EvmYul.State.tload evm slot).2 := by
  unfold EvmYul.State.tload EvmYul.State.lookupAccount
  rw [hOwner]
  exact hWorld.transientStorage_at evm.executionEnv.codeOwner slot

theorem CompiledAccountMapRel.tstore_accountMap
    {yul : EvmYul.State .Yul} {evm : EvmYul.State .EVM}
    {slot value : Word}
    (hWorld : CompiledAccountMapRel yul.accountMap evm.accountMap)
    (hOwner : yul.executionEnv.codeOwner = evm.executionEnv.codeOwner) :
    CompiledAccountMapRel
      (EvmYul.State.tstore yul slot value).accountMap
      (EvmYul.State.tstore evm slot value).accountMap := by
  unfold EvmYul.State.tstore EvmYul.State.lookupAccount EvmYul.State.updateAccount
  rw [hOwner]
  cases hYul : yul.accountMap.find? evm.executionEnv.codeOwner with
  | none =>
      have hEvm := hWorld.not_find_evm_of_not_find_yul hYul
      simp [Option.option, hYul, hEvm]
      exact hWorld
  | some yulAccount =>
      rcases hWorld.find_yul hYul with ⟨evmAccount, hEvm, hAccount⟩
      simp [Option.option, hYul, hEvm]
      exact hWorld.insert evm.executionEnv.codeOwner
        (hAccount.update_transientStorage slot value)

noncomputable def stateRelConfig
    (varStackRel : Reference.VarStackRel)
    (terminalRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop)
    (revertRel : Reference.State → EVMState → Prop)
    (gasAvailableRel : Word → Word → Prop)
    (gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm)
    (totalGasRel : Nat → Nat → Prop) :
    Reference.StateRelConfig where
  accountMapRel := accountMapRel
  selfbalanceRel := by
    intro yul evm hWorld hOwner
    exact hWorld.selfbalance hOwner
  balanceRel := by
    intro yul evm address hWorld
    exact hWorld.balance
  sloadRel := by
    intro yul evm slot hWorld hOwner
    exact hWorld.sload hOwner
  sstoreAccountMapRel := by
    intro yul evm slot value hWorld hSigma hOwner hSubstate
    exact hWorld.sstore_accountMap hSigma hOwner hSubstate
  sstoreSubstateRel := by
    intro yul evm slot value hWorld hSigma hOwner hSubstate
    exact hWorld.sstore_substate hSigma hOwner hSubstate
  tloadRel := by
    intro yul evm slot hWorld hOwner
    exact hWorld.tload hOwner
  tstoreAccountMapRel := by
    intro yul evm slot value hWorld hOwner
    exact hWorld.tstore_accountMap hOwner
  codeRel := codeImageRel
  varStackRel := varStackRel
  terminalRel := terminalRel
  revertRel := revertRel
  gasAvailableRel := gasAvailableRel
  gasValueRel := gasValueRel
  totalGasRel := totalGasRel

theorem executionEnvRel_callFrame
    {cfg : Reference.StateRelConfig}
    {yulCode : AstContract} {evmCode : ByteArray}
    (hCode : cfg.codeRel yulCode evmCode)
    (codeOwner sender source : EvmYul.AccountAddress)
    (weiValue : EvmYul.UInt256)
    (calldata : ByteArray)
    (gasPrice depth : Nat)
      (header : EvmYul.BlockHeader)
      (perm : Bool)
      (blobVersionedHashes : List ByteArray)
      (yulCodeBytes evmCodeBytes : ByteArray)
      (hCodeBytes : yulCodeBytes = evmCode) :
    Reference.ExecutionEnvRel cfg
      { codeOwner := codeOwner
        sender := sender
        source := source
        weiValue := weiValue
        calldata := calldata
        code := yulCode
        gasPrice := gasPrice
        header := header
        depth := depth
        perm := perm
        blobVersionedHashes := blobVersionedHashes
        codeBytes := yulCodeBytes }
      { codeOwner := codeOwner
        sender := sender
        source := source
        weiValue := weiValue
        calldata := calldata
        code := evmCode
        gasPrice := gasPrice
        header := header
        depth := depth
        perm := perm
        blobVersionedHashes := blobVersionedHashes
        codeBytes := evmCodeBytes } := by
  exact
    { codeOwner := rfl
      sender := rfl
      source := rfl
      weiValue := rfl
      calldata := rfl
      code := hCode
      gasPrice := rfl
      header := rfl
      depth := rfl
      perm := rfl
      blobVersionedHashes := rfl
      codeBytes := hCodeBytes }

theorem CompiledToExecuteRel.executionEnvRel_callFrame
    {cfg : Reference.StateRelConfig}
    {yulExec : EvmYul.ToExecute .Yul}
    {evmExec : EvmYul.ToExecute .EVM}
    (hExec : CompiledToExecuteRel yulExec evmExec)
    (hCodeRel :
      ∀ {yulCode : AstContract} {evmCode : ByteArray},
        CompiledCodeRel yulCode evmCode →
          cfg.codeRel yulCode evmCode)
    (codeOwner sender source : EvmYul.AccountAddress)
    (weiValue : EvmYul.UInt256)
    (calldata : ByteArray)
    (gasPrice depth : Nat)
      (header : EvmYul.BlockHeader)
      (perm : Bool)
      (blobVersionedHashes : List ByteArray)
      (yulCodeBytes evmCodeBytes : ByteArray)
      (hCodeBytes :
        yulCodeBytes =
          match evmExec with
          | EvmYul.ToExecute.Precompiled _ => default
          | EvmYul.ToExecute.Code evmCode => evmCode) :
    Reference.ExecutionEnvRel cfg
      { codeOwner := codeOwner
        sender := sender
        source := source
        weiValue := weiValue
        calldata := calldata
        code :=
          match yulExec with
          | EvmYul.ToExecute.Precompiled _ => default
          | EvmYul.ToExecute.Code yulCode => yulCode
        gasPrice := gasPrice
        header := header
        depth := depth
        perm := perm
        blobVersionedHashes := blobVersionedHashes
        codeBytes := yulCodeBytes }
      { codeOwner := codeOwner
        sender := sender
        source := source
        weiValue := weiValue
        calldata := calldata
        code :=
          match evmExec with
          | EvmYul.ToExecute.Precompiled _ => default
          | EvmYul.ToExecute.Code evmCode => evmCode
        gasPrice := gasPrice
        header := header
        depth := depth
        perm := perm
        blobVersionedHashes := blobVersionedHashes
        codeBytes := evmCodeBytes } := by
  cases hExec with
  | precompiled precompiled =>
        simpa using
          World.executionEnvRel_callFrame
            (hCodeRel CompiledCodeRel.empty)
            codeOwner sender source weiValue calldata gasPrice depth
            header perm blobVersionedHashes yulCodeBytes evmCodeBytes
            hCodeBytes
  | code hCode =>
        simpa using
          World.executionEnvRel_callFrame
            (hCodeRel hCode)
            codeOwner sender source weiValue calldata gasPrice depth
            header perm blobVersionedHashes yulCodeBytes evmCodeBytes
            hCodeBytes

theorem chainStateRel_addAccessedAccount
    {cfg : Reference.StateRelConfig}
    {yul : EvmYul.State .Yul} {evm : EvmYul.State .EVM}
    (hChain : Reference.ChainStateRel cfg yul evm)
    (addr : EvmYul.AccountAddress) :
    Reference.ChainStateRel cfg
      (EvmYul.State.addAccessedAccount yul addr)
      (EvmYul.State.addAccessedAccount evm addr) := by
  rcases hChain with
    ⟨hAccountMap, hSigma, hTotal, hReceipts, hSubstate, hEnv,
      hBlocks, hGenesis, hCreated⟩
  constructor
  · simpa [EvmYul.State.addAccessedAccount] using hAccountMap
  · simpa [EvmYul.State.addAccessedAccount] using hSigma
  · simpa [EvmYul.State.addAccessedAccount] using hTotal
  · simpa [EvmYul.State.addAccessedAccount] using hReceipts
  · simp [EvmYul.State.addAccessedAccount, EvmYul.Substate.addAccessedAccount,
      hSubstate]
  · simpa [EvmYul.State.addAccessedAccount] using hEnv
  · simpa [EvmYul.State.addAccessedAccount] using hBlocks
  · simpa [EvmYul.State.addAccessedAccount] using hGenesis
  · simpa [EvmYul.State.addAccessedAccount] using hCreated

theorem sharedStateRel_addAccessedAccount
    {cfg : Reference.StateRelConfig}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.SharedState .EVM}
    (hShared : Reference.SharedStateRel cfg yul evm)
    (addr : EvmYul.AccountAddress) :
    Reference.SharedStateRel cfg
      { yul with toState := EvmYul.State.addAccessedAccount yul.toState addr }
      { evm with toState := EvmYul.State.addAccessedAccount evm.toState addr } := by
  rcases hShared with ⟨hChain, hMachine⟩
  constructor
  · exact chainStateRel_addAccessedAccount hChain addr
  · simpa [EvmYul.State.addAccessedAccount] using hMachine

theorem machineStateRel_finishExternalCall
    {cfg : Reference.StateRelConfig}
    {yul evm : EvmYul.MachineState}
    (hMachine : Reference.MachineStateRel cfg yul evm)
    (returnData : ByteArray)
    (inOffset inSize outOffset outSize : EvmYul.UInt256) :
    Reference.MachineStateRel cfg
      (yul.finishExternalCall returnData inOffset inSize outOffset outSize)
      (evm.finishExternalCall returnData inOffset inSize outOffset outSize) := by
  rcases hMachine with ⟨hGas, hActive, hMemory, _hReturn, _hHReturn⟩
  constructor
  · simpa [EvmYul.MachineState.finishExternalCall, EvmYul.writeBytes] using
      hGas
  · simp [EvmYul.MachineState.finishExternalCall, EvmYul.writeBytes,
      hActive]
  · simp [EvmYul.MachineState.finishExternalCall, EvmYul.writeBytes,
      hMemory]
  · simp [EvmYul.MachineState.finishExternalCall]
  · simp [EvmYul.MachineState.finishExternalCall]

theorem machineStateRel_finishExternalCallWithTargetGas
    {cfg : Reference.StateRelConfig}
    {yul evm : EvmYul.MachineState}
    (hMachine : Reference.MachineStateRel cfg yul evm)
    {targetGas : EvmYul.UInt256}
    (returnData : ByteArray)
    (inOffset inSize outOffset outSize : EvmYul.UInt256)
    (hGas :
      cfg.gasAvailableRel
        (yul.finishExternalCall returnData inOffset inSize
          outOffset outSize).gasAvailable
        targetGas) :
    Reference.MachineStateRel cfg
      (yul.finishExternalCall returnData inOffset inSize outOffset outSize)
      { evm.finishExternalCall returnData inOffset inSize outOffset outSize with
        gasAvailable := targetGas } := by
  rcases hMachine with ⟨_hGas, hActive, hMemory, _hReturn, _hHReturn⟩
  constructor
  · exact hGas
  · simp [EvmYul.MachineState.finishExternalCall, EvmYul.writeBytes,
      hActive]
  · simp [EvmYul.MachineState.finishExternalCall, EvmYul.writeBytes,
      hMemory]
  · simp [EvmYul.MachineState.finishExternalCall]
  · simp [EvmYul.MachineState.finishExternalCall]

theorem machineStateRel_gasAvailable_eq
    {cfg : Reference.StateRelConfig}
    {yul evm : EvmYul.MachineState}
    (hMachine : Reference.MachineStateRel cfg yul evm) :
    yul.gasAvailable = evm.gasAvailable := by
  simpa [EvmYul.MachineState.gas] using
    cfg.gasValueRel hMachine.gasAvailable

theorem machineStateRel_freshExternalCall
    {cfg : Reference.StateRelConfig}
    {yulGas evmGas : EvmYul.UInt256}
    (hGas : cfg.gasAvailableRel yulGas evmGas) :
    Reference.MachineStateRel cfg
      (EvmYul.MachineState.freshExternalCall yulGas)
      (EvmYul.MachineState.freshExternalCall evmGas) := by
  constructor
  · simpa [EvmYul.MachineState.freshExternalCall] using hGas
  · simp [EvmYul.MachineState.freshExternalCall]
  · simp [EvmYul.MachineState.freshExternalCall]
  · simp [EvmYul.MachineState.freshExternalCall]
  · simp [EvmYul.MachineState.freshExternalCall]

theorem sharedStateRel_freshExternalCall
    {cfg : Reference.StateRelConfig}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.SharedState .EVM}
    (hShared : Reference.SharedStateRel cfg yul evm)
    {yulGas evmGas : EvmYul.UInt256}
    (hGas : cfg.gasAvailableRel yulGas evmGas) :
    Reference.SharedStateRel cfg
      { yul with
        toMachineState := EvmYul.MachineState.freshExternalCall yulGas }
      { evm with
        toMachineState := EvmYul.MachineState.freshExternalCall evmGas } := by
  rcases hShared with ⟨hChain, _hMachine⟩
  exact ⟨hChain, machineStateRel_freshExternalCall hGas⟩

theorem sharedStateRel_finishExternalCall
    {cfg : Reference.StateRelConfig}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.SharedState .EVM}
    (hShared : Reference.SharedStateRel cfg yul evm)
    (returnData : ByteArray)
    (inOffset inSize outOffset outSize : EvmYul.UInt256) :
    Reference.SharedStateRel cfg
      { yul with
        toMachineState :=
          yul.toMachineState.finishExternalCall returnData
            inOffset inSize outOffset outSize }
      { evm with
        toMachineState :=
          evm.toMachineState.finishExternalCall returnData
            inOffset inSize outOffset outSize } := by
  rcases hShared with ⟨hChain, hMachine⟩
  exact
    ⟨hChain,
      machineStateRel_finishExternalCall hMachine returnData
        inOffset inSize outOffset outSize⟩

theorem sharedStateRel_finishExternalCallWithTargetGas
    {cfg : Reference.StateRelConfig}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.SharedState .EVM}
    (hShared : Reference.SharedStateRel cfg yul evm)
    {targetGas : EvmYul.UInt256}
    (returnData : ByteArray)
    (inOffset inSize outOffset outSize : EvmYul.UInt256)
    (hGas :
      cfg.gasAvailableRel
        (yul.toMachineState.finishExternalCall returnData
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    Reference.SharedStateRel cfg
      { yul with
        toMachineState :=
          yul.toMachineState.finishExternalCall returnData
            inOffset inSize outOffset outSize }
      { evm with
        toMachineState :=
          { evm.toMachineState.finishExternalCall returnData
              inOffset inSize outOffset outSize with
            gasAvailable := targetGas } } := by
  rcases hShared with ⟨hChain, hMachine⟩
  exact
    ⟨hChain,
      machineStateRel_finishExternalCallWithTargetGas hMachine
        returnData inOffset inSize outOffset outSize hGas⟩

theorem sharedStateRel_finishExternalCallAfterAccessWithTargetGas
    {cfg : Reference.StateRelConfig}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.SharedState .EVM}
    (hShared : Reference.SharedStateRel cfg yul evm)
    (addr : EvmYul.AccountAddress)
    {targetGas : EvmYul.UInt256}
    (returnData : ByteArray)
    (inOffset inSize outOffset outSize : EvmYul.UInt256)
    (hGas :
      cfg.gasAvailableRel
        (yul.toMachineState.finishExternalCall returnData
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    Reference.SharedStateRel cfg
      { yul with
        toState := EvmYul.State.addAccessedAccount yul.toState addr
        toMachineState :=
          yul.toMachineState.finishExternalCall returnData
            inOffset inSize outOffset outSize }
      { evm with
        toState := EvmYul.State.addAccessedAccount evm.toState addr
        toMachineState :=
          { evm.toMachineState.finishExternalCall returnData
              inOffset inSize outOffset outSize with
            gasAvailable := targetGas } } := by
  simpa using
    sharedStateRel_finishExternalCallWithTargetGas
      (sharedStateRel_addAccessedAccount hShared addr)
      returnData inOffset inSize outOffset outSize hGas

theorem sharedStateRel_finishExternalCallWithWorld
    {cfg : Reference.StateRelConfig}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.SharedState .EVM}
    (hShared : Reference.SharedStateRel cfg yul evm)
    {yulAccountMap : EvmYul.AccountMap .Yul}
    {evmAccountMap : EvmYul.AccountMap .EVM}
    {yulSubstate evmSubstate : EvmYul.Substate}
    {yulCreated evmCreated : Batteries.RBSet EvmYul.AccountAddress compare}
    (hAccountMap : cfg.accountMapRel yulAccountMap evmAccountMap)
    (hSubstate : yulSubstate = evmSubstate)
    (hCreated : yulCreated = evmCreated)
    (returnData : ByteArray)
    (inOffset inSize outOffset outSize : EvmYul.UInt256) :
    Reference.SharedStateRel cfg
      { yul with
        toMachineState :=
          yul.toMachineState.finishExternalCall returnData
            inOffset inSize outOffset outSize
        accountMap := yulAccountMap
        substate := yulSubstate
        createdAccounts := yulCreated }
      { evm with
        toMachineState :=
          evm.toMachineState.finishExternalCall returnData
            inOffset inSize outOffset outSize
        accountMap := evmAccountMap
        substate := evmSubstate
        createdAccounts := evmCreated } := by
  rcases hShared with ⟨hChain, hMachine⟩
  rcases hChain with
    ⟨_hAccountMap, hSigma, hTotal, hReceipts, _hSubstate, hEnv,
      hBlocks, hGenesis, _hCreated⟩
  constructor
  · constructor
    · exact hAccountMap
    · simpa using hSigma
    · simpa using hTotal
    · simpa using hReceipts
    · exact hSubstate
    · simpa using hEnv
    · simpa using hBlocks
    · simpa using hGenesis
    · exact hCreated
  · exact
      machineStateRel_finishExternalCall hMachine returnData
        inOffset inSize outOffset outSize

theorem sharedStateRel_finishExternalCallWithWorldAndTargetGas
    {cfg : Reference.StateRelConfig}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.SharedState .EVM}
    (hShared : Reference.SharedStateRel cfg yul evm)
    {yulAccountMap : EvmYul.AccountMap .Yul}
    {evmAccountMap : EvmYul.AccountMap .EVM}
    {yulSubstate evmSubstate : EvmYul.Substate}
    {yulCreated evmCreated : Batteries.RBSet EvmYul.AccountAddress compare}
    {targetGas : EvmYul.UInt256}
    (hAccountMap : cfg.accountMapRel yulAccountMap evmAccountMap)
    (hSubstate : yulSubstate = evmSubstate)
    (hCreated : yulCreated = evmCreated)
    (returnData : ByteArray)
    (inOffset inSize outOffset outSize : EvmYul.UInt256)
    (hGas :
      cfg.gasAvailableRel
        (yul.toMachineState.finishExternalCall returnData
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    Reference.SharedStateRel cfg
      { yul with
        toMachineState :=
          yul.toMachineState.finishExternalCall returnData
            inOffset inSize outOffset outSize
        accountMap := yulAccountMap
        substate := yulSubstate
        createdAccounts := yulCreated }
      { evm with
        toMachineState :=
          { evm.toMachineState.finishExternalCall returnData
              inOffset inSize outOffset outSize with
            gasAvailable := targetGas }
        accountMap := evmAccountMap
        substate := evmSubstate
        createdAccounts := evmCreated } := by
  rcases hShared with ⟨hChain, hMachine⟩
  rcases hChain with
    ⟨_hAccountMap, hSigma, hTotal, hReceipts, _hSubstate, hEnv,
      hBlocks, hGenesis, _hCreated⟩
  constructor
  · exact
      { accountMap := hAccountMap
        σ₀ := by simpa using hSigma
        totalGasUsedInBlock := by simpa using hTotal
        transactionReceipts := by simpa using hReceipts
        substate := hSubstate
        executionEnv := by simpa using hEnv
        blocks := by simpa using hBlocks
        genesisBlockHeader := by simpa using hGenesis
        createdAccounts := hCreated }
  · exact
      machineStateRel_finishExternalCallWithTargetGas hMachine
        returnData inOffset inSize outOffset outSize hGas

theorem sharedStateRel_finishExternalCallAfterAccessWithWorldAndTargetGas
    {cfg : Reference.StateRelConfig}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.SharedState .EVM}
    (hShared : Reference.SharedStateRel cfg yul evm)
    (addr : EvmYul.AccountAddress)
    {yulAccountMap : EvmYul.AccountMap .Yul}
    {evmAccountMap : EvmYul.AccountMap .EVM}
    {yulCreated evmCreated : Batteries.RBSet EvmYul.AccountAddress compare}
    {targetGas : EvmYul.UInt256}
    (hAccountMap : cfg.accountMapRel yulAccountMap evmAccountMap)
    (hCreated : yulCreated = evmCreated)
    (returnData : ByteArray)
    (inOffset inSize outOffset outSize : EvmYul.UInt256)
    (hGas :
      cfg.gasAvailableRel
        (yul.toMachineState.finishExternalCall returnData
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    Reference.SharedStateRel cfg
      { yul with
        toMachineState :=
          yul.toMachineState.finishExternalCall returnData
            inOffset inSize outOffset outSize
        accountMap := yulAccountMap
        substate := (EvmYul.State.addAccessedAccount yul.toState addr).substate
        createdAccounts := yulCreated }
      { evm with
        toMachineState :=
          { evm.toMachineState.finishExternalCall returnData
              inOffset inSize outOffset outSize with
            gasAvailable := targetGas }
        accountMap := evmAccountMap
        substate := (EvmYul.State.addAccessedAccount evm.toState addr).substate
        createdAccounts := evmCreated } := by
  have hSubstate :
      (EvmYul.State.addAccessedAccount yul.toState addr).substate =
        (EvmYul.State.addAccessedAccount evm.toState addr).substate := by
    rcases hShared with ⟨hChain, _hMachine⟩
    rcases hChain with
      ⟨_hAccountMap, _hSigma, _hTotal, _hReceipts, hSubstate,
        _hEnv, _hBlocks, _hGenesis, _hCreated⟩
    simp [EvmYul.State.addAccessedAccount, EvmYul.Substate.addAccessedAccount,
      hSubstate]
  simpa [EvmYul.State.addAccessedAccount] using
    sharedStateRel_finishExternalCallWithWorldAndTargetGas
      (sharedStateRel_addAccessedAccount hShared addr)
      hAccountMap hSubstate hCreated returnData
      inOffset inSize outOffset outSize hGas

theorem buildContractCallEmptyReturnState_none_rel
    {cfg : Reference.StateRelConfig}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.SharedState .EVM}
    (hShared : Reference.SharedStateRel cfg yul evm)
    (store : EvmYul.Yul.VarStore)
    {targetGas : EvmYul.UInt256}
    (inOffset inSize outOffset outSize value : EvmYul.UInt256)
    (hGas :
      cfg.gasAvailableRel
        (yul.toMachineState.finishExternalCall ByteArray.empty
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    ∃ yulAfter,
      EvmYul.Yul.buildContractCallEmptyReturnState
          (.Ok yul store) none
          inOffset inSize outOffset outSize value =
        .ok (.Ok yulAfter store, [value]) ∧
      Reference.SharedStateRel cfg yulAfter
        { evm with
          toMachineState :=
            { evm.toMachineState.finishExternalCall ByteArray.empty
                inOffset inSize outOffset outSize with
              gasAvailable := targetGas } } := by
  refine
    ⟨{ yul with
        toMachineState :=
          yul.toMachineState.finishExternalCall ByteArray.empty
            inOffset inSize outOffset outSize },
      ?_, ?_⟩
  · simp [EvmYul.Yul.buildContractCallEmptyReturnState,
      EvmYul.Yul.State.toSharedState, EvmYul.Yul.State.toMachineState]
  · exact
      sharedStateRel_finishExternalCallWithTargetGas hShared
        ByteArray.empty inOffset inSize outOffset outSize hGas

theorem buildContractCallEmptyReturnState_afterAccess_some_rel
    {cfg : Reference.StateRelConfig}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.SharedState .EVM}
    (hShared : Reference.SharedStateRel cfg yul evm)
    (store : EvmYul.Yul.VarStore)
    (addr : EvmYul.AccountAddress)
    {yulAccountMap : EvmYul.AccountMap .Yul}
    {evmAccountMap : EvmYul.AccountMap .EVM}
    {targetGas : EvmYul.UInt256}
    (hAccountMap : cfg.accountMapRel yulAccountMap evmAccountMap)
    (inOffset inSize outOffset outSize value : EvmYul.UInt256)
    (hGas :
      cfg.gasAvailableRel
        (yul.toMachineState.finishExternalCall ByteArray.empty
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    ∃ yulAfter,
      EvmYul.Yul.buildContractCallEmptyReturnState
          (EvmYul.Yul.addAccessedAccount
            (.Ok yul store) addr)
          (some yulAccountMap)
          inOffset inSize outOffset outSize value =
        .ok (.Ok yulAfter store, [value]) ∧
      Reference.SharedStateRel cfg yulAfter
        { evm with
          toMachineState :=
            { evm.toMachineState.finishExternalCall ByteArray.empty
                inOffset inSize outOffset outSize with
              gasAvailable := targetGas }
          accountMap := evmAccountMap
          substate := (EvmYul.State.addAccessedAccount evm.toState addr).substate } := by
  have hCreated : yul.createdAccounts = evm.createdAccounts := by
    rcases hShared with ⟨hChain, _hMachine⟩
    exact hChain.createdAccounts
  refine
    ⟨{ yul with
        toMachineState :=
          yul.toMachineState.finishExternalCall ByteArray.empty
            inOffset inSize outOffset outSize
        accountMap := yulAccountMap
        substate := (EvmYul.State.addAccessedAccount yul.toState addr).substate },
      ?_, ?_⟩
  · simp [EvmYul.Yul.buildContractCallEmptyReturnState,
      EvmYul.Yul.addAccessedAccount, EvmYul.Yul.State.setState,
      EvmYul.Yul.State.toState, EvmYul.Yul.State.toSharedState,
      EvmYul.Yul.State.toMachineState, EvmYul.State.addAccessedAccount]
  · simpa [EvmYul.State.addAccessedAccount] using
      sharedStateRel_finishExternalCallAfterAccessWithWorldAndTargetGas
        hShared addr hAccountMap hCreated ByteArray.empty
        inOffset inSize outOffset outSize hGas

theorem buildContractCallEmptyReturnState_afterAccess_none_rel
    {cfg : Reference.StateRelConfig}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.SharedState .EVM}
    (hShared : Reference.SharedStateRel cfg yul evm)
    (store : EvmYul.Yul.VarStore)
    (addr : EvmYul.AccountAddress)
    {targetGas : EvmYul.UInt256}
    (inOffset inSize outOffset outSize value : EvmYul.UInt256)
    (hGas :
      cfg.gasAvailableRel
        (yul.toMachineState.finishExternalCall ByteArray.empty
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    ∃ yulAfter,
      EvmYul.Yul.buildContractCallEmptyReturnState
          (EvmYul.Yul.addAccessedAccount
            (.Ok yul store) addr)
          none
          inOffset inSize outOffset outSize value =
        .ok (.Ok yulAfter store, [value]) ∧
      Reference.SharedStateRel cfg yulAfter
        { evm with
          toMachineState :=
            { evm.toMachineState.finishExternalCall ByteArray.empty
                inOffset inSize outOffset outSize with
              gasAvailable := targetGas }
          substate := (EvmYul.State.addAccessedAccount evm.toState addr).substate } := by
  refine
    ⟨{ yul with
        toMachineState :=
          yul.toMachineState.finishExternalCall ByteArray.empty
            inOffset inSize outOffset outSize
        substate := (EvmYul.State.addAccessedAccount yul.toState addr).substate },
      ?_, ?_⟩
  · simp [EvmYul.Yul.buildContractCallEmptyReturnState,
      EvmYul.Yul.addAccessedAccount, EvmYul.Yul.State.setState,
      EvmYul.Yul.State.toState, EvmYul.Yul.State.toSharedState,
      EvmYul.Yul.State.toMachineState, EvmYul.State.addAccessedAccount]
  · simpa [EvmYul.State.addAccessedAccount] using
      sharedStateRel_finishExternalCallAfterAccessWithTargetGas
        hShared addr ByteArray.empty inOffset inSize outOffset outSize hGas

theorem EVM_call_insufficientFunds_eq
    {fuel gasCost : Nat}
    {blobVersionedHashes : List ByteArray}
    {evm : EvmYul.EVM.State}
    {gas address value inOffset inSize outOffset outSize : EvmYul.UInt256}
    (hNotEnough :
      ¬ value ≤
        (evm.accountMap.find? evm.executionEnv.codeOwner |>.option ⟨0⟩
          (·.balance))) :
    let target := EvmYul.AccountAddress.ofUInt256 address
    let callGas :=
      EvmYul.EVM.Ccallgas target target value gas evm.accountMap
        evm.toMachineState evm.substate
    let charged : EvmYul.EVM.State :=
      { evm with gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
    let targetGas :=
      (charged.toMachineState.finishExternalCall ByteArray.empty
        inOffset inSize outOffset outSize).gasAvailable +
        EvmYul.UInt256.ofNat callGas
    EvmYul.EVM.call fuel.succ gasCost blobVersionedHashes gas
        (EvmYul.UInt256.ofNat evm.executionEnv.codeOwner) address address
        value value inOffset inSize outOffset outSize evm.executionEnv.perm
        evm =
      .ok (⟨0⟩,
        { charged with
          toMachineState :=
            { charged.toMachineState.finishExternalCall ByteArray.empty
                inOffset inSize outOffset outSize with
              gasAvailable := targetGas }
          substate :=
            (EvmYul.State.addAccessedAccount charged.toState target).substate }) := by
  simp [EvmYul.EVM.call, hNotEnough]

theorem call_insufficientFunds_emptyReturn_rel
    {cfg : Reference.StateRelConfig}
    {fuel gasCost : Nat}
    {blobVersionedHashes : List ByteArray}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.EVM.State}
    (hShared : Reference.SharedStateRel cfg yul evm.toSharedState)
    (hParentWorld : CompiledAccountMapRel yul.accountMap evm.accountMap)
    (store : EvmYul.Yul.VarStore)
    {gas address value inOffset inSize outOffset outSize : EvmYul.UInt256}
    (hNotEnough :
      ¬ value ≤
        (evm.accountMap.find? evm.executionEnv.codeOwner |>.option ⟨0⟩
          (·.balance)))
    (hGas :
      let target := EvmYul.AccountAddress.ofUInt256 address
      let callGas :=
        EvmYul.EVM.Ccallgas target target value gas evm.accountMap
          evm.toMachineState evm.substate
      let charged : EvmYul.EVM.State :=
        { evm with
          gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
      let targetGas :=
        (charged.toMachineState.finishExternalCall ByteArray.empty
          inOffset inSize outOffset outSize).gasAvailable +
          EvmYul.UInt256.ofNat callGas
      cfg.gasAvailableRel
        (yul.toMachineState.finishExternalCall ByteArray.empty
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    let target := EvmYul.AccountAddress.ofUInt256 address
    let callGas :=
      EvmYul.EVM.Ccallgas target target value gas evm.accountMap
        evm.toMachineState evm.substate
    let charged : EvmYul.EVM.State :=
      { evm with gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
    let targetGas :=
      (charged.toMachineState.finishExternalCall ByteArray.empty
        inOffset inSize outOffset outSize).gasAvailable +
        EvmYul.UInt256.ofNat callGas
    let evmAfter : EvmYul.EVM.State :=
      { charged with
        toMachineState :=
          { charged.toMachineState.finishExternalCall ByteArray.empty
              inOffset inSize outOffset outSize with
            gasAvailable := targetGas }
        substate :=
          (EvmYul.State.addAccessedAccount charged.toState target).substate }
    EvmYul.EVM.call fuel.succ gasCost blobVersionedHashes gas
        (EvmYul.UInt256.ofNat evm.executionEnv.codeOwner) address address
        value value inOffset inSize outOffset outSize evm.executionEnv.perm
        evm =
      .ok (⟨0⟩, evmAfter) ∧
      EvmYul.Yul.callTransferAccountMap? yul.accountMap
          yul.executionEnv.codeOwner target value =
        none ∧
      ∃ yulAfter,
        EvmYul.Yul.buildContractCallEmptyReturnState
            (EvmYul.Yul.addAccessedAccount (.Ok yul store) target)
            none inOffset inSize outOffset outSize ⟨0⟩ =
          .ok (.Ok yulAfter store, [⟨0⟩]) ∧
        Reference.SharedStateRel cfg yulAfter evmAfter.toSharedState := by
  dsimp at hGas ⊢
  constructor
  · exact EVM_call_insufficientFunds_eq hNotEnough
  · constructor
    · have hOwner :
        yul.executionEnv.codeOwner = evm.executionEnv.codeOwner := by
          rcases hShared with ⟨hChain, _hMachine⟩
          simpa using hChain.executionEnv.codeOwner
      exact
        hParentWorld.callTransferAccountMap?_none_of_evm_not_enough
          (source := yul.executionEnv.codeOwner)
          (recipient := EvmYul.AccountAddress.ofUInt256 address)
          (value := value)
          (by simpa [hOwner] using hNotEnough)
    · exact
        buildContractCallEmptyReturnState_afterAccess_none_rel
          hShared store (EvmYul.AccountAddress.ofUInt256 address)
          inOffset inSize outOffset outSize ⟨0⟩ hGas

theorem primCall_CALL_insufficientFunds_emptyReturn_rel
    {cfg : Reference.StateRelConfig}
    {fuel gasCost : Nat}
    {blobVersionedHashes : List ByteArray}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.EVM.State}
    (hShared : Reference.SharedStateRel cfg yul evm.toSharedState)
    (hParentWorld : CompiledAccountMapRel yul.accountMap evm.accountMap)
    (store : EvmYul.Yul.VarStore)
    {gas address value inOffset inSize outOffset outSize : EvmYul.UInt256}
    (hStaticAllowed :
      ¬ (¬ yul.executionEnv.perm ∧ value ≠ ⟨0⟩))
    (hNotEnough :
      ¬ value ≤
        (evm.accountMap.find? evm.executionEnv.codeOwner |>.option ⟨0⟩
          (·.balance)))
    (hGas :
      let target := EvmYul.AccountAddress.ofUInt256 address
      let callGas :=
        EvmYul.EVM.Ccallgas target target value gas evm.accountMap
          evm.toMachineState evm.substate
      let charged : EvmYul.EVM.State :=
        { evm with
          gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
      let targetGas :=
        (charged.toMachineState.finishExternalCall ByteArray.empty
          inOffset inSize outOffset outSize).gasAvailable +
          EvmYul.UInt256.ofNat callGas
      cfg.gasAvailableRel
        (yul.toMachineState.finishExternalCall ByteArray.empty
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    let target := EvmYul.AccountAddress.ofUInt256 address
    let callGas :=
      EvmYul.EVM.Ccallgas target target value gas evm.accountMap
        evm.toMachineState evm.substate
    let charged : EvmYul.EVM.State :=
      { evm with gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
    let targetGas :=
      (charged.toMachineState.finishExternalCall ByteArray.empty
        inOffset inSize outOffset outSize).gasAvailable +
        EvmYul.UInt256.ofNat callGas
    let evmAfter : EvmYul.EVM.State :=
      { charged with
        toMachineState :=
          { charged.toMachineState.finishExternalCall ByteArray.empty
              inOffset inSize outOffset outSize with
            gasAvailable := targetGas }
        substate :=
          (EvmYul.State.addAccessedAccount charged.toState target).substate }
    EvmYul.EVM.call fuel.succ gasCost blobVersionedHashes gas
        (EvmYul.UInt256.ofNat evm.executionEnv.codeOwner) address address
        value value inOffset inSize outOffset outSize evm.executionEnv.perm
        evm =
      .ok (⟨0⟩, evmAfter) ∧
      ∃ yulAfter,
        EvmYul.Yul.primCall fuel.succ (.Ok yul store) .CALL
            [gas, address, value, inOffset, inSize, outOffset, outSize] =
          .ok (.Ok yulAfter store, [⟨0⟩]) ∧
        Reference.SharedStateRel cfg yulAfter evmAfter.toSharedState := by
  dsimp at hGas ⊢
  rcases
      call_insufficientFunds_emptyReturn_rel hShared hParentWorld store
        hNotEnough hGas with
    ⟨hEvm, hTransfer, yulAfter, hBuild, hRel⟩
  refine ⟨hEvm, yulAfter, ?_, hRel⟩
  have hStaticAllowed' :
      ¬ (yul.executionEnv.perm = false ∧ ¬ value = ⟨0⟩) := by
    intro hStatic
    exact hStaticAllowed (by simpa using hStatic)
  simpa [EvmYul.Yul.primCall, hStaticAllowed', hTransfer,
    EvmYul.Yul.addAccessedAccount, EvmYul.Yul.State.sharedState,
    EvmYul.Yul.State.executionEnv, EvmYul.Yul.State.setState,
    EvmYul.Yul.State.toState, EvmYul.Yul.State.toSharedState,
    EvmYul.Yul.State.toMachineState] using hBuild

theorem EVM_call_depthLimit_eq
    {fuel gasCost : Nat}
    {blobVersionedHashes : List ByteArray}
    {evm : EvmYul.EVM.State}
    {gas address value inOffset inSize outOffset outSize : EvmYul.UInt256}
    (hEnough :
      value ≤
        (evm.accountMap.find? evm.executionEnv.codeOwner |>.option ⟨0⟩
          (·.balance)))
    (hDepthLimit : ¬ evm.executionEnv.depth < 1024) :
    let target := EvmYul.AccountAddress.ofUInt256 address
    let callGas :=
      EvmYul.EVM.Ccallgas target target value gas evm.accountMap
        evm.toMachineState evm.substate
    let charged : EvmYul.EVM.State :=
      { evm with gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
    let targetGas :=
      (charged.toMachineState.finishExternalCall ByteArray.empty
        inOffset inSize outOffset outSize).gasAvailable +
        EvmYul.UInt256.ofNat callGas
    EvmYul.EVM.call fuel.succ gasCost blobVersionedHashes gas
        (EvmYul.UInt256.ofNat evm.executionEnv.codeOwner) address address
        value value inOffset inSize outOffset outSize evm.executionEnv.perm
        evm =
      .ok (⟨0⟩,
        { charged with
          toMachineState :=
            { charged.toMachineState.finishExternalCall ByteArray.empty
                inOffset inSize outOffset outSize with
              gasAvailable := targetGas }
          substate :=
            (EvmYul.State.addAccessedAccount charged.toState target).substate }) := by
  simp [EvmYul.EVM.call, hEnough, hDepthLimit]

theorem call_depthLimit_emptyReturn_rel
    {cfg : Reference.StateRelConfig}
    {fuel gasCost : Nat}
    {blobVersionedHashes : List ByteArray}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.EVM.State}
    (hShared : Reference.SharedStateRel cfg yul evm.toSharedState)
    (hParentWorld : CompiledAccountMapRel yul.accountMap evm.accountMap)
    (store : EvmYul.Yul.VarStore)
    {gas address value inOffset inSize outOffset outSize : EvmYul.UInt256}
    (hEnough :
      value ≤
        (evm.accountMap.find? evm.executionEnv.codeOwner |>.option ⟨0⟩
          (·.balance)))
    (hDepthLimit : ¬ evm.executionEnv.depth < 1024)
    (hGas :
      let target := EvmYul.AccountAddress.ofUInt256 address
      let callGas :=
        EvmYul.EVM.Ccallgas target target value gas evm.accountMap
          evm.toMachineState evm.substate
      let charged : EvmYul.EVM.State :=
        { evm with
          gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
      let targetGas :=
        (charged.toMachineState.finishExternalCall ByteArray.empty
          inOffset inSize outOffset outSize).gasAvailable +
          EvmYul.UInt256.ofNat callGas
      cfg.gasAvailableRel
        (yul.toMachineState.finishExternalCall ByteArray.empty
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    let target := EvmYul.AccountAddress.ofUInt256 address
    let callGas :=
      EvmYul.EVM.Ccallgas target target value gas evm.accountMap
        evm.toMachineState evm.substate
    let charged : EvmYul.EVM.State :=
      { evm with gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
    let targetGas :=
      (charged.toMachineState.finishExternalCall ByteArray.empty
        inOffset inSize outOffset outSize).gasAvailable +
        EvmYul.UInt256.ofNat callGas
    let evmAfter : EvmYul.EVM.State :=
      { charged with
        toMachineState :=
          { charged.toMachineState.finishExternalCall ByteArray.empty
              inOffset inSize outOffset outSize with
            gasAvailable := targetGas }
        substate :=
          (EvmYul.State.addAccessedAccount charged.toState target).substate }
    EvmYul.EVM.call fuel.succ gasCost blobVersionedHashes gas
        (EvmYul.UInt256.ofNat evm.executionEnv.codeOwner) address address
        value value inOffset inSize outOffset outSize evm.executionEnv.perm
        evm =
      .ok (⟨0⟩, evmAfter) ∧
      (∃ yulCallMap,
        EvmYul.Yul.callTransferAccountMap? yul.accountMap
            yul.executionEnv.codeOwner target value =
          some yulCallMap ∧
        CompiledAccountMapRel yulCallMap
          (evmCallTransfer evm.accountMap yul.executionEnv.codeOwner
            target value)) ∧
      (1024 : Nat) ≤ yul.executionEnv.depth ∧
      ∃ yulAfter,
        EvmYul.Yul.buildContractCallEmptyReturnState
            (EvmYul.Yul.addAccessedAccount (.Ok yul store) target)
            none inOffset inSize outOffset outSize ⟨0⟩ =
          .ok (.Ok yulAfter store, [⟨0⟩]) ∧
        Reference.SharedStateRel cfg yulAfter evmAfter.toSharedState := by
  dsimp at hGas ⊢
  constructor
  · exact EVM_call_depthLimit_eq hEnough hDepthLimit
  · have hOwner :
        yul.executionEnv.codeOwner = evm.executionEnv.codeOwner := by
      rcases hShared with ⟨hChain, _hMachine⟩
      simpa using hChain.executionEnv.codeOwner
    have hDepth :
        yul.executionEnv.depth = evm.executionEnv.depth := by
      rcases hShared with ⟨hChain, _hMachine⟩
      simpa using hChain.executionEnv.depth
    constructor
    · exact
        hParentWorld.callTransferAccountMap?_of_evm_enough
          (source := yul.executionEnv.codeOwner)
          (recipient := EvmYul.AccountAddress.ofUInt256 address)
          (value := value)
          (by simpa [hOwner] using hEnough)
    · constructor
      · rw [hDepth]
        exact Nat.not_lt.mp hDepthLimit
      · exact
          buildContractCallEmptyReturnState_afterAccess_none_rel
            hShared store (EvmYul.AccountAddress.ofUInt256 address)
            inOffset inSize outOffset outSize ⟨0⟩ hGas

theorem primCall_CALL_depthLimit_emptyReturn_rel
    {cfg : Reference.StateRelConfig}
    {fuel gasCost : Nat}
    {blobVersionedHashes : List ByteArray}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.EVM.State}
    (hShared : Reference.SharedStateRel cfg yul evm.toSharedState)
    (hParentWorld : CompiledAccountMapRel yul.accountMap evm.accountMap)
    (store : EvmYul.Yul.VarStore)
    {gas address value inOffset inSize outOffset outSize : EvmYul.UInt256}
    (hStaticAllowed :
      ¬ (¬ yul.executionEnv.perm ∧ value ≠ ⟨0⟩))
    (hEnough :
      value ≤
        (evm.accountMap.find? evm.executionEnv.codeOwner |>.option ⟨0⟩
          (·.balance)))
    (hDepthLimit : ¬ evm.executionEnv.depth < 1024)
    (hGas :
      let target := EvmYul.AccountAddress.ofUInt256 address
      let callGas :=
        EvmYul.EVM.Ccallgas target target value gas evm.accountMap
          evm.toMachineState evm.substate
      let charged : EvmYul.EVM.State :=
        { evm with
          gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
      let targetGas :=
        (charged.toMachineState.finishExternalCall ByteArray.empty
          inOffset inSize outOffset outSize).gasAvailable +
          EvmYul.UInt256.ofNat callGas
      cfg.gasAvailableRel
        (yul.toMachineState.finishExternalCall ByteArray.empty
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    let target := EvmYul.AccountAddress.ofUInt256 address
    let callGas :=
      EvmYul.EVM.Ccallgas target target value gas evm.accountMap
        evm.toMachineState evm.substate
    let charged : EvmYul.EVM.State :=
      { evm with gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
    let targetGas :=
      (charged.toMachineState.finishExternalCall ByteArray.empty
        inOffset inSize outOffset outSize).gasAvailable +
        EvmYul.UInt256.ofNat callGas
    let evmAfter : EvmYul.EVM.State :=
      { charged with
        toMachineState :=
          { charged.toMachineState.finishExternalCall ByteArray.empty
              inOffset inSize outOffset outSize with
            gasAvailable := targetGas }
        substate :=
          (EvmYul.State.addAccessedAccount charged.toState target).substate }
    EvmYul.EVM.call fuel.succ gasCost blobVersionedHashes gas
        (EvmYul.UInt256.ofNat evm.executionEnv.codeOwner) address address
        value value inOffset inSize outOffset outSize evm.executionEnv.perm
        evm =
      .ok (⟨0⟩, evmAfter) ∧
      ∃ yulAfter,
        EvmYul.Yul.primCall fuel.succ (.Ok yul store) .CALL
            [gas, address, value, inOffset, inSize, outOffset, outSize] =
          .ok (.Ok yulAfter store, [⟨0⟩]) ∧
        Reference.SharedStateRel cfg yulAfter evmAfter.toSharedState := by
  dsimp at hGas ⊢
  rcases
      call_depthLimit_emptyReturn_rel hShared hParentWorld store
        hEnough hDepthLimit hGas with
    ⟨hEvm, hTransferExists, hDepthYul, yulAfter, hBuild, hRel⟩
  rcases hTransferExists with ⟨yulCallMap, hTransfer, _hCallMapRel⟩
  refine ⟨hEvm, yulAfter, ?_, hRel⟩
  have hStaticAllowed' :
      ¬ (yul.executionEnv.perm = false ∧ ¬ value = ⟨0⟩) := by
    intro hStatic
    exact hStaticAllowed (by simpa using hStatic)
  simpa [EvmYul.Yul.primCall, hStaticAllowed', hTransfer, hDepthYul,
    EvmYul.Yul.addAccessedAccount, EvmYul.Yul.State.sharedState,
    EvmYul.Yul.State.executionEnv, EvmYul.Yul.State.setState,
    EvmYul.Yul.State.toState, EvmYul.Yul.State.toSharedState,
    EvmYul.Yul.State.toMachineState] using hBuild

theorem UInt256_sub_zero (value : EvmYul.UInt256) :
    value - EvmYul.UInt256.ofNat 0 = value := by
  cases value with
  | mk val =>
      change
        EvmYul.UInt256.mk
            (val - (EvmYul.UInt256.ofNat 0).val) =
          EvmYul.UInt256.mk val
      congr
      have hZero :
          (EvmYul.UInt256.ofNat 0).val =
            (0 : Fin EvmYul.UInt256.size) := rfl
      rw [hZero]
      apply Fin.ext
      rw [(Fin.coe_sub_iff_le).mpr]
      · simp
      · exact Fin.zero_le val

theorem AccountAddress_ofUInt256_ofNat
    (addr : EvmYul.AccountAddress) :
    EvmYul.AccountAddress.ofUInt256 (EvmYul.UInt256.ofNat addr) =
      addr := by
  apply Fin.ext
  unfold EvmYul.AccountAddress.ofUInt256
  rw [Fin.val_ofNat]
  have hAddrLtUInt :
      (addr : Nat) < EvmYul.UInt256.size := by
    exact Nat.lt_trans addr.isLt (by decide)
  have hVal :
      (EvmYul.UInt256.ofNat addr).val.val = addr.val := by
    unfold EvmYul.UInt256.ofNat
    change (Fin.ofNat EvmYul.UInt256.size addr.val).val = addr.val
    rw [Fin.val_ofNat]
    exact Nat.mod_eq_of_lt hAddrLtUInt
  rw [hVal]
  simp [Nat.mod_eq_of_lt addr.isLt]

theorem EVM_decode_default (pc : EvmYul.UInt256) :
    EvmYul.EVM.decode (default : ByteArray) pc = none := by
  unfold EvmYul.EVM.decode ByteArray.get?
  have hNotLt :
      ¬ pc.toNat < (default : ByteArray).size := by
    rw [show (default : ByteArray).size = 0 from rfl]
    exact Nat.not_lt_zero _
  simp [hNotLt]

theorem EVM_C'_STOP (state : EvmYul.EVM.State) :
    EvmYul.EVM.C' state EvmYul.Operation.STOP = 0 := by
  simp [EvmYul.EVM.C', EvmYul.EVM.InstructionGasGroups.Wzero,
    EvmYul.EVM.InstructionGasGroups.Wcopy,
    EvmYul.EVM.InstructionGasGroups.Wextaccount,
    GasConstants.Gzero]

theorem EVM_memoryExpansionCost_STOP (state : EvmYul.EVM.State) :
    EvmYul.EVM.memoryExpansionCost state EvmYul.Operation.STOP = 0 := by
  simp [EvmYul.EVM.memoryExpansionCost,
    EvmYul.EVM.memoryExpansionCost.μᵢ', EvmYul.EVM.Cₘ]

def EVM_stopState (state : EvmYul.EVM.State) : EvmYul.EVM.State :=
  let stepped : EvmYul.EVM.State :=
    { state with execLength := state.execLength + 1 }
  { stepped with
    toMachineState :=
      (stepped.toMachineState.setReturnData ByteArray.empty).setHReturn
        ByteArray.empty }

theorem EVM_step_STOP_zero
    {fuel : Nat} (state : EvmYul.EVM.State) :
    EvmYul.EVM.step fuel.succ 0
        (some (EvmYul.Operation.STOP, none)) state =
      .ok (EVM_stopState state) := by
  unfold EvmYul.EVM.step
  dsimp
  change
    (EvmYul.step (τ := .EVM) EvmYul.Operation.STOP none)
      ({ { state with execLength := state.execLength + 1 } with
        gasAvailable := state.gasAvailable - EvmYul.UInt256.ofNat 0 }) =
      _
  rw [UInt256_sub_zero]
  rfl

theorem EVM_X_emptyCode_STOP_success
    {fuel : Nat} {validJumps : Array EvmYul.UInt256}
    {state : EvmYul.EVM.State}
    (hCode : state.executionEnv.code = default)
    (hStack : state.stack = []) :
    EvmYul.EVM.X fuel.succ.succ validJumps state =
      .ok (.success (EVM_stopState state) ByteArray.empty) := by
  simp [EvmYul.EVM.X, hCode, EVM_decode_default,
    EVM_memoryExpansionCost_STOP, EVM_C'_STOP, hStack,
    EvmYul.EVM.δ, EvmYul.EVM.α, EvmYul.Operation.isCreate,
    UInt256_sub_zero, EVM_stopState]
  change
    (do
      let evmState' ←
        EvmYul.EVM.step fuel.succ 0
          (some (EvmYul.Operation.STOP, none))
          ({ state with stack := [] })
      Except.ok (EvmYul.EVM.ExecutionResult.success evmState'
        ByteArray.empty)) = _
  rw [EVM_step_STOP_zero]
  rfl

theorem buildContractCallReturnState_ok_rel
    {cfg : Reference.StateRelConfig}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.SharedState .EVM}
    (hShared : Reference.SharedStateRel cfg yul evm)
    (store : EvmYul.Yul.VarStore)
    {yulAccountMap : EvmYul.AccountMap .Yul}
    {evmAccountMap : EvmYul.AccountMap .EVM}
    {yulSubstate evmSubstate : EvmYul.Substate}
    {targetGas : EvmYul.UInt256}
    (hAccountMap : cfg.accountMapRel yulAccountMap evmAccountMap)
    (hSubstate : yulSubstate = evmSubstate)
    (returnData : ByteArray)
    (inOffset inSize outOffset outSize value : EvmYul.UInt256)
    (hGas :
      cfg.gasAvailableRel
        (yul.toMachineState.finishExternalCall returnData
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    ∃ yulAfter,
      EvmYul.Yul.buildContractCallReturnState
          (.Ok yul store) yulAccountMap yulSubstate returnData
          inOffset inSize outOffset outSize value =
        .ok (.Ok yulAfter store, [value]) ∧
      Reference.SharedStateRel cfg yulAfter
        { evm with
          toMachineState :=
            { evm.toMachineState.finishExternalCall returnData
                inOffset inSize outOffset outSize with
              gasAvailable := targetGas }
          accountMap := evmAccountMap
          substate := evmSubstate } := by
  have hCreated : yul.createdAccounts = evm.createdAccounts := by
    rcases hShared with ⟨hChain, _hMachine⟩
    exact hChain.createdAccounts
  refine
    ⟨{ yul with
        toMachineState :=
          yul.toMachineState.finishExternalCall returnData
            inOffset inSize outOffset outSize
        accountMap := yulAccountMap
        substate := yulSubstate },
      ?_, ?_⟩
  · simp [EvmYul.Yul.buildContractCallReturnState,
      EvmYul.Yul.State.toMachineState]
  · exact
      sharedStateRel_finishExternalCallWithWorldAndTargetGas
        hShared hAccountMap hSubstate hCreated returnData
        inOffset inSize outOffset outSize hGas

theorem buildPrecompiledContractCallState_success_rel
    {cfg : Reference.StateRelConfig}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.SharedState .EVM}
    (hShared : Reference.SharedStateRel cfg yul evm)
    (store : EvmYul.Yul.VarStore)
    {yulAccountMap yulAccountMapAfter : EvmYul.AccountMap .Yul}
    {evmAccountMapAfter : EvmYul.AccountMap .EVM}
    {yulSubstateAfter evmSubstateAfter : EvmYul.Substate}
    {targetGas yulReturnedGas : EvmYul.UInt256}
    (precompiled : EvmYul.PrecompiledContract)
    (gas : EvmYul.UInt256)
    (yulEnv : EvmYul.ExecutionEnv .Yul)
    (returnData : ByteArray)
    (inOffset inSize outOffset outSize : EvmYul.UInt256)
    (hRun :
      runPrecompiledContract precompiled yulAccountMap gas yul.substate yulEnv =
        (true, yulAccountMapAfter, yulReturnedGas,
          yulSubstateAfter, returnData))
    (hAccountMap :
      cfg.accountMapRel
        (if yulAccountMapAfter.isEmpty then
          yul.accountMap
        else
          yulAccountMapAfter)
        evmAccountMapAfter)
    (hSubstate : yulSubstateAfter = evmSubstateAfter)
    (hGas :
      cfg.gasAvailableRel
        (yul.toMachineState.finishExternalCall returnData
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    ∃ yulAfter,
      EvmYul.Yul.buildPrecompiledContractCallState
          (.Ok yul store) yulAccountMap precompiled gas yulEnv
          inOffset inSize outOffset outSize =
        .ok (.Ok yulAfter store, [⟨1⟩]) ∧
      Reference.SharedStateRel cfg yulAfter
        { evm with
          toMachineState :=
            { evm.toMachineState.finishExternalCall returnData
                inOffset inSize outOffset outSize with
              gasAvailable := targetGas }
          accountMap := evmAccountMapAfter
          substate := evmSubstateAfter } := by
  rcases
    buildContractCallReturnState_ok_rel
      hShared store hAccountMap hSubstate returnData
      inOffset inSize outOffset outSize ⟨1⟩ hGas with
    ⟨yulAfter, hBuild, hRel⟩
  refine ⟨yulAfter, ?_, hRel⟩
  simp [EvmYul.Yul.buildPrecompiledContractCallState,
    EvmYul.Yul.State.toState, EvmYul.Yul.State.toSharedState,
    hRun, hBuild]

theorem buildPrecompiledContractCallState_failure_rel
    {cfg : Reference.StateRelConfig}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.SharedState .EVM}
    (hShared : Reference.SharedStateRel cfg yul evm)
    (store : EvmYul.Yul.VarStore)
    {yulAccountMap yulAccountMapAfter : EvmYul.AccountMap .Yul}
    {yulSubstateAfter : EvmYul.Substate}
    {targetGas yulReturnedGas : EvmYul.UInt256}
    (precompiled : EvmYul.PrecompiledContract)
    (gas : EvmYul.UInt256)
    (yulEnv : EvmYul.ExecutionEnv .Yul)
    (returnData : ByteArray)
    (inOffset inSize outOffset outSize : EvmYul.UInt256)
    (hRun :
      runPrecompiledContract precompiled yulAccountMap gas yul.substate yulEnv =
        (false, yulAccountMapAfter, yulReturnedGas,
          yulSubstateAfter, returnData))
    (hGas :
      cfg.gasAvailableRel
        (yul.toMachineState.finishExternalCall ByteArray.empty
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    ∃ yulAfter,
      EvmYul.Yul.buildPrecompiledContractCallState
          (.Ok yul store) yulAccountMap precompiled gas yulEnv
          inOffset inSize outOffset outSize =
        .ok (.Ok yulAfter store, [⟨0⟩]) ∧
      Reference.SharedStateRel cfg yulAfter
        { evm with
          toMachineState :=
            { evm.toMachineState.finishExternalCall ByteArray.empty
                inOffset inSize outOffset outSize with
              gasAvailable := targetGas } } := by
  rcases
    buildContractCallEmptyReturnState_none_rel
      hShared store inOffset inSize outOffset outSize ⟨0⟩ hGas with
    ⟨yulAfter, hBuild, hRel⟩
  refine ⟨yulAfter, ?_, hRel⟩
  simp [EvmYul.Yul.buildPrecompiledContractCallState,
    EvmYul.Yul.State.toState, hRun, hBuild]

theorem sharedStateRel_callResultMergeWithTargetGas
    {cfg : Reference.StateRelConfig}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.SharedState .EVM}
    (hShared : Reference.SharedStateRel cfg yul evm)
    {yulAccountMap : EvmYul.AccountMap .Yul}
    {evmAccountMap : EvmYul.AccountMap .EVM}
    {yulSubstate evmSubstate : EvmYul.Substate}
    {yulCreated evmCreated : Batteries.RBSet EvmYul.AccountAddress compare}
    {targetGas : EvmYul.UInt256}
    (hAccountMap :
      cfg.accountMapRel yulAccountMap
        (if evmAccountMap.isEmpty then
          evm.accountMap
        else
          evmAccountMap))
    (hSubstate :
      yulSubstate =
        if evmAccountMap.isEmpty then
          evm.substate
        else
          evmSubstate)
    (hCreated : yulCreated = evmCreated)
    (returnData : ByteArray)
    (inOffset inSize outOffset outSize : EvmYul.UInt256)
    (hGas :
      cfg.gasAvailableRel
        (yul.toMachineState.finishExternalCall returnData
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    Reference.SharedStateRel cfg
      { yul with
        toMachineState :=
          yul.toMachineState.finishExternalCall returnData
            inOffset inSize outOffset outSize
        accountMap := yulAccountMap
        substate := yulSubstate
        createdAccounts := yulCreated }
      { evm with
        toMachineState :=
          { evm.toMachineState.finishExternalCall returnData
              inOffset inSize outOffset outSize with
            gasAvailable := targetGas }
        accountMap :=
          if evmAccountMap.isEmpty then
            evm.accountMap
          else
            evmAccountMap
        substate :=
          if evmAccountMap.isEmpty then
            evm.substate
          else
            evmSubstate
        createdAccounts := evmCreated } := by
  exact
    sharedStateRel_finishExternalCallWithWorldAndTargetGas hShared
      hAccountMap hSubstate hCreated returnData inOffset inSize
      outOffset outSize hGas

theorem sharedStateRel_callSuccessMergeWithTargetGasOfEvmNonempty
    {cfg : Reference.StateRelConfig}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.SharedState .EVM}
    (hShared : Reference.SharedStateRel cfg yul evm)
    {yulAccountMap : EvmYul.AccountMap .Yul}
    {evmAccountMap : EvmYul.AccountMap .EVM}
    {yulSubstate evmSubstate : EvmYul.Substate}
    {yulCreated evmCreated : Batteries.RBSet EvmYul.AccountAddress compare}
    {targetGas : EvmYul.UInt256}
    (hAccountMap : cfg.accountMapRel yulAccountMap evmAccountMap)
    (hSubstate : yulSubstate = evmSubstate)
    (hCreated : yulCreated = evmCreated)
    (hEvmAccountMapNonempty :
      (evmAccountMap.isEmpty) = false)
    (returnData : ByteArray)
    (inOffset inSize outOffset outSize : EvmYul.UInt256)
    (hGas :
      cfg.gasAvailableRel
        (yul.toMachineState.finishExternalCall returnData
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    Reference.SharedStateRel cfg
      { yul with
        toMachineState :=
          yul.toMachineState.finishExternalCall returnData
            inOffset inSize outOffset outSize
        accountMap := yulAccountMap
        substate := yulSubstate
        createdAccounts := yulCreated }
      { evm with
        toMachineState :=
          { evm.toMachineState.finishExternalCall returnData
              inOffset inSize outOffset outSize with
            gasAvailable := targetGas }
        accountMap :=
          if evmAccountMap.isEmpty then
            evm.accountMap
          else
            evmAccountMap
        substate :=
          if evmAccountMap.isEmpty then
            evm.substate
          else
            evmSubstate
        createdAccounts := evmCreated } := by
  simpa [hEvmAccountMapNonempty] using
    sharedStateRel_callResultMergeWithTargetGas hShared
      (yulAccountMap := yulAccountMap)
      (evmAccountMap := evmAccountMap)
      (yulSubstate := yulSubstate)
      (evmSubstate := evmSubstate)
      (yulCreated := yulCreated)
      (evmCreated := evmCreated)
      (targetGas := targetGas)
      (by simpa [hEvmAccountMapNonempty] using hAccountMap)
      (by simpa [hEvmAccountMapNonempty] using hSubstate)
      hCreated returnData inOffset inSize
      outOffset outSize hGas

theorem restoreSuccessfulContractCallState_ok_rel
    {cfg : Reference.StateRelConfig}
    {yulParent : EvmYul.SharedState .Yul}
    {evmParent : EvmYul.SharedState .EVM}
    (hParent : Reference.SharedStateRel cfg yulParent evmParent)
    (parentStore childStore restoreStore : EvmYul.Yul.VarStore)
    {yulChild : EvmYul.SharedState .Yul}
    {evmChildAccountMap : EvmYul.AccountMap .EVM}
    {evmChildSubstate : EvmYul.Substate}
    {evmChildCreated : Batteries.RBSet EvmYul.AccountAddress compare}
    {targetGas : EvmYul.UInt256}
    (hAccountMap :
      cfg.accountMapRel
        (if yulChild.accountMap.isEmpty then
          yulParent.accountMap
        else
          yulChild.accountMap)
        (if evmChildAccountMap.isEmpty then
          evmParent.accountMap
        else
          evmChildAccountMap))
    (hSubstate :
      (if yulChild.accountMap.isEmpty then
        yulParent.substate
      else
        yulChild.substate) =
        if evmChildAccountMap.isEmpty then
          evmParent.substate
        else
          evmChildSubstate)
    (hCreated : yulChild.createdAccounts = evmChildCreated)
    (returnData : ByteArray)
    (inOffset inSize outOffset outSize : EvmYul.UInt256)
    (hGas :
      cfg.gasAvailableRel
        (yulParent.toMachineState.finishExternalCall returnData
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    ∃ yulAfter,
      EvmYul.Yul.restoreSuccessfulContractCallState
          (.Ok yulParent parentStore)
          (.Ok yulChild childStore)
          restoreStore returnData inOffset inSize outOffset outSize =
        .ok (.Ok yulAfter restoreStore, [⟨1⟩]) ∧
      Reference.SharedStateRel cfg yulAfter
        { evmParent with
          toMachineState :=
            { evmParent.toMachineState.finishExternalCall returnData
                inOffset inSize outOffset outSize with
              gasAvailable := targetGas }
          accountMap :=
            if evmChildAccountMap.isEmpty then
              evmParent.accountMap
            else
              evmChildAccountMap
          substate :=
            if evmChildAccountMap.isEmpty then
              evmParent.substate
            else
              evmChildSubstate
          createdAccounts := evmChildCreated } := by
  refine
    ⟨{ yulParent with
        toMachineState :=
          yulParent.toMachineState.finishExternalCall returnData
            inOffset inSize outOffset outSize
        accountMap :=
          if yulChild.accountMap.isEmpty then
            yulParent.accountMap
          else
            yulChild.accountMap
        substate :=
          if yulChild.accountMap.isEmpty then
            yulParent.substate
          else
            yulChild.substate
        createdAccounts := yulChild.createdAccounts },
      ?_, ?_⟩
  · simp [EvmYul.Yul.restoreSuccessfulContractCallState,
      EvmYul.Yul.State.toMachineState]
  · exact
      sharedStateRel_callResultMergeWithTargetGas hParent
        hAccountMap hSubstate hCreated returnData
        inOffset inSize outOffset outSize hGas

theorem restoreRevertedContractCallState_afterAccess_ok_rel
    {cfg : Reference.StateRelConfig}
    {yulParent : EvmYul.SharedState .Yul}
    {evmParent : EvmYul.SharedState .EVM}
    (hParent : Reference.SharedStateRel cfg yulParent evmParent)
    (parentStore childStore : EvmYul.Yul.VarStore)
    (addr : EvmYul.AccountAddress)
    {yulChild : EvmYul.SharedState .Yul}
    {targetGas : EvmYul.UInt256}
    (inOffset inSize outOffset outSize : EvmYul.UInt256)
    (hGas :
      cfg.gasAvailableRel
        (yulParent.toMachineState.finishExternalCall
          yulChild.toMachineState.H_return
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    ∃ yulAfter,
      EvmYul.Yul.restoreRevertedContractCallState
          (EvmYul.Yul.addAccessedAccount (.Ok yulParent parentStore) addr)
          (.Ok yulChild childStore)
          inOffset inSize outOffset outSize =
        .ok (.Ok yulAfter parentStore, [⟨0⟩]) ∧
      Reference.SharedStateRel cfg yulAfter
        { evmParent with
          toMachineState :=
            { evmParent.toMachineState.finishExternalCall
                yulChild.toMachineState.H_return
                inOffset inSize outOffset outSize with
              gasAvailable := targetGas }
          substate :=
            (EvmYul.State.addAccessedAccount evmParent.toState addr).substate } := by
  refine
    ⟨{ yulParent with
        toMachineState :=
          yulParent.toMachineState.finishExternalCall
            yulChild.toMachineState.H_return
            inOffset inSize outOffset outSize
        substate :=
          (EvmYul.State.addAccessedAccount yulParent.toState addr).substate },
      ?_, ?_⟩
  · simp [EvmYul.Yul.restoreRevertedContractCallState,
      EvmYul.Yul.addAccessedAccount, EvmYul.Yul.State.setState,
      EvmYul.Yul.State.toMachineState, EvmYul.Yul.State.toState,
      EvmYul.State.addAccessedAccount]
  · simpa [EvmYul.State.addAccessedAccount] using
      sharedStateRel_finishExternalCallAfterAccessWithTargetGas
        hParent addr yulChild.toMachineState.H_return
        inOffset inSize outOffset outSize hGas

theorem sharedStateRel_of_eraseGas_eq
    {cfg : Reference.StateRelConfig}
    {yul : EvmYul.SharedState .Yul}
    {evm target : EVMState}
    (hShared : Reference.SharedStateRel cfg yul target.toSharedState)
    (hErase : Assembly.eraseGas evm = Assembly.eraseGas target)
    (hGas :
      cfg.gasAvailableRel yul.toMachineState.gasAvailable
        evm.gasAvailable) :
    Reference.SharedStateRel cfg yul evm.toSharedState := by
  have hAccountMap : evm.accountMap = target.accountMap := by
    simpa [Assembly.eraseGas] using
      congrArg (fun state : EVMState => state.accountMap) hErase
  have hSigma : evm.σ₀ = target.σ₀ := by
    simpa [Assembly.eraseGas] using
      congrArg (fun state : EVMState => state.σ₀) hErase
  have hTotal :
      evm.totalGasUsedInBlock = target.totalGasUsedInBlock := by
    simpa [Assembly.eraseGas] using
      congrArg (fun state : EVMState => state.totalGasUsedInBlock) hErase
  have hReceipts :
      evm.transactionReceipts = target.transactionReceipts := by
    simpa [Assembly.eraseGas] using
      congrArg (fun state : EVMState => state.transactionReceipts) hErase
  have hSubstate : evm.substate = target.substate := by
    simpa [Assembly.eraseGas] using
      congrArg (fun state : EVMState => state.substate) hErase
  have hEnv : evm.executionEnv = target.executionEnv := by
    simpa [Assembly.eraseGas] using
      congrArg (fun state : EVMState => state.executionEnv) hErase
  have hBlocks : evm.blocks = target.blocks := by
    simpa [Assembly.eraseGas] using
      congrArg (fun state : EVMState => state.blocks) hErase
  have hGenesis : evm.genesisBlockHeader = target.genesisBlockHeader := by
    simpa [Assembly.eraseGas] using
      congrArg (fun state : EVMState => state.genesisBlockHeader) hErase
  have hCreated : evm.createdAccounts = target.createdAccounts := by
    simpa [Assembly.eraseGas] using
      congrArg (fun state : EVMState => state.createdAccounts) hErase
  have hActiveWords :
      evm.toMachineState.activeWords =
        target.toMachineState.activeWords := by
    simpa [Assembly.eraseGas] using
      congrArg
        (fun state : EVMState => state.toMachineState.activeWords) hErase
  have hMemory :
      evm.toMachineState.memory = target.toMachineState.memory := by
    simpa [Assembly.eraseGas] using
      congrArg (fun state : EVMState => state.toMachineState.memory) hErase
  have hReturnData :
      evm.toMachineState.returnData =
        target.toMachineState.returnData := by
    simpa [Assembly.eraseGas] using
      congrArg
        (fun state : EVMState => state.toMachineState.returnData) hErase
  have hHReturn :
      evm.toMachineState.H_return =
        target.toMachineState.H_return := by
    simpa [Assembly.eraseGas] using
      congrArg (fun state : EVMState => state.toMachineState.H_return) hErase
  rcases hShared with ⟨hChain, hMachine⟩
  constructor
  · constructor
    · simpa [hAccountMap] using hChain.accountMap
    · simpa [hSigma] using hChain.σ₀
    · simpa [hTotal] using hChain.totalGasUsedInBlock
    · simpa [hReceipts] using hChain.transactionReceipts
    · simpa [hSubstate] using hChain.substate
    · simpa [hEnv] using hChain.executionEnv
    · simpa [hBlocks] using hChain.blocks
    · simpa [hGenesis] using hChain.genesisBlockHeader
    · simpa [hCreated] using hChain.createdAccounts
  · constructor
    · exact hGas
    · simpa [hActiveWords] using hMachine.activeWords
    · simpa [hMemory] using hMachine.memory
    · simpa [hReturnData] using hMachine.returnData
    · simpa [hHReturn] using hMachine.H_return

theorem sharedStateRel_of_eraseControl_eq
    {cfg : Reference.StateRelConfig}
    {yul : EvmYul.SharedState .Yul}
    {evm target : EVMState}
    (hShared : Reference.SharedStateRel cfg yul target.toSharedState)
    (hErase :
      Structured.Preservation.eraseControl evm =
        Structured.Preservation.eraseControl target)
    (hGas :
      cfg.gasAvailableRel yul.toMachineState.gasAvailable
        evm.gasAvailable) :
    Reference.SharedStateRel cfg yul evm.toSharedState := by
  have hAccountMap : evm.accountMap = target.accountMap := by
    simpa [Structured.Preservation.eraseControl, Assembly.eraseGas] using
      congrArg (fun state : EVMState => state.accountMap) hErase
  have hSigma : evm.σ₀ = target.σ₀ := by
    simpa [Structured.Preservation.eraseControl, Assembly.eraseGas] using
      congrArg (fun state : EVMState => state.σ₀) hErase
  have hTotal :
      evm.totalGasUsedInBlock = target.totalGasUsedInBlock := by
    simpa [Structured.Preservation.eraseControl, Assembly.eraseGas] using
      congrArg (fun state : EVMState => state.totalGasUsedInBlock) hErase
  have hReceipts :
      evm.transactionReceipts = target.transactionReceipts := by
    simpa [Structured.Preservation.eraseControl, Assembly.eraseGas] using
      congrArg (fun state : EVMState => state.transactionReceipts) hErase
  have hSubstate : evm.substate = target.substate := by
    simpa [Structured.Preservation.eraseControl, Assembly.eraseGas] using
      congrArg (fun state : EVMState => state.substate) hErase
  have hEnv : evm.executionEnv = target.executionEnv := by
    simpa [Structured.Preservation.eraseControl, Assembly.eraseGas] using
      congrArg (fun state : EVMState => state.executionEnv) hErase
  have hBlocks : evm.blocks = target.blocks := by
    simpa [Structured.Preservation.eraseControl, Assembly.eraseGas] using
      congrArg (fun state : EVMState => state.blocks) hErase
  have hGenesis : evm.genesisBlockHeader = target.genesisBlockHeader := by
    simpa [Structured.Preservation.eraseControl, Assembly.eraseGas] using
      congrArg (fun state : EVMState => state.genesisBlockHeader) hErase
  have hCreated : evm.createdAccounts = target.createdAccounts := by
    simpa [Structured.Preservation.eraseControl, Assembly.eraseGas] using
      congrArg (fun state : EVMState => state.createdAccounts) hErase
  have hActiveWords :
      evm.toMachineState.activeWords =
        target.toMachineState.activeWords := by
    simpa [Structured.Preservation.eraseControl, Assembly.eraseGas] using
      congrArg
        (fun state : EVMState => state.toMachineState.activeWords) hErase
  have hMemory :
      evm.toMachineState.memory = target.toMachineState.memory := by
    simpa [Structured.Preservation.eraseControl, Assembly.eraseGas] using
      congrArg (fun state : EVMState => state.toMachineState.memory) hErase
  have hReturnData :
      evm.toMachineState.returnData =
        target.toMachineState.returnData := by
    simpa [Structured.Preservation.eraseControl, Assembly.eraseGas] using
      congrArg
        (fun state : EVMState => state.toMachineState.returnData) hErase
  have hHReturn :
      evm.toMachineState.H_return =
        target.toMachineState.H_return := by
    simpa [Structured.Preservation.eraseControl, Assembly.eraseGas] using
      congrArg (fun state : EVMState => state.toMachineState.H_return)
        hErase
  rcases hShared with ⟨hChain, hMachine⟩
  constructor
  · constructor
    · simpa [hAccountMap] using hChain.accountMap
    · simpa [hSigma] using hChain.σ₀
    · simpa [hTotal] using hChain.totalGasUsedInBlock
    · simpa [hReceipts] using hChain.transactionReceipts
    · simpa [hSubstate] using hChain.substate
    · simpa [hEnv] using hChain.executionEnv
    · simpa [hBlocks] using hChain.blocks
    · simpa [hGenesis] using hChain.genesisBlockHeader
    · simpa [hCreated] using hChain.createdAccounts
  · constructor
    · exact hGas
    · simpa [hActiveWords] using hMachine.activeWords
    · simpa [hMemory] using hMachine.memory
    · simpa [hReturnData] using hMachine.returnData
    · simpa [hHReturn] using hMachine.H_return

theorem wholeProgramOutcomeRel_regular_sharedStateRel
    {cfg : Reference.StateRelConfig}
    {yul : EvmYul.SharedState .Yul}
    {source : Objects.Source.State} {target : EVMState}
    (hSource :
      Reference.SharedStateRel cfg yul source.shared)
    (hRel :
      SourceLowered.WholeProgramOutcomeRel
        (Functions.Source.Outcome.regular source) (.running target))
    (hGas :
      cfg.gasAvailableRel yul.toMachineState.gasAvailable
        target.gasAvailable) :
    Reference.SharedStateRel cfg yul target.toSharedState := by
  rcases hRel with ⟨direct, hBlock, hStructured⟩
  cases direct with
  | mk directState directMode =>
      cases directMode <;>
        simp [Functions.SourceDirect.BlockScopedOutcomeRel,
          Functions.SourceDirect.StmtOutcomeRel,
          Structured.Preservation.WholeProgramOutcomeRel,
          Functions.Source.Outcome.regular,
          Locals.Source.Outcome.regular] at hBlock hStructured
      have hDirectShared :
          Reference.SharedStateRel cfg yul directState.evm.toSharedState := by
        simpa [hBlock.1.1] using hSource
      exact
        sharedStateRel_of_eraseControl_eq hDirectShared hStructured.symm
          hGas

theorem wholeProgramOutcomeRel_regular_accountMap_eq
    {source : Objects.Source.State} {target : EVMState}
    (hRel :
      SourceLowered.WholeProgramOutcomeRel
        (Functions.Source.Outcome.regular source) (.running target)) :
    target.accountMap = source.shared.accountMap := by
  rcases hRel with ⟨direct, hBlock, hStructured⟩
  cases direct with
  | mk directState directMode =>
      cases directMode <;>
        simp [Functions.SourceDirect.BlockScopedOutcomeRel,
          Functions.SourceDirect.StmtOutcomeRel,
          Structured.Preservation.WholeProgramOutcomeRel,
          Functions.Source.Outcome.regular,
          Locals.Source.Outcome.regular] at hBlock hStructured
      have hTargetAccountMap :
          target.accountMap = directState.evm.accountMap := by
        simpa [Structured.Preservation.eraseControl, Assembly.eraseGas] using
          congrArg (fun state : EVMState => state.accountMap)
            hStructured.symm
      have hDirectAccountMap :
          directState.evm.accountMap = source.shared.accountMap := by
        simpa using
          congrArg (fun shared : EvmYul.SharedState .EVM =>
            shared.accountMap) hBlock.1.1
      exact hTargetAccountMap.trans hDirectAccountMap

theorem wholeProgramOutcomeRel_regular_compiledAccountMapRel
    {yul : EvmYul.SharedState .Yul}
    {source : Objects.Source.State} {target : EVMState}
    (hWorld :
      CompiledAccountMapRel yul.accountMap source.shared.accountMap)
    (hRel :
      SourceLowered.WholeProgramOutcomeRel
        (Functions.Source.Outcome.regular source) (.running target)) :
    CompiledAccountMapRel yul.accountMap target.accountMap := by
  have hMap := wholeProgramOutcomeRel_regular_accountMap_eq hRel
  simpa [hMap] using hWorld

theorem wholeProgramOutcomeRel_halt_sharedStateRel
    {cfg : Reference.StateRelConfig}
    {yul : EvmYul.SharedState .Yul}
    {kind : Assembly.HaltKind} {source : Objects.Source.State}
    {halt : Assembly.Halt}
    (hSource :
      Reference.SharedStateRel cfg yul source.shared)
    (hRel :
      SourceLowered.WholeProgramOutcomeRel
        (Functions.Source.Outcome.halt kind source) (.halted halt))
    (hGas :
      cfg.gasAvailableRel yul.toMachineState.gasAvailable
        halt.state.gasAvailable) :
    Reference.SharedStateRel cfg yul halt.state.toSharedState := by
  rcases hRel with ⟨direct, hBlock, hStructured⟩
  cases direct with
  | mk directState directMode =>
      cases directMode <;>
        simp [Functions.SourceDirect.BlockScopedOutcomeRel,
          Functions.SourceDirect.StmtOutcomeRel,
          Structured.Preservation.WholeProgramOutcomeRel,
          Functions.Source.Outcome.halt,
          Locals.Source.Outcome.halt] at hBlock hStructured
      · rename_i directKind
        rcases hStructured with ⟨_hKind, tokens, hFrame⟩
        have hDirectShared :
            Reference.SharedStateRel cfg yul directState.evm.toSharedState := by
          simpa [hBlock.2.symm] using hSource
        have hStackShared :
            Reference.SharedStateRel cfg yul
              ({ directState.evm with stack := halt.state.stack }
                : EVMState).toSharedState := by
          simpa using hDirectShared
        exact
          sharedStateRel_of_eraseControl_eq hStackShared hFrame.dataRel hGas

theorem wholeProgramOutcomeRel_halt_accountMap_eq
    {kind : Assembly.HaltKind} {source : Objects.Source.State}
    {halt : Assembly.Halt}
    (hRel :
      SourceLowered.WholeProgramOutcomeRel
        (Functions.Source.Outcome.halt kind source) (.halted halt)) :
    halt.state.accountMap = source.shared.accountMap := by
  rcases hRel with ⟨direct, hBlock, hStructured⟩
  cases direct with
  | mk directState directMode =>
      cases directMode <;>
        simp [Functions.SourceDirect.BlockScopedOutcomeRel,
          Functions.SourceDirect.StmtOutcomeRel,
          Structured.Preservation.WholeProgramOutcomeRel,
          Functions.Source.Outcome.halt,
          Locals.Source.Outcome.halt] at hBlock hStructured
      · rename_i directKind
        rcases hStructured with ⟨_hKind, tokens, hFrame⟩
        have hTargetAccountMap :
            halt.state.accountMap = directState.evm.accountMap := by
          simpa [Structured.Preservation.eraseControl, Assembly.eraseGas] using
            congrArg (fun state : EVMState => state.accountMap)
              hFrame.dataRel
        have hDirectAccountMap :
            directState.evm.accountMap = source.shared.accountMap := by
          simpa using
            congrArg (fun shared : EvmYul.SharedState .EVM =>
              shared.accountMap) hBlock.2.symm
        exact hTargetAccountMap.trans hDirectAccountMap

theorem wholeProgramOutcomeRel_halt_compiledAccountMapRel
    {yul : EvmYul.SharedState .Yul}
    {kind : Assembly.HaltKind} {source : Objects.Source.State}
    {halt : Assembly.Halt}
    (hWorld :
      CompiledAccountMapRel yul.accountMap source.shared.accountMap)
    (hRel :
      SourceLowered.WholeProgramOutcomeRel
        (Functions.Source.Outcome.halt kind source) (.halted halt)) :
    CompiledAccountMapRel yul.accountMap halt.state.accountMap := by
  have hMap := wholeProgramOutcomeRel_halt_accountMap_eq hRel
  simpa [hMap] using hWorld

theorem dispatcherOutcomeRel_regular_ok_whole_running_sharedStateRel
    {cfg : Reference.StateRelConfig}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {program : Program}
    {initialShared finalShared : EvmYul.SharedState .Yul}
    {initialStore finalStore : EvmYul.Yul.VarStore}
    {sourceOutcome : Objects.Source.Outcome}
    {target : EVMState}
    (hOutcomeRel :
      Program.RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg
        terminalRel revertRel program (.Ok initialShared initialStore)
        (.regular (.Ok finalShared finalStore)) sourceOutcome)
    (hWhole :
      SourceLowered.WholeProgramOutcomeRel sourceOutcome (.running target))
    (hGas :
      cfg.gasAvailableRel finalShared.toMachineState.gasAvailable
        target.gasAvailable) :
    Reference.SharedStateRel cfg finalShared target.toSharedState := by
  rcases hOutcomeRel with ⟨bodyState, hFinal, hSourceRel⟩
  cases hSourceRel with
  | regular hRel =>
      cases hRel with
      | ok hShared hVars =>
          rename_i compiler shared store
          simp [Program.installContract, EvmYul.Yul.State.reviveJump,
            EvmYul.Yul.State.overwrite?, EvmYul.Yul.State.setStore] at hFinal
          rcases hFinal with ⟨hFinalShared, _hFinalStore⟩
          have hSharedFinal :
              Reference.SharedStateRel cfg finalShared compiler.shared := by
            simpa [hFinalShared.symm] using hShared
          exact
            wholeProgramOutcomeRel_regular_sharedStateRel hSharedFinal hWhole
              hGas
  | brk hRel =>
      exact False.elim (wholeProgramOutcomeRel_brk_false hWhole)
  | cont hRel =>
      exact False.elim (wholeProgramOutcomeRel_cont_false hWhole)
  | leave hRel =>
      exact False.elim (wholeProgramOutcomeRel_leave_false hWhole)

theorem compiledAccountMapRel_of_sharedStateRel_stateRelConfig
    {varStackRel : Reference.VarStackRel}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop}
    {revertRel : Reference.State → EVMState → Prop}
    {gasAvailableRel : Word → Word → Prop}
    {gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm}
    {totalGasRel : Nat → Nat → Prop}
    {yul : EvmYul.SharedState .Yul}
    {evm : EvmYul.SharedState .EVM}
    (hShared :
      Reference.SharedStateRel
        (stateRelConfig varStackRel terminalRel revertRel gasAvailableRel
          gasValueRel totalGasRel)
        yul evm) :
    CompiledAccountMapRel yul.accountMap evm.accountMap :=
  hShared.chain.accountMap

theorem stateRelConfig_accountMapRel_of_compiledAccountMapRel
    {varStackRel : Reference.VarStackRel}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop}
    {revertRel : Reference.State → EVMState → Prop}
    {gasAvailableRel : Word → Word → Prop}
    {gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm}
    {totalGasRel : Nat → Nat → Prop}
    {yulMap : EvmYul.AccountMap .Yul}
    {evmMap : EvmYul.AccountMap .EVM}
    (hRel : CompiledAccountMapRel yulMap evmMap) :
    (stateRelConfig varStackRel terminalRel revertRel gasAvailableRel
      gasValueRel totalGasRel).accountMapRel yulMap evmMap := by
  simpa [stateRelConfig, accountMapRel] using hRel

structure OrdinaryCALLBranchFacts
    (yul : EvmYul.SharedState .Yul) (evm : EvmYul.EVM.State)
    (address value : EvmYul.UInt256)
    (yulRecipient : EvmYul.Account .Yul)
    (yulCallMap : EvmYul.AccountMap .Yul)
    (evmRecipient : EvmYul.Account .EVM)
    (program : Program) (asm : Assembly.Program)
    (target : Assembly.TargetProgram) : Prop where
  findYul :
    yul.accountMap.find? (EvmYul.AccountAddress.ofUInt256 address) =
      some yulRecipient
  codeNondefault : yulRecipient.code ≠ default
  transfer :
    EvmYul.Yul.callTransferAccountMap? yul.accountMap
        yul.executionEnv.codeOwner
        (EvmYul.AccountAddress.ofUInt256 address) value =
      some yulCallMap
  yulTransferNonempty : yulCallMap.isEmpty = false
  evmTransferNonempty :
    (evmCallTransfer evm.accountMap evm.executionEnv.codeOwner
        (EvmYul.AccountAddress.ofUInt256 address) value).isEmpty =
      false
  transferRel :
    CompiledAccountMapRel yulCallMap
      (evmCallTransfer evm.accountMap evm.executionEnv.codeOwner
        (EvmYul.AccountAddress.ofUInt256 address) value)
  findEvm :
    evm.accountMap.find? (EvmYul.AccountAddress.ofUInt256 address) =
      some evmRecipient
  accountRel : CompiledAccountRel yulRecipient evmRecipient
  contract : program.contract = yulRecipient.code
  compileBoundary :
    compileCheckedAssemblyTargetBytecodeResourcesSourceStatic? program =
      some (asm, target)
  sourceStatic : Program.RecursiveBridgeSourceStaticFacts program
  sourceAccepted : Program.SourceAccepted program
  sourceCompileAccepted : Program.SourceCompileAccepted program
  compileChecked : Program.compileChecked? program = some asm
  bytecode :
    Program.compileCheckedAssemblyTargetBytecode? program =
      some (asm, target)
  resources :
    _root_.EvmCompiler.Yul.Program.RecursiveBridgeCompileResources program
  decode : Assembly.Bytecode.TargetFitsDecodeWindow target
  jumpdest : Assembly.Bytecode.JumpdestCorrect target
  code : evmRecipient.code = Assembly.Bytecode.encodeTarget target

theorem OrdinaryCALLBranchFacts.sourceCodeBytes_eq_target
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.EVM.State}
    {address value : EvmYul.UInt256}
    {yulRecipient : EvmYul.Account .Yul}
    {yulCallMap : EvmYul.AccountMap .Yul}
    {evmRecipient : EvmYul.Account .EVM}
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    (hFacts :
      OrdinaryCALLBranchFacts yul evm address value yulRecipient
        yulCallMap evmRecipient program asm target) :
    yulRecipient.codeBytes = Assembly.Bytecode.encodeTarget target :=
  hFacts.accountRel.codeBytes.trans hFacts.code

theorem OrdinaryCALLBranchFacts.fullSourceAccepted
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.EVM.State}
    {address value : EvmYul.UInt256}
    {yulRecipient : EvmYul.Account .Yul}
    {yulCallMap : EvmYul.AccountMap .Yul}
    {evmRecipient : EvmYul.Account .EVM}
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    (hFacts :
      OrdinaryCALLBranchFacts yul evm address value yulRecipient
        yulCallMap evmRecipient program asm target) :
    Program.RecursiveBridgeFullSourceAccepted program :=
  hFacts.sourceStatic.toFullSourceAccepted
    (Program.accepted_of_sourceAccepted_compileChecked?
      hFacts.sourceAccepted hFacts.compileChecked)

inductive CALLBranchFacts
    (yul : EvmYul.SharedState .Yul) (evm : EvmYul.EVM.State)
    (address value : EvmYul.UInt256) : Prop where
  | insufficientFunds
      (notEnough :
        ¬ value ≤
          (evm.accountMap.find? evm.executionEnv.codeOwner |>.option ⟨0⟩
            (·.balance))) :
      CALLBranchFacts yul evm address value
  | depthLimit
      (enough :
        value ≤
          (evm.accountMap.find? evm.executionEnv.codeOwner |>.option ⟨0⟩
            (·.balance)))
      (depthLimit : ¬ evm.executionEnv.depth < 1024) :
      CALLBranchFacts yul evm address value
  | noCode
      (enough :
        value ≤
          (evm.accountMap.find? evm.executionEnv.codeOwner |>.option ⟨0⟩
            (·.balance)))
      (depth : evm.executionEnv.depth < 1024)
      (notPrecompile :
        EvmYul.PrecompiledContract.ofAddress?
          (EvmYul.AccountAddress.ofUInt256 address) = none)
      (missingYul :
        yul.accountMap.find?
          (EvmYul.AccountAddress.ofUInt256 address) = none)
      (missingEvm :
        evm.accountMap.find?
          (EvmYul.AccountAddress.ofUInt256 address) = none) :
      CALLBranchFacts yul evm address value
  | precompiled
      (precompiled : EvmYul.PrecompiledContract)
      (enough :
        value ≤
          (evm.accountMap.find? evm.executionEnv.codeOwner |>.option ⟨0⟩
            (·.balance)))
      (depth : evm.executionEnv.depth < 1024)
      (precompile :
        EvmYul.PrecompiledContract.ofAddress?
          (EvmYul.AccountAddress.ofUInt256 address) = some precompiled) :
      CALLBranchFacts yul evm address value
  | existingDefaultCode
      (yulRecipient : EvmYul.Account .Yul)
      (evmRecipient : EvmYul.Account .EVM)
      (enough :
        value ≤
          (evm.accountMap.find? evm.executionEnv.codeOwner |>.option ⟨0⟩
            (·.balance)))
      (depth : evm.executionEnv.depth < 1024)
      (notPrecompile :
        EvmYul.PrecompiledContract.ofAddress?
          (EvmYul.AccountAddress.ofUInt256 address) = none)
      (findYul :
        yul.accountMap.find?
          (EvmYul.AccountAddress.ofUInt256 address) =
        some yulRecipient)
      (codeDefault : yulRecipient.code = default)
      (findEvm :
        evm.accountMap.find?
          (EvmYul.AccountAddress.ofUInt256 address) =
        some evmRecipient)
      (accountRel : CompiledAccountRel yulRecipient evmRecipient)
      (evmCodeDefault : evmRecipient.code = default) :
      CALLBranchFacts yul evm address value
  | ordinary
      (yulRecipient : EvmYul.Account .Yul)
      (yulCallMap : EvmYul.AccountMap .Yul)
      (evmRecipient : EvmYul.Account .EVM)
      (program : Program) (asm : Assembly.Program)
      (target : Assembly.TargetProgram)
      (enough :
        value ≤
          (evm.accountMap.find? evm.executionEnv.codeOwner |>.option ⟨0⟩
            (·.balance)))
      (depth : evm.executionEnv.depth < 1024)
      (notPrecompile :
        EvmYul.PrecompiledContract.ofAddress?
          (EvmYul.AccountAddress.ofUInt256 address) = none)
      (facts :
        OrdinaryCALLBranchFacts yul evm address value yulRecipient
          yulCallMap evmRecipient program asm target) :
      CALLBranchFacts yul evm address value

theorem ordinaryCall_nondefault_transferCheckedFacts_stateRelConfig
    {varStackRel : Reference.VarStackRel}
    {terminalCfgRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop}
    {revertCfgRel : Reference.State → EVMState → Prop}
    {gasAvailableRel : Word → Word → Prop}
    {gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm}
    {totalGasRel : Nat → Nat → Prop}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.EVM.State}
    (hShared :
      Reference.SharedStateRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        yul evm.toSharedState)
    {address value : EvmYul.UInt256}
    {yulRecipient : EvmYul.Account .Yul}
    (hFindYul :
      yul.accountMap.find? (EvmYul.AccountAddress.ofUInt256 address) =
        some yulRecipient)
    (hCodeNondefault : yulRecipient.code ≠ default)
    (hEnough :
      value ≤
        (evm.accountMap.find? evm.executionEnv.codeOwner |>.option ⟨0⟩
          (·.balance))) :
    ∃ (yulCallMap : EvmYul.AccountMap .Yul)
      (evmRecipient : EvmYul.Account .EVM)
      (program : Program) (asm : Assembly.Program)
      (target : Assembly.TargetProgram),
      EvmYul.Yul.callTransferAccountMap? yul.accountMap
          yul.executionEnv.codeOwner
          (EvmYul.AccountAddress.ofUInt256 address) value =
        some yulCallMap ∧
        yulCallMap.isEmpty = false ∧
        (evmCallTransfer evm.accountMap evm.executionEnv.codeOwner
            (EvmYul.AccountAddress.ofUInt256 address) value).isEmpty =
          false ∧
        CompiledAccountMapRel yulCallMap
          (evmCallTransfer evm.accountMap evm.executionEnv.codeOwner
            (EvmYul.AccountAddress.ofUInt256 address) value) ∧
        evm.accountMap.find? (EvmYul.AccountAddress.ofUInt256 address) =
          some evmRecipient ∧
        CompiledAccountRel yulRecipient evmRecipient ∧
        program.contract = yulRecipient.code ∧
        compileCheckedAssemblyTargetBytecodeResourcesSourceStatic? program =
          some (asm, target) ∧
        Program.RecursiveBridgeSourceStaticFacts program ∧
        Program.SourceAccepted program ∧
        Program.SourceCompileAccepted program ∧
        Program.compileChecked? program = some asm ∧
        Program.compileCheckedAssemblyTargetBytecode? program =
          some (asm, target) ∧
        _root_.EvmCompiler.Yul.Program.RecursiveBridgeCompileResources
          program ∧
        Assembly.Bytecode.TargetFitsDecodeWindow target ∧
        Assembly.Bytecode.JumpdestCorrect target ∧
        evmRecipient.code = Assembly.Bytecode.encodeTarget target := by
  have hWorld :
      CompiledAccountMapRel yul.accountMap evm.accountMap :=
    compiledAccountMapRel_of_sharedStateRel_stateRelConfig hShared
  have hOwner :
      yul.executionEnv.codeOwner = evm.executionEnv.codeOwner := by
    rcases hShared with ⟨hChain, _hMachine⟩
    simpa using hChain.executionEnv.codeOwner
  rcases
      hWorld.ordinaryCall_nondefault_transferCheckedFacts
        (source := yul.executionEnv.codeOwner)
        (recipient := EvmYul.AccountAddress.ofUInt256 address)
        (value := value)
        hFindYul hCodeNondefault (by simpa [hOwner] using hEnough) with
    ⟨yulCallMap, evmRecipient, program, asm, target, hTransfer,
      hYulNonempty, hEvmNonempty, hTransferRel, hFindEvm, hAccount,
      hContract, hCompile, hStatic, hSourceAccepted,
      hSourceCompileAccepted, hCompileChecked, hBytecode, hResources,
      hDecode, hJumpdest, hBytes⟩
  exact
    ⟨yulCallMap, evmRecipient, program, asm, target, hTransfer,
      hYulNonempty, by simpa [hOwner] using hEvmNonempty,
      by simpa [hOwner] using hTransferRel, hFindEvm, hAccount,
      hContract, hCompile, hStatic, hSourceAccepted,
      hSourceCompileAccepted, hCompileChecked, hBytecode, hResources,
      hDecode, hJumpdest, hBytes⟩

theorem ordinaryCALLBranchFacts_stateRelConfig
    {varStackRel : Reference.VarStackRel}
    {terminalCfgRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop}
    {revertCfgRel : Reference.State → EVMState → Prop}
    {gasAvailableRel : Word → Word → Prop}
    {gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm}
    {totalGasRel : Nat → Nat → Prop}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.EVM.State}
    (hShared :
      Reference.SharedStateRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        yul evm.toSharedState)
    {address value : EvmYul.UInt256}
    {yulRecipient : EvmYul.Account .Yul}
    (hFindYul :
      yul.accountMap.find? (EvmYul.AccountAddress.ofUInt256 address) =
        some yulRecipient)
    (hCodeNondefault : yulRecipient.code ≠ default)
    (hEnough :
      value ≤
        (evm.accountMap.find? evm.executionEnv.codeOwner |>.option ⟨0⟩
          (·.balance))) :
    ∃ (yulCallMap : EvmYul.AccountMap .Yul)
      (evmRecipient : EvmYul.Account .EVM)
      (program : Program) (asm : Assembly.Program)
      (target : Assembly.TargetProgram),
      OrdinaryCALLBranchFacts yul evm address value yulRecipient
        yulCallMap evmRecipient program asm target := by
  rcases
      ordinaryCall_nondefault_transferCheckedFacts_stateRelConfig
        hShared hFindYul hCodeNondefault hEnough with
    ⟨yulCallMap, evmRecipient, program, asm, target, hTransfer,
      hYulNonempty, hEvmNonempty, hTransferRel, hFindEvm, hAccount,
      hContract, hCompile, hStatic, hSourceAccepted,
      hSourceCompileAccepted, hCompileChecked, hBytecode, hResources,
      hDecode, hJumpdest, hBytes⟩
  exact
    ⟨yulCallMap, evmRecipient, program, asm, target,
      { findYul := hFindYul
        codeNondefault := hCodeNondefault
        transfer := hTransfer
        yulTransferNonempty := hYulNonempty
        evmTransferNonempty := hEvmNonempty
        transferRel := hTransferRel
        findEvm := hFindEvm
        accountRel := hAccount
        contract := hContract
        compileBoundary := hCompile
        sourceStatic := hStatic
        sourceAccepted := hSourceAccepted
        sourceCompileAccepted := hSourceCompileAccepted
        compileChecked := hCompileChecked
        bytecode := hBytecode
        resources := hResources
        decode := hDecode
        jumpdest := hJumpdest
        code := hBytes }⟩

theorem CALLBranchFacts_stateRelConfig
    {varStackRel : Reference.VarStackRel}
    {terminalCfgRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop}
    {revertCfgRel : Reference.State → EVMState → Prop}
    {gasAvailableRel : Word → Word → Prop}
    {gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm}
    {totalGasRel : Nat → Nat → Prop}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.EVM.State}
    (hShared :
      Reference.SharedStateRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        yul evm.toSharedState)
    (address value : EvmYul.UInt256) :
    CALLBranchFacts yul evm address value := by
  have hWorld :
      CompiledAccountMapRel yul.accountMap evm.accountMap :=
    compiledAccountMapRel_of_sharedStateRel_stateRelConfig hShared
  by_cases hEnough :
      value ≤
        (evm.accountMap.find? evm.executionEnv.codeOwner |>.option ⟨0⟩
          (·.balance))
  · by_cases hDepth : evm.executionEnv.depth < 1024
    · cases hPrecompile :
        EvmYul.PrecompiledContract.ofAddress?
          (EvmYul.AccountAddress.ofUInt256 address) with
      | some precompiled =>
          exact
            CALLBranchFacts.precompiled precompiled hEnough hDepth
              hPrecompile
      | none =>
          cases hFindYul :
              yul.accountMap.find?
                (EvmYul.AccountAddress.ofUInt256 address) with
          | none =>
              exact
                CALLBranchFacts.noCode hEnough hDepth hPrecompile hFindYul
                  (hWorld.not_find_evm_of_not_find_yul hFindYul)
          | some yulRecipient =>
              by_cases hCodeDefault : yulRecipient.code = default
              · rcases hWorld.find_yul hFindYul with
                  ⟨evmRecipient, hFindEvm, hAccount⟩
                exact
                  CALLBranchFacts.existingDefaultCode yulRecipient
                    evmRecipient hEnough hDepth hPrecompile hFindYul
                    hCodeDefault hFindEvm hAccount
                    (hAccount.evm_code_eq_default_of_yul_code_default
                      hCodeDefault)
              · rcases
                  ordinaryCALLBranchFacts_stateRelConfig
                    hShared hFindYul hCodeDefault hEnough with
                  ⟨yulCallMap, evmRecipient, program, asm, target, hFacts⟩
                exact
                  CALLBranchFacts.ordinary yulRecipient yulCallMap
                    evmRecipient program asm target hEnough hDepth
                    hPrecompile hFacts
    · exact CALLBranchFacts.depthLimit hEnough hDepth
  · exact CALLBranchFacts.insufficientFunds hEnough

inductive CALLPrimitiveRel
    (cfg : Reference.StateRelConfig)
    (sourceFuel evmFuel gasCost : Nat)
    (blobVersionedHashes : List ByteArray)
    (yul : EvmYul.SharedState .Yul) (evm : EvmYul.EVM.State)
    (store : EvmYul.Yul.VarStore)
    (gas address value inOffset inSize outOffset outSize :
      EvmYul.UInt256) : Prop where
  | intro
      (ret : EvmYul.UInt256)
      (evmAfter : EvmYul.EVM.State)
      (yulAfter : EvmYul.SharedState .Yul)
      (evmCall :
    EvmYul.EVM.call evmFuel gasCost blobVersionedHashes gas
        (EvmYul.UInt256.ofNat evm.executionEnv.codeOwner) address address
        value value inOffset inSize outOffset outSize evm.executionEnv.perm
        evm =
      .ok (ret, evmAfter))
      (yulCall :
    EvmYul.Yul.primCall sourceFuel (.Ok yul store) .CALL
        [gas, address, value, inOffset, inSize, outOffset, outSize] =
      .ok (.Ok yulAfter store, [ret]))
      (stateRel :
    Reference.SharedStateRel cfg yulAfter evmAfter.toSharedState) :
      CALLPrimitiveRel cfg sourceFuel evmFuel gasCost blobVersionedHashes
        yul evm store gas address value inOffset inSize outOffset outSize

theorem primCall_CALL_insufficientFunds_emptyReturn_rel_stateRelConfig
    {varStackRel : Reference.VarStackRel}
    {terminalCfgRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop}
    {revertCfgRel : Reference.State → EVMState → Prop}
    {gasAvailableRel : Word → Word → Prop}
    {gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm}
    {totalGasRel : Nat → Nat → Prop}
    {fuel gasCost : Nat}
    {blobVersionedHashes : List ByteArray}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.EVM.State}
    (hShared :
      Reference.SharedStateRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        yul evm.toSharedState)
    (store : EvmYul.Yul.VarStore)
    {gas address value inOffset inSize outOffset outSize : EvmYul.UInt256}
    (hStaticAllowed :
      ¬ (¬ yul.executionEnv.perm ∧ value ≠ ⟨0⟩))
    (hNotEnough :
      ¬ value ≤
        (evm.accountMap.find? evm.executionEnv.codeOwner |>.option ⟨0⟩
          (·.balance)))
    (hGas :
      let target := EvmYul.AccountAddress.ofUInt256 address
      let callGas :=
        EvmYul.EVM.Ccallgas target target value gas evm.accountMap
          evm.toMachineState evm.substate
      let charged : EvmYul.EVM.State :=
        { evm with
          gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
      let targetGas :=
        (charged.toMachineState.finishExternalCall ByteArray.empty
          inOffset inSize outOffset outSize).gasAvailable +
          EvmYul.UInt256.ofNat callGas
      gasAvailableRel
        (yul.toMachineState.finishExternalCall ByteArray.empty
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    let target := EvmYul.AccountAddress.ofUInt256 address
    let callGas :=
      EvmYul.EVM.Ccallgas target target value gas evm.accountMap
        evm.toMachineState evm.substate
    let charged : EvmYul.EVM.State :=
      { evm with gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
    let targetGas :=
      (charged.toMachineState.finishExternalCall ByteArray.empty
        inOffset inSize outOffset outSize).gasAvailable +
        EvmYul.UInt256.ofNat callGas
    let evmAfter : EvmYul.EVM.State :=
      { charged with
        toMachineState :=
          { charged.toMachineState.finishExternalCall ByteArray.empty
              inOffset inSize outOffset outSize with
            gasAvailable := targetGas }
        substate :=
          (EvmYul.State.addAccessedAccount charged.toState target).substate }
    EvmYul.EVM.call fuel.succ gasCost blobVersionedHashes gas
        (EvmYul.UInt256.ofNat evm.executionEnv.codeOwner) address address
        value value inOffset inSize outOffset outSize evm.executionEnv.perm
        evm =
      .ok (⟨0⟩, evmAfter) ∧
      ∃ yulAfter,
        EvmYul.Yul.primCall fuel.succ (.Ok yul store) .CALL
            [gas, address, value, inOffset, inSize, outOffset, outSize] =
          .ok (.Ok yulAfter store, [⟨0⟩]) ∧
        Reference.SharedStateRel
          (stateRelConfig varStackRel terminalCfgRel revertCfgRel
            gasAvailableRel gasValueRel totalGasRel)
          yulAfter evmAfter.toSharedState := by
  exact
    primCall_CALL_insufficientFunds_emptyReturn_rel
      (cfg :=
        stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
      hShared
      (compiledAccountMapRel_of_sharedStateRel_stateRelConfig hShared)
      store hStaticAllowed hNotEnough hGas

theorem CALLPrimitiveRel.insufficientFunds_stateRelConfig
    {varStackRel : Reference.VarStackRel}
    {terminalCfgRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop}
    {revertCfgRel : Reference.State → EVMState → Prop}
    {gasAvailableRel : Word → Word → Prop}
    {gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm}
    {totalGasRel : Nat → Nat → Prop}
    {fuel gasCost : Nat}
    {blobVersionedHashes : List ByteArray}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.EVM.State}
    (hShared :
      Reference.SharedStateRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        yul evm.toSharedState)
    (store : EvmYul.Yul.VarStore)
    {gas address value inOffset inSize outOffset outSize : EvmYul.UInt256}
    (hStaticAllowed :
      ¬ (¬ yul.executionEnv.perm ∧ value ≠ ⟨0⟩))
    (hNotEnough :
      ¬ value ≤
        (evm.accountMap.find? evm.executionEnv.codeOwner |>.option ⟨0⟩
          (·.balance)))
    (hGas :
      let target := EvmYul.AccountAddress.ofUInt256 address
      let callGas :=
        EvmYul.EVM.Ccallgas target target value gas evm.accountMap
          evm.toMachineState evm.substate
      let charged : EvmYul.EVM.State :=
        { evm with
          gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
      let targetGas :=
        (charged.toMachineState.finishExternalCall ByteArray.empty
          inOffset inSize outOffset outSize).gasAvailable +
          EvmYul.UInt256.ofNat callGas
      gasAvailableRel
        (yul.toMachineState.finishExternalCall ByteArray.empty
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    CALLPrimitiveRel
      (stateRelConfig varStackRel terminalCfgRel revertCfgRel
        gasAvailableRel gasValueRel totalGasRel)
      fuel.succ fuel.succ gasCost blobVersionedHashes yul evm store
      gas address value inOffset inSize outOffset outSize := by
  let target := EvmYul.AccountAddress.ofUInt256 address
  let callGas :=
    EvmYul.EVM.Ccallgas target target value gas evm.accountMap
      evm.toMachineState evm.substate
  let charged : EvmYul.EVM.State :=
    { evm with gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
  let targetGas :=
    (charged.toMachineState.finishExternalCall ByteArray.empty
      inOffset inSize outOffset outSize).gasAvailable +
      EvmYul.UInt256.ofNat callGas
  let evmAfter : EvmYul.EVM.State :=
    { charged with
      toMachineState :=
        { charged.toMachineState.finishExternalCall ByteArray.empty
            inOffset inSize outOffset outSize with
          gasAvailable := targetGas }
      substate :=
        (EvmYul.State.addAccessedAccount charged.toState target).substate }
  rcases
      primCall_CALL_insufficientFunds_emptyReturn_rel_stateRelConfig
        hShared store hStaticAllowed hNotEnough hGas with
    ⟨hEvm, yulAfter, hYul, hRel⟩
  refine ⟨⟨0⟩, evmAfter, yulAfter, ?_, ?_, ?_⟩
  · simpa [evmAfter, targetGas, charged, callGas, target] using hEvm
  · exact hYul
  · simpa [evmAfter, targetGas, charged, callGas, target] using hRel

theorem primCall_CALL_depthLimit_emptyReturn_rel_stateRelConfig
    {varStackRel : Reference.VarStackRel}
    {terminalCfgRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop}
    {revertCfgRel : Reference.State → EVMState → Prop}
    {gasAvailableRel : Word → Word → Prop}
    {gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm}
    {totalGasRel : Nat → Nat → Prop}
    {fuel gasCost : Nat}
    {blobVersionedHashes : List ByteArray}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.EVM.State}
    (hShared :
      Reference.SharedStateRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        yul evm.toSharedState)
    (store : EvmYul.Yul.VarStore)
    {gas address value inOffset inSize outOffset outSize : EvmYul.UInt256}
    (hStaticAllowed :
      ¬ (¬ yul.executionEnv.perm ∧ value ≠ ⟨0⟩))
    (hEnough :
      value ≤
        (evm.accountMap.find? evm.executionEnv.codeOwner |>.option ⟨0⟩
          (·.balance)))
    (hDepthLimit : ¬ evm.executionEnv.depth < 1024)
    (hGas :
      let target := EvmYul.AccountAddress.ofUInt256 address
      let callGas :=
        EvmYul.EVM.Ccallgas target target value gas evm.accountMap
          evm.toMachineState evm.substate
      let charged : EvmYul.EVM.State :=
        { evm with
          gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
      let targetGas :=
        (charged.toMachineState.finishExternalCall ByteArray.empty
          inOffset inSize outOffset outSize).gasAvailable +
          EvmYul.UInt256.ofNat callGas
      gasAvailableRel
        (yul.toMachineState.finishExternalCall ByteArray.empty
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    let target := EvmYul.AccountAddress.ofUInt256 address
    let callGas :=
      EvmYul.EVM.Ccallgas target target value gas evm.accountMap
        evm.toMachineState evm.substate
    let charged : EvmYul.EVM.State :=
      { evm with gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
    let targetGas :=
      (charged.toMachineState.finishExternalCall ByteArray.empty
        inOffset inSize outOffset outSize).gasAvailable +
        EvmYul.UInt256.ofNat callGas
    let evmAfter : EvmYul.EVM.State :=
      { charged with
        toMachineState :=
          { charged.toMachineState.finishExternalCall ByteArray.empty
              inOffset inSize outOffset outSize with
            gasAvailable := targetGas }
        substate :=
          (EvmYul.State.addAccessedAccount charged.toState target).substate }
    EvmYul.EVM.call fuel.succ gasCost blobVersionedHashes gas
        (EvmYul.UInt256.ofNat evm.executionEnv.codeOwner) address address
        value value inOffset inSize outOffset outSize evm.executionEnv.perm
        evm =
      .ok (⟨0⟩, evmAfter) ∧
      ∃ yulAfter,
        EvmYul.Yul.primCall fuel.succ (.Ok yul store) .CALL
            [gas, address, value, inOffset, inSize, outOffset, outSize] =
          .ok (.Ok yulAfter store, [⟨0⟩]) ∧
        Reference.SharedStateRel
          (stateRelConfig varStackRel terminalCfgRel revertCfgRel
            gasAvailableRel gasValueRel totalGasRel)
          yulAfter evmAfter.toSharedState := by
  exact
    primCall_CALL_depthLimit_emptyReturn_rel
      (cfg :=
        stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
      hShared
      (compiledAccountMapRel_of_sharedStateRel_stateRelConfig hShared)
      store hStaticAllowed hEnough hDepthLimit hGas

theorem CALLPrimitiveRel.depthLimit_stateRelConfig
    {varStackRel : Reference.VarStackRel}
    {terminalCfgRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop}
    {revertCfgRel : Reference.State → EVMState → Prop}
    {gasAvailableRel : Word → Word → Prop}
    {gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm}
    {totalGasRel : Nat → Nat → Prop}
    {fuel gasCost : Nat}
    {blobVersionedHashes : List ByteArray}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.EVM.State}
    (hShared :
      Reference.SharedStateRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        yul evm.toSharedState)
    (store : EvmYul.Yul.VarStore)
    {gas address value inOffset inSize outOffset outSize : EvmYul.UInt256}
    (hStaticAllowed :
      ¬ (¬ yul.executionEnv.perm ∧ value ≠ ⟨0⟩))
    (hEnough :
      value ≤
        (evm.accountMap.find? evm.executionEnv.codeOwner |>.option ⟨0⟩
          (·.balance)))
    (hDepthLimit : ¬ evm.executionEnv.depth < 1024)
    (hGas :
      let target := EvmYul.AccountAddress.ofUInt256 address
      let callGas :=
        EvmYul.EVM.Ccallgas target target value gas evm.accountMap
          evm.toMachineState evm.substate
      let charged : EvmYul.EVM.State :=
        { evm with
          gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
      let targetGas :=
        (charged.toMachineState.finishExternalCall ByteArray.empty
          inOffset inSize outOffset outSize).gasAvailable +
          EvmYul.UInt256.ofNat callGas
      gasAvailableRel
        (yul.toMachineState.finishExternalCall ByteArray.empty
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    CALLPrimitiveRel
      (stateRelConfig varStackRel terminalCfgRel revertCfgRel
        gasAvailableRel gasValueRel totalGasRel)
      fuel.succ fuel.succ gasCost blobVersionedHashes yul evm store
      gas address value inOffset inSize outOffset outSize := by
  let target := EvmYul.AccountAddress.ofUInt256 address
  let callGas :=
    EvmYul.EVM.Ccallgas target target value gas evm.accountMap
      evm.toMachineState evm.substate
  let charged : EvmYul.EVM.State :=
    { evm with gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
  let targetGas :=
    (charged.toMachineState.finishExternalCall ByteArray.empty
      inOffset inSize outOffset outSize).gasAvailable +
      EvmYul.UInt256.ofNat callGas
  let evmAfter : EvmYul.EVM.State :=
    { charged with
      toMachineState :=
        { charged.toMachineState.finishExternalCall ByteArray.empty
            inOffset inSize outOffset outSize with
          gasAvailable := targetGas }
      substate :=
        (EvmYul.State.addAccessedAccount charged.toState target).substate }
  rcases
      primCall_CALL_depthLimit_emptyReturn_rel_stateRelConfig
        hShared store hStaticAllowed hEnough hDepthLimit hGas with
    ⟨hEvm, yulAfter, hYul, hRel⟩
  refine ⟨⟨0⟩, evmAfter, yulAfter, ?_, ?_, ?_⟩
  · simpa [evmAfter, targetGas, charged, callGas, target] using hEvm
  · exact hYul
  · simpa [evmAfter, targetGas, charged, callGas, target] using hRel

theorem dispatcherOutcomeRel_regular_ok_whole_running_compiledAccountMapRel
    {varStackRel : Reference.VarStackRel}
    {terminalCfgRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop}
    {revertCfgRel : Reference.State → EVMState → Prop}
    {gasAvailableRel : Word → Word → Prop}
    {gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm}
    {totalGasRel : Nat → Nat → Prop}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {program : Program}
    {initialShared finalShared : EvmYul.SharedState .Yul}
    {initialStore finalStore : EvmYul.Yul.VarStore}
    {sourceOutcome : Objects.Source.Outcome}
    {target : EVMState}
    (hOutcomeRel :
      Program.RecursiveBridgeSemanticContracts.dispatcherOutcomeRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        terminalRel revertRel program (.Ok initialShared initialStore)
        (.regular (.Ok finalShared finalStore)) sourceOutcome)
    (hWhole :
      SourceLowered.WholeProgramOutcomeRel sourceOutcome (.running target)) :
    CompiledAccountMapRel finalShared.accountMap target.accountMap := by
  rcases hOutcomeRel with ⟨bodyState, hFinal, hSourceRel⟩
  cases hSourceRel with
  | regular hRel =>
      cases hRel with
      | ok hShared hVars =>
          rename_i compiler shared store
          simp [Program.installContract, EvmYul.Yul.State.reviveJump,
            EvmYul.Yul.State.overwrite?, EvmYul.Yul.State.setStore] at hFinal
          rcases hFinal with ⟨hFinalShared, _hFinalStore⟩
          have hSharedFinal :
              Reference.SharedStateRel
                (stateRelConfig varStackRel terminalCfgRel revertCfgRel
                  gasAvailableRel gasValueRel totalGasRel)
                finalShared compiler.shared := by
            simpa [hFinalShared.symm] using hShared
          have hWorld :
              CompiledAccountMapRel finalShared.accountMap
                compiler.shared.accountMap :=
            compiledAccountMapRel_of_sharedStateRel_stateRelConfig
              hSharedFinal
          exact
            wholeProgramOutcomeRel_regular_compiledAccountMapRel hWorld hWhole
  | brk hRel =>
      exact False.elim (wholeProgramOutcomeRel_brk_false hWhole)
  | cont hRel =>
      exact False.elim (wholeProgramOutcomeRel_cont_false hWhole)
  | leave hRel =>
      exact False.elim (wholeProgramOutcomeRel_leave_false hWhole)

theorem dispatcherOutcomeRel_regular_ok_whole_running_childRelations
    {varStackRel : Reference.VarStackRel}
    {terminalCfgRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop}
    {revertCfgRel : Reference.State → EVMState → Prop}
    {gasAvailableRel : Word → Word → Prop}
    {gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm}
    {totalGasRel : Nat → Nat → Prop}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {program : Program}
    {initialShared finalShared : EvmYul.SharedState .Yul}
    {initialStore finalStore : EvmYul.Yul.VarStore}
    {sourceOutcome : Objects.Source.Outcome}
    {target : EVMState}
    (hOutcomeRel :
      Program.RecursiveBridgeSemanticContracts.dispatcherOutcomeRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        terminalRel revertRel program (.Ok initialShared initialStore)
        (.regular (.Ok finalShared finalStore)) sourceOutcome)
    (hWhole :
      SourceLowered.WholeProgramOutcomeRel sourceOutcome (.running target))
    (hGas :
      gasAvailableRel finalShared.toMachineState.gasAvailable
        target.gasAvailable) :
    Reference.SharedStateRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        finalShared target.toSharedState ∧
      CompiledAccountMapRel finalShared.accountMap target.accountMap := by
  exact
    ⟨dispatcherOutcomeRel_regular_ok_whole_running_sharedStateRel
        (cfg :=
          stateRelConfig varStackRel terminalCfgRel revertCfgRel
            gasAvailableRel gasValueRel totalGasRel)
        hOutcomeRel hWhole hGas,
      dispatcherOutcomeRel_regular_ok_whole_running_compiledAccountMapRel
        hOutcomeRel hWhole⟩

theorem dispatcherOutcomeRel_regular_ok_whole_childRelations
    {varStackRel : Reference.VarStackRel}
    {terminalCfgRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop}
    {revertCfgRel : Reference.State → EVMState → Prop}
    {gasAvailableRel : Word → Word → Prop}
    {gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm}
    {totalGasRel : Nat → Nat → Prop}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {program : Program}
    {initialShared finalShared : EvmYul.SharedState .Yul}
    {initialStore finalStore : EvmYul.Yul.VarStore}
    {sourceOutcome : Objects.Source.Outcome}
    {targetOutcome : Assembly.StepResult}
    (hOutcomeRel :
      Program.RecursiveBridgeSemanticContracts.dispatcherOutcomeRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        terminalRel revertRel program (.Ok initialShared initialStore)
        (.regular (.Ok finalShared finalStore)) sourceOutcome)
    (hWhole :
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome)
    (hGas :
      ∀ {target}, targetOutcome = .running target →
        gasAvailableRel finalShared.toMachineState.gasAvailable
          target.gasAvailable) :
    ∃ target,
      targetOutcome = .running target ∧
        Reference.SharedStateRel
          (stateRelConfig varStackRel terminalCfgRel revertCfgRel
            gasAvailableRel gasValueRel totalGasRel)
          finalShared target.toSharedState ∧
        CompiledAccountMapRel finalShared.accountMap target.accountMap := by
  rcases dispatcherOutcomeRel_regular_whole_running hOutcomeRel hWhole with
    ⟨bodyState, target, _hFinal, _hSourceRel, hTarget⟩
  have hWholeTarget :
      SourceLowered.WholeProgramOutcomeRel sourceOutcome (.running target) := by
    simpa [hTarget] using hWhole
  exact
    ⟨target, hTarget,
      dispatcherOutcomeRel_regular_ok_whole_running_sharedStateRel
        (cfg :=
          stateRelConfig varStackRel terminalCfgRel revertCfgRel
            gasAvailableRel gasValueRel totalGasRel)
        hOutcomeRel hWholeTarget (hGas hTarget),
      dispatcherOutcomeRel_regular_ok_whole_running_compiledAccountMapRel
        hOutcomeRel hWholeTarget⟩

theorem dispatcherOutcomeRel_yulHalt_ok_whole_childRelations
    {varStackRel : Reference.VarStackRel}
    {terminalCfgRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop}
    {revertCfgRel : Reference.State → EVMState → Prop}
    {gasAvailableRel : Word → Word → Prop}
    {gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm}
    {totalGasRel : Nat → Nat → Prop}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {program : Program}
    {initialShared finalShared : EvmYul.SharedState .Yul}
    {initialStore finalStore : EvmYul.Yul.VarStore}
    {value : Word}
    {sourceOutcome : Objects.Source.Outcome}
    {targetOutcome : Assembly.StepResult}
    (hOutcomeRel :
      Program.RecursiveBridgeSemanticContracts.dispatcherOutcomeRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        terminalRel revertRel program (.Ok initialShared initialStore)
        (.yulHalt (.Ok finalShared finalStore) value) sourceOutcome)
    (hWhole :
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome)
    (hTerminalShared :
      ∀ {kind compiler},
        terminalRel kind value (.Ok finalShared finalStore) compiler →
          Reference.SharedStateRel
            (stateRelConfig varStackRel terminalCfgRel revertCfgRel
              gasAvailableRel gasValueRel totalGasRel)
            finalShared compiler.shared)
    (hGas :
      ∀ {halt}, targetOutcome = .halted halt →
        gasAvailableRel finalShared.toMachineState.gasAvailable
          halt.state.gasAvailable) :
    ∃ kind compiler halt,
      terminalRel kind value (.Ok finalShared finalStore) compiler ∧
        sourceOutcome = Functions.Source.Outcome.halt kind compiler ∧
        targetOutcome = .halted halt ∧
        halt.kind = kind ∧
        Reference.SharedStateRel
          (stateRelConfig varStackRel terminalCfgRel revertCfgRel
            gasAvailableRel gasValueRel totalGasRel)
          finalShared halt.state.toSharedState ∧
        CompiledAccountMapRel finalShared.accountMap halt.state.accountMap := by
  rcases dispatcherOutcomeRel_yulHalt_whole_halted hOutcomeRel hWhole with
    ⟨kind, compiler, halt, hTerminal, hSource, hTarget, hKind⟩
  have hWholeHalt :
      SourceLowered.WholeProgramOutcomeRel
        (Functions.Source.Outcome.halt kind compiler) (.halted halt) := by
    simpa [hSource, hTarget] using hWhole
  have hSharedSource := hTerminalShared hTerminal
  have hWorldSource :
      CompiledAccountMapRel finalShared.accountMap
        compiler.shared.accountMap :=
    compiledAccountMapRel_of_sharedStateRel_stateRelConfig hSharedSource
  exact
    ⟨kind, compiler, halt, hTerminal, hSource, hTarget, hKind,
      wholeProgramOutcomeRel_halt_sharedStateRel hSharedSource hWholeHalt
        (hGas hTarget),
      wholeProgramOutcomeRel_halt_compiledAccountMapRel hWorldSource
        hWholeHalt⟩

theorem dispatcherOutcomeRel_revert_ok_whole_childRelations
    {varStackRel : Reference.VarStackRel}
    {terminalCfgRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop}
    {revertCfgRel : Reference.State → EVMState → Prop}
    {gasAvailableRel : Word → Word → Prop}
    {gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm}
    {totalGasRel : Nat → Nat → Prop}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {program : Program}
    {initialShared finalShared : EvmYul.SharedState .Yul}
    {initialStore finalStore : EvmYul.Yul.VarStore}
    {sourceOutcome : Objects.Source.Outcome}
    {targetOutcome : Assembly.StepResult}
    (hOutcomeRel :
      Program.RecursiveBridgeSemanticContracts.dispatcherOutcomeRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        terminalRel revertRel program (.Ok initialShared initialStore)
        (.revert (.Ok finalShared finalStore)) sourceOutcome)
    (hWhole :
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome)
    (hRevertShared :
      ∀ {compiler},
        revertRel (.Ok finalShared finalStore) compiler →
          Reference.SharedStateRel
            (stateRelConfig varStackRel terminalCfgRel revertCfgRel
              gasAvailableRel gasValueRel totalGasRel)
            finalShared compiler.shared)
    (hGas :
      ∀ {halt}, targetOutcome = .halted halt →
        gasAvailableRel finalShared.toMachineState.gasAvailable
          halt.state.gasAvailable) :
    ∃ compiler halt,
      revertRel (.Ok finalShared finalStore) compiler ∧
        sourceOutcome = Functions.Source.Outcome.halt .revert compiler ∧
        targetOutcome = .halted halt ∧
        halt.kind = .revert ∧
        Reference.SharedStateRel
          (stateRelConfig varStackRel terminalCfgRel revertCfgRel
            gasAvailableRel gasValueRel totalGasRel)
          finalShared halt.state.toSharedState ∧
        CompiledAccountMapRel finalShared.accountMap halt.state.accountMap := by
  rcases dispatcherOutcomeRel_revert_whole_halted hOutcomeRel hWhole with
    ⟨compiler, halt, hRevert, hSource, hTarget, hKind⟩
  have hWholeHalt :
      SourceLowered.WholeProgramOutcomeRel
        (Functions.Source.Outcome.halt .revert compiler) (.halted halt) := by
    simpa [hSource, hTarget] using hWhole
  have hSharedSource := hRevertShared hRevert
  have hWorldSource :
      CompiledAccountMapRel finalShared.accountMap
        compiler.shared.accountMap :=
    compiledAccountMapRel_of_sharedStateRel_stateRelConfig hSharedSource
  exact
    ⟨compiler, halt, hRevert, hSource, hTarget, hKind,
      wholeProgramOutcomeRel_halt_sharedStateRel hSharedSource hWholeHalt
        (hGas hTarget),
      wholeProgramOutcomeRel_halt_compiledAccountMapRel hWorldSource
        hWholeHalt⟩

theorem sharedStateRel_of_XResultAgrees_running_success
    {cfg : Reference.StateRelConfig}
    {yul : EvmYul.SharedState .Yul}
    {target evm : EVMState}
    {output : ByteArray}
    (hShared : Reference.SharedStateRel cfg yul target.toSharedState)
    (hAgree :
      Assembly.GasAware.XResultAgrees (.running target)
        (.success evm output))
    (hGas :
      cfg.gasAvailableRel yul.toMachineState.gasAvailable
        evm.gasAvailable) :
    Reference.SharedStateRel cfg yul evm.toSharedState :=
  sharedStateRel_of_eraseGas_eq hShared hAgree.1 hGas

theorem XResultAgrees_running_success_output_empty
    {target evm : EVMState} {output : ByteArray}
    (hAgree :
      Assembly.GasAware.XResultAgrees (.running target)
        (.success evm output)) :
    output = ByteArray.empty :=
  hAgree.2

theorem XResultAgrees_running_success_shape
    {target : EVMState}
    {result : EvmYul.EVM.ExecutionResult EVMState}
    (hAgree : Assembly.GasAware.XResultAgrees (.running target) result) :
    ∃ evm output,
      result = .success evm output ∧
        Assembly.GasAware.XResultAgrees (.running target)
          (.success evm output) := by
  cases result with
  | success evm output => exact ⟨evm, output, rfl, hAgree⟩
  | revert returnedGas output => cases hAgree

theorem XResultAgrees_halted_nonrevert_success_shape
    {halt : Assembly.Halt}
    {result : EvmYul.EVM.ExecutionResult EVMState}
    (hAgree : Assembly.GasAware.XResultAgrees (.halted halt) result)
    (hNotRevert : halt.kind ≠ .revert) :
    ∃ evm output,
      result = .success evm output ∧
        Assembly.GasAware.XResultAgrees (.halted halt)
          (.success evm output) := by
  cases result with
  | success evm output => exact ⟨evm, output, rfl, hAgree⟩
  | revert returnedGas output =>
      exact False.elim (hNotRevert hAgree.1)

theorem XResultAgrees_halted_revert_shape
    {halt : Assembly.Halt}
    {result : EvmYul.EVM.ExecutionResult EVMState}
    (hAgree : Assembly.GasAware.XResultAgrees (.halted halt) result)
    (hRevert : halt.kind = .revert) :
    ∃ returnedGas output,
      result = .revert returnedGas output ∧
        Assembly.GasAware.XResultAgrees (.halted halt)
          (.revert returnedGas output) := by
  cases result with
  | success evm output =>
      exact False.elim (hAgree.1 hRevert)
  | revert returnedGas output =>
      exact ⟨returnedGas, output, rfl, hAgree⟩

theorem sharedStateRel_of_XResultAgrees_halted_success
    {cfg : Reference.StateRelConfig}
    {yul : EvmYul.SharedState .Yul}
    {halt : Assembly.Halt}
    {evm : EVMState}
    {output : ByteArray}
    (hShared : Reference.SharedStateRel cfg yul halt.state.toSharedState)
    (hAgree :
      Assembly.GasAware.XResultAgrees (.halted halt)
        (.success evm output))
    (hGas :
      cfg.gasAvailableRel yul.toMachineState.gasAvailable
        evm.gasAvailable) :
    halt.kind ≠ .revert ∧
      Reference.SharedStateRel cfg yul evm.toSharedState ∧
        output = halt.output := by
  rcases hAgree with ⟨hNotRevert, hErase, hOutput⟩
  exact
    ⟨hNotRevert, sharedStateRel_of_eraseGas_eq hShared hErase hGas,
      hOutput⟩

theorem terminalReturnData_eq_of_halted_success
    {cfg : Reference.StateRelConfig}
    {yulChild : EvmYul.SharedState .Yul}
    {halt : Assembly.Halt}
    {evmChild : EVMState}
    {output : ByteArray}
    (hTargetChild :
      Reference.SharedStateRel cfg yulChild halt.state.toSharedState)
    (hHaltOutput : halt.output = halt.kind.output halt.state)
    (hAgree :
      Assembly.GasAware.XResultAgrees (.halted halt)
        (.success evmChild output))
    (hNonReturnEmpty :
      halt.kind ≠ .return →
        yulChild.toMachineState.H_return = ByteArray.empty) :
    yulChild.toMachineState.H_return = output := by
  rcases hTargetChild with ⟨_hChain, hMachine⟩
  rcases hAgree with ⟨hNotRevert, _hErase, hOutput⟩
  cases hKind : halt.kind with
  | stop =>
      have hNotReturn : halt.kind ≠ .return := by
        intro hReturn
        rw [hKind] at hReturn
        cases hReturn
      have hEmpty := hNonReturnEmpty hNotReturn
      have hHaltEmpty : halt.output = ByteArray.empty := by
        simpa [Assembly.HaltKind.output, hKind] using hHaltOutput
      calc
        yulChild.toMachineState.H_return = ByteArray.empty := hEmpty
        _ = halt.output := hHaltEmpty.symm
        _ = output := hOutput.symm
  | «return» =>
      have hHaltReturn :
          halt.output = halt.state.toMachineState.H_return := by
        simpa [Assembly.HaltKind.output, hKind] using hHaltOutput
      calc
        yulChild.toMachineState.H_return =
            halt.state.toMachineState.H_return := hMachine.H_return
        _ = halt.output := hHaltReturn.symm
        _ = output := hOutput.symm
  | revert =>
      exact False.elim (hNotRevert hKind)
  | selfdestruct =>
      have hNotReturn : halt.kind ≠ .return := by
        intro hReturn
        rw [hKind] at hReturn
        cases hReturn
      have hEmpty := hNonReturnEmpty hNotReturn
      have hHaltEmpty : halt.output = ByteArray.empty := by
        simpa [Assembly.HaltKind.output, hKind] using hHaltOutput
      calc
        yulChild.toMachineState.H_return = ByteArray.empty := hEmpty
        _ = halt.output := hHaltEmpty.symm
        _ = output := hOutput.symm

theorem terminalReturnData_eq_of_halted_success_H_return
    {yulChild : EvmYul.SharedState .Yul}
    {halt : Assembly.Halt}
    {evmChild : EVMState}
    {output : ByteArray}
    (hTargetHReturn :
      yulChild.toMachineState.H_return =
        halt.state.toMachineState.H_return)
    (hHaltOutput : halt.output = halt.kind.output halt.state)
    (hAgree :
      Assembly.GasAware.XResultAgrees (.halted halt)
        (.success evmChild output))
    (hNonReturnEmpty :
      halt.kind ≠ .return →
        yulChild.toMachineState.H_return = ByteArray.empty) :
    yulChild.toMachineState.H_return = output := by
  rcases hAgree with ⟨hNotRevert, _hErase, hOutput⟩
  cases hKind : halt.kind with
  | stop =>
      have hNotReturn : halt.kind ≠ .return := by
        intro hReturn
        rw [hKind] at hReturn
        cases hReturn
      have hEmpty := hNonReturnEmpty hNotReturn
      have hHaltEmpty : halt.output = ByteArray.empty := by
        simpa [Assembly.HaltKind.output, hKind] using hHaltOutput
      calc
        yulChild.toMachineState.H_return = ByteArray.empty := hEmpty
        _ = halt.output := hHaltEmpty.symm
        _ = output := hOutput.symm
  | «return» =>
      have hHaltReturn :
          halt.output = halt.state.toMachineState.H_return := by
        simpa [Assembly.HaltKind.output, hKind] using hHaltOutput
      calc
        yulChild.toMachineState.H_return =
            halt.state.toMachineState.H_return := hTargetHReturn
        _ = halt.output := hHaltReturn.symm
        _ = output := hOutput.symm
  | revert =>
      exact False.elim (hNotRevert hKind)
  | selfdestruct =>
      have hNotReturn : halt.kind ≠ .return := by
        intro hReturn
        rw [hKind] at hReturn
        cases hReturn
      have hEmpty := hNonReturnEmpty hNotReturn
      have hHaltEmpty : halt.output = ByteArray.empty := by
        simpa [Assembly.HaltKind.output, hKind] using hHaltOutput
      calc
        yulChild.toMachineState.H_return = ByteArray.empty := hEmpty
        _ = halt.output := hHaltEmpty.symm
        _ = output := hOutput.symm

theorem XResultAgrees_halted_revert
    {halt : Assembly.Halt}
    {returnedGas : EvmYul.UInt256}
    {output : ByteArray}
    (hAgree :
      Assembly.GasAware.XResultAgrees (.halted halt)
        (.revert returnedGas output)) :
    halt.kind = .revert ∧ output = halt.output := by
  simpa [Assembly.GasAware.XResultAgrees] using hAgree

theorem restoreRevertedContractCallState_of_XResultAgrees_halted_revert
    {cfg : Reference.StateRelConfig}
    {yulParent : EvmYul.SharedState .Yul}
    {evmParent : EvmYul.SharedState .EVM}
    (hParent : Reference.SharedStateRel cfg yulParent evmParent)
    (parentStore childStore : EvmYul.Yul.VarStore)
    (addr : EvmYul.AccountAddress)
    {yulChild : EvmYul.SharedState .Yul}
    {halt : Assembly.Halt}
    {returnedGas : EvmYul.UInt256}
    {output : ByteArray}
    (hTargetChild :
      Reference.SharedStateRel cfg yulChild halt.state.toSharedState)
    (hHaltOutput :
      halt.output = halt.kind.output halt.state)
    (hAgree :
      Assembly.GasAware.XResultAgrees (.halted halt)
        (.revert returnedGas output))
    (inOffset inSize outOffset outSize : EvmYul.UInt256)
    (hGas :
      cfg.gasAvailableRel
        (yulParent.toMachineState.finishExternalCall output
          inOffset inSize outOffset outSize).gasAvailable
        returnedGas) :
    halt.kind = .revert ∧
      ∃ yulAfter,
        EvmYul.Yul.restoreRevertedContractCallState
            (EvmYul.Yul.addAccessedAccount
              (.Ok yulParent parentStore) addr)
            (.Ok yulChild childStore)
            inOffset inSize outOffset outSize =
          .ok (.Ok yulAfter parentStore, [⟨0⟩]) ∧
        Reference.SharedStateRel cfg yulAfter
          { evmParent with
            toMachineState :=
              { evmParent.toMachineState.finishExternalCall output
                  inOffset inSize outOffset outSize with
                gasAvailable := returnedGas }
            substate :=
              (EvmYul.State.addAccessedAccount
                evmParent.toState addr).substate } := by
  rcases XResultAgrees_halted_revert hAgree with
    ⟨hKind, hResultOutput⟩
  rcases hTargetChild with ⟨_hChildChain, hChildMachine⟩
  have hHaltReturn :
      halt.output = halt.state.toMachineState.H_return := by
    simpa [Assembly.HaltKind.output, hKind] using hHaltOutput
  have hYulOutput :
      yulChild.toMachineState.H_return = output := by
    calc
      yulChild.toMachineState.H_return =
          halt.state.toMachineState.H_return := hChildMachine.H_return
      _ = halt.output := hHaltReturn.symm
      _ = output := hResultOutput.symm
  have hGasYul :
      cfg.gasAvailableRel
        (yulParent.toMachineState.finishExternalCall
          yulChild.toMachineState.H_return
          inOffset inSize outOffset outSize).gasAvailable
        returnedGas := by
    simpa [hYulOutput] using hGas
  rcases
    restoreRevertedContractCallState_afterAccess_ok_rel
      hParent parentStore childStore addr
      (yulChild := yulChild)
      inOffset inSize outOffset outSize hGasYul with
    ⟨yulAfter, hRestore, hRel⟩
  exact ⟨hKind, yulAfter, hRestore, by simpa [hYulOutput] using hRel⟩

theorem restoreRevertedContractCallState_of_XResultAgrees_halted_revert_trace
    {cfg : Reference.StateRelConfig}
    {yulParent : EvmYul.SharedState .Yul}
    {evmParent : EvmYul.SharedState .EVM}
    (hParent : Reference.SharedStateRel cfg yulParent evmParent)
    (parentStore childStore : EvmYul.Yul.VarStore)
    (addr : EvmYul.AccountAddress)
    {yulChild : EvmYul.SharedState .Yul}
    {halt : Assembly.Halt}
    {returnedGas : EvmYul.UInt256}
    {output : ByteArray}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {targetFuel : Nat} {initial : EVMState}
    (hTargetChild :
      Reference.SharedStateRel cfg yulChild halt.state.toSharedState)
    (hTrace :
      Assembly.Preservation.BlockTraceResult asm target targetFuel initial
        (.halted halt))
    (hAgree :
      Assembly.GasAware.XResultAgrees (.halted halt)
        (.revert returnedGas output))
    (inOffset inSize outOffset outSize : EvmYul.UInt256)
    (hGas :
      cfg.gasAvailableRel
        (yulParent.toMachineState.finishExternalCall output
          inOffset inSize outOffset outSize).gasAvailable
        returnedGas) :
    halt.kind = .revert ∧
      ∃ yulAfter,
        EvmYul.Yul.restoreRevertedContractCallState
            (EvmYul.Yul.addAccessedAccount
              (.Ok yulParent parentStore) addr)
            (.Ok yulChild childStore)
            inOffset inSize outOffset outSize =
          .ok (.Ok yulAfter parentStore, [⟨0⟩]) ∧
        Reference.SharedStateRel cfg yulAfter
          { evmParent with
            toMachineState :=
              { evmParent.toMachineState.finishExternalCall output
                  inOffset inSize outOffset outSize with
                gasAvailable := returnedGas }
            substate :=
              (EvmYul.State.addAccessedAccount
                evmParent.toState addr).substate } :=
  restoreRevertedContractCallState_of_XResultAgrees_halted_revert
    hParent parentStore childStore addr hTargetChild hTrace.halted_output
    hAgree inOffset inSize outOffset outSize hGas

theorem restoreRevertedContractCallState_of_XResultAgrees_halted_revert_trace_targetGas
    {cfg : Reference.StateRelConfig}
    {yulParent : EvmYul.SharedState .Yul}
    {evmParent : EvmYul.SharedState .EVM}
    (hParent : Reference.SharedStateRel cfg yulParent evmParent)
    (parentStore childStore : EvmYul.Yul.VarStore)
    (addr : EvmYul.AccountAddress)
    {yulChild : EvmYul.SharedState .Yul}
    {halt : Assembly.Halt}
    {returnedGas targetGas : EvmYul.UInt256}
    {output : ByteArray}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {targetFuel : Nat} {initial : EVMState}
    (hTargetChild :
      Reference.SharedStateRel cfg yulChild halt.state.toSharedState)
    (hTrace :
      Assembly.Preservation.BlockTraceResult asm target targetFuel initial
        (.halted halt))
    (hAgree :
      Assembly.GasAware.XResultAgrees (.halted halt)
        (.revert returnedGas output))
    (inOffset inSize outOffset outSize : EvmYul.UInt256)
    (hGas :
      cfg.gasAvailableRel
        (yulParent.toMachineState.finishExternalCall output
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    halt.kind = .revert ∧
      ∃ yulAfter,
        EvmYul.Yul.restoreRevertedContractCallState
            (EvmYul.Yul.addAccessedAccount
              (.Ok yulParent parentStore) addr)
            (.Ok yulChild childStore)
            inOffset inSize outOffset outSize =
          .ok (.Ok yulAfter parentStore, [⟨0⟩]) ∧
        Reference.SharedStateRel cfg yulAfter
          { evmParent with
            toMachineState :=
              { evmParent.toMachineState.finishExternalCall output
                  inOffset inSize outOffset outSize with
                gasAvailable := targetGas }
            substate :=
              (EvmYul.State.addAccessedAccount
                evmParent.toState addr).substate } := by
  rcases XResultAgrees_halted_revert hAgree with
    ⟨hKind, hResultOutput⟩
  rcases hTargetChild with ⟨_hChildChain, hChildMachine⟩
  have hHaltReturn :
      halt.output = halt.state.toMachineState.H_return := by
    simpa [Assembly.HaltKind.output, hKind] using hTrace.halted_output
  have hYulOutput :
      yulChild.toMachineState.H_return = output := by
    calc
      yulChild.toMachineState.H_return =
          halt.state.toMachineState.H_return := hChildMachine.H_return
      _ = halt.output := hHaltReturn.symm
      _ = output := hResultOutput.symm
  have hGasYul :
      cfg.gasAvailableRel
        (yulParent.toMachineState.finishExternalCall
          yulChild.toMachineState.H_return
          inOffset inSize outOffset outSize).gasAvailable
        targetGas := by
    simpa [hYulOutput] using hGas
  rcases
    restoreRevertedContractCallState_afterAccess_ok_rel
      hParent parentStore childStore addr
      (yulChild := yulChild)
      inOffset inSize outOffset outSize hGasYul with
    ⟨yulAfter, hRestore, hRel⟩
  exact ⟨hKind, yulAfter, hRestore, by simpa [hYulOutput] using hRel⟩

theorem CompiledAccountMapRel.of_eraseGas_eq
    {yul : EvmYul.AccountMap .Yul} {target evm : EVMState}
    (hWorld : CompiledAccountMapRel yul target.accountMap)
    (hErase : Assembly.eraseGas evm = Assembly.eraseGas target) :
    CompiledAccountMapRel yul evm.accountMap := by
  have hAccountMap : evm.accountMap = target.accountMap := by
    simpa [Assembly.eraseGas] using
      congrArg (fun state : EVMState => state.accountMap) hErase
  rw [hAccountMap]
  exact hWorld

/--
The part of a child execution state that parent call restoration actually
merges back into the caller.

This deliberately omits the child machine-state relation: successful call
restoration receives the return bytes explicitly and computes the parent
machine state from the parent, while the child contributes only world data.
-/
structure ExternalChildMergeRel
    (yul : EvmYul.SharedState .Yul)
    (evm : EvmYul.SharedState .EVM) : Prop where
  accountMap :
    CompiledAccountMapRel yul.accountMap evm.accountMap
  substate : yul.substate = evm.substate
  createdAccounts : yul.createdAccounts = evm.createdAccounts

namespace ExternalChildMergeRel

theorem of_sharedStateRel
    {cfg : Reference.StateRelConfig}
    {yul : EvmYul.SharedState .Yul}
    {evm : EvmYul.SharedState .EVM}
    (hShared : Reference.SharedStateRel cfg yul evm)
    (hWorld : CompiledAccountMapRel yul.accountMap evm.accountMap) :
    ExternalChildMergeRel yul evm := by
  exact
    ⟨hWorld, hShared.chain.substate, hShared.chain.createdAccounts⟩

theorem of_eraseGas_eq
    {yul : EvmYul.SharedState .Yul} {target evm : EVMState}
    (hChild : ExternalChildMergeRel yul target.toSharedState)
    (hErase : Assembly.eraseGas evm = Assembly.eraseGas target) :
    ExternalChildMergeRel yul evm.toSharedState := by
  have hSubstate : evm.substate = target.substate := by
    simpa [Assembly.eraseGas] using
      congrArg (fun state : EVMState => state.substate) hErase
  have hCreated : evm.createdAccounts = target.createdAccounts := by
    simpa [Assembly.eraseGas] using
      congrArg (fun state : EVMState => state.createdAccounts) hErase
  exact
    ⟨hChild.accountMap.of_eraseGas_eq hErase,
      by simpa [hSubstate.symm] using hChild.substate,
      by simpa [hCreated.symm] using hChild.createdAccounts⟩

theorem selfdestruct_of_sharedStateRel
    {cfg : Reference.StateRelConfig}
    {yul : EvmYul.SharedState .Yul}
    {evm : EvmYul.SharedState .EVM}
    (hShared : Reference.SharedStateRel cfg yul evm)
    (hWorld : CompiledAccountMapRel yul.accountMap evm.accountMap)
    (recipient : Word) (store : EvmYul.Yul.VarStore)
    (pc : Word) (stack tail : EvmYul.Stack Word) (execLength : Nat) :
    ExternalChildMergeRel
      (EvmYul.Yul.selfdestructState (.Ok yul store) recipient).toSharedState
      (EvmYul.EVM.selfdestructState
        { toSharedState := evm
          pc := pc
          stack := stack
          execLength := execLength } recipient tail).toSharedState := by
  let source := yul.executionEnv.codeOwner
  let target : EvmYul.AccountAddress :=
    EvmYul.AccountAddress.ofUInt256 recipient
  let created := yul.createdAccounts.contains source
  have hSource : evm.executionEnv.codeOwner = source := by
    simpa [source] using hShared.chain.executionEnv.codeOwner.symm
  have hCreated :
      evm.createdAccounts.contains evm.executionEnv.codeOwner = created := by
    simp [created, source, hSource, hShared.chain.createdAccounts]
  have hCreatedSource :
      evm.createdAccounts.contains source = created := by
    simp [created, source, hShared.chain.createdAccounts]
  refine ⟨?_, ?_, ?_⟩
  · simpa [EvmYul.Yul.selfdestructState, EvmYul.EVM.selfdestructState,
      EvmYul.Yul.State.setState, EvmYul.Yul.State.setMachineState,
      EvmYul.Yul.State.toSharedState, EvmYul.Yul.State.toState,
      EvmYul.Yul.State.executionEnv, EvmYul.Yul.State.toMachineState,
      EvmYul.EVM.State.replaceStackAndIncrPC, EvmYul.EVM.State.incrPC,
      source, target, created, hSource, hCreated, hCreatedSource] using
      hWorld.selfdestructAccountMap source target created
  · simp [EvmYul.Yul.selfdestructState, EvmYul.EVM.selfdestructState,
      EvmYul.Yul.State.setState, EvmYul.Yul.State.setMachineState,
      EvmYul.Yul.State.toSharedState, EvmYul.Yul.State.toState,
      EvmYul.Yul.State.executionEnv, EvmYul.Yul.State.toMachineState,
      EvmYul.EVM.State.replaceStackAndIncrPC, EvmYul.EVM.State.incrPC,
      source, created, hSource, hCreatedSource,
      hShared.chain.substate]
  · simp [EvmYul.Yul.selfdestructState, EvmYul.EVM.selfdestructState,
      EvmYul.Yul.State.setState, EvmYul.Yul.State.setMachineState,
      EvmYul.Yul.State.toSharedState, EvmYul.Yul.State.toState,
      EvmYul.Yul.State.executionEnv, EvmYul.Yul.State.toMachineState,
      EvmYul.EVM.State.replaceStackAndIncrPC, EvmYul.EVM.State.incrPC,
      hShared.chain.createdAccounts]

end ExternalChildMergeRel

set_option maxHeartbeats 1200000 in

theorem canonicalTerminalRel_externalChildMergeRel
    {varStackRel : Reference.VarStackRel}
    {terminalCfgRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop}
    {revertCfgRel : Reference.State → EVMState → Prop}
    {gasAvailableRel : Word → Word → Prop}
    {gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm}
    {totalGasRel : Nat → Nat → Prop}
    {kind : Assembly.HaltKind} {value : Word}
    {yulChild : EvmYul.SharedState .Yul}
    {childStore : EvmYul.Yul.VarStore}
    {compiler : Objects.Source.State}
    (hRel :
      Program.RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        kind value (.Ok yulChild childStore) compiler) :
    ExternalChildMergeRel yulChild compiler.shared := by
  have hNonRevert : kind ≠ .revert :=
    Program.RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel_nonrevert
      hRel
  rcases hRel with
    ⟨yulPrim, argFuel, source, sourceAfterArgs, sourceValues, args, rest,
      codeOverride, compilerAfterArgs, sharedAfter, layout, hTerminal,
      hExecSeq, hEvalArgs, hArgsRel, hStruct, hCompiler⟩
  cases hArgsRel with
  | @ok sourceShared sourceStore compilerAfterArgs hShared _hVars =>
      let sourceAfterArgs : Reference.State := .Ok sourceShared sourceStore
      have hWorld :
          CompiledAccountMapRel sourceShared.accountMap
            compilerAfterArgs.shared.accountMap :=
        compiledAccountMapRel_of_sharedStateRel_stateRelConfig hShared
      cases yulPrim <;> simp [Prim.terminal?] at hTerminal
      case StopArith op =>
        cases op <;> simp at hTerminal
        cases hTerminal
        cases argFuel with
        | zero => simp [EvmYul.Yul.evalArgs] at hEvalArgs
        | succ fuel =>
            let stopState : Reference.State :=
              sourceAfterArgs.setMachineState
                (sourceAfterArgs.toMachineState.setHReturn ByteArray.empty)
            have hPrim :
                EvmYul.Yul.primCall fuel.succ sourceAfterArgs
                    ((.StopArith .STOP : EvmYul.Operation .Yul)) sourceValues =
                  .error (.YulHalt stopState (EvmYul.UInt256.ofNat 0)) := by
              simpa [stopState, sourceAfterArgs] using
                PrimSemantics.primCall_stop_eq fuel sourceAfterArgs sourceValues
            have hResult :=
              Reference.SourceBridgeFacts.execSeq_expr_prim_call_error_of_evalArgs_ok_primCall_error
                (sourceFuel := fuel.succ) (source := source)
                (sourceAfterArgs := sourceAfterArgs)
                (yulPrim := (.StopArith .STOP : EvmYul.Operation .Yul))
                (args := args) (rest := rest) (codeOverride := codeOverride)
                (argValues := sourceValues)
                (err := .YulHalt stopState (EvmYul.UInt256.ofNat 0))
                (sourceResult :=
                  .error (.YulHalt (.Ok yulChild childStore) value))
                hEvalArgs hPrim hExecSeq
            injection hResult with hErr
            injection hErr with hState _hValue
            have hStateOk :
                (.Ok yulChild childStore : Reference.State) =
                  .Ok
                    { sourceShared with
                      toMachineState :=
                        sourceShared.toMachineState.setHReturn
                          ByteArray.empty }
                    sourceStore := by
              simpa [stopState, sourceAfterArgs,
                EvmYul.Yul.State.setMachineState] using hState
            injection hStateOk with hSharedEq _hStoreEq
            have hSharedAfter :
                sharedAfter =
                    { compilerAfterArgs.shared with
                      toMachineState :=
                        (compilerAfterArgs.shared.toMachineState.setReturnData
                          ByteArray.empty).setHReturn ByteArray.empty } := by
              let iso : EVMState :=
                { toSharedState := compilerAfterArgs.shared,
                  pc := EvmYul.UInt256.ofNat 0,
                  stack := sourceValues,
                  execLength := 0 }
              have hStep :
                  Structured.Terminal.step .stop iso =
                    .ok
                      { iso with
                        toMachineState :=
                          (iso.toMachineState.setReturnData
                            ByteArray.empty).setHReturn ByteArray.empty } := by
                simp [iso, Structured.Terminal.step,
                  Assembly.Target.stepInstr, Assembly.HaltKind.toPrimOp,
                  Assembly.PrimOp.step, Assembly.PrimOp.continuingStep?,
                  Assembly.PrimOp.toEVM]
                rfl
              simpa [Locals.Source.PrimitiveSemantics.structured,
                iso, hStep, EvmYul.EVM.State.toSharedState] using
                hStruct.symm
            cases hSharedEq
            cases hSharedAfter
            cases hCompiler
            exact
              ⟨by simpa using hWorld,
                by simpa using hShared.chain.substate,
                by simpa using hShared.chain.createdAccounts⟩
      case System op =>
        cases op <;> simp at hTerminal
        · -- RETURN
          cases hTerminal
          cases argFuel with
          | zero => simp [EvmYul.Yul.evalArgs] at hEvalArgs
          | succ fuel =>
              cases sourceValues with
              | nil =>
                  have hPrim :=
                    PrimSemantics.primCall_return_nil_eq fuel sourceAfterArgs
                  have hResult :=
                    Reference.SourceBridgeFacts.execSeq_expr_prim_call_error_of_evalArgs_ok_primCall_error
                      (sourceFuel := fuel.succ) (source := source)
                      (sourceAfterArgs := sourceAfterArgs)
                      (yulPrim := (.System .RETURN : EvmYul.Operation .Yul))
                      (args := args) (rest := rest)
                      (codeOverride := codeOverride) (argValues := [])
                      (err := .InvalidArguments)
                      (sourceResult :=
                        .error (.YulHalt (.Ok yulChild childStore) value))
                      hEvalArgs hPrim hExecSeq
                  cases hResult
              | cons offset restValues =>
                  cases restValues with
                  | nil =>
                      have hPrim :=
                        PrimSemantics.primCall_return_singleton_eq fuel
                          sourceAfterArgs offset
                      have hResult :=
                        Reference.SourceBridgeFacts.execSeq_expr_prim_call_error_of_evalArgs_ok_primCall_error
                          (sourceFuel := fuel.succ) (source := source)
                          (sourceAfterArgs := sourceAfterArgs)
                          (yulPrim := (.System .RETURN :
                            EvmYul.Operation .Yul))
                          (args := args) (rest := rest)
                          (codeOverride := codeOverride)
                          (argValues := [offset])
                          (err := .InvalidArguments)
                          (sourceResult :=
                            .error (.YulHalt (.Ok yulChild childStore) value))
                          hEvalArgs hPrim hExecSeq
                      cases hResult
                  | cons size more =>
                      cases more with
                      | nil =>
                          have hPrimEq :
                              EvmYul.Yul.primCall fuel.succ sourceAfterArgs
                                  ((.System .RETURN :
                                    EvmYul.Operation .Yul)) [offset, size] =
                                .error
                                  (.YulHalt
                                    (sourceAfterArgs.setMachineState
                                      (sourceAfterArgs.toMachineState.evmReturn
                                        offset size))
                                    ((Option.none : Option Word).getD ⟨1⟩)) := by
                            simp [EvmYul.Yul.primCall]
                            have hStep :
                                EvmYul.step
                                    ((.System .RETURN :
                                      EvmYul.Operation .Yul)) none =
                                  (fun yulState lits =>
                                    match
                                      EvmYul.Yul.binaryMachineStateOp
                                        EvmYul.MachineState.evmReturn
                                        yulState lits with
                                    | .error e => .error e
                                    | .ok (s, v) =>
                                        .error
                                          (EvmYul.Yul.Exception.YulHalt s
                                            (v.getD ⟨1⟩))) := by
                              rfl
                            rw [hStep]
                            rfl
                          have hResult :=
                            Reference.SourceBridgeFacts.execSeq_expr_prim_call_error_of_evalArgs_ok_primCall_error
                              (sourceFuel := fuel.succ) (source := source)
                              (sourceAfterArgs := sourceAfterArgs)
                              (yulPrim := (.System .RETURN :
                                EvmYul.Operation .Yul))
                              (args := args) (rest := rest)
                              (codeOverride := codeOverride)
                              (argValues := [offset, size])
                              (err :=
                                .YulHalt
                                  (sourceAfterArgs.setMachineState
                                    (sourceAfterArgs.toMachineState.evmReturn
                                      offset size))
                                  ((Option.none : Option Word).getD ⟨1⟩))
                              (sourceResult :=
                                .error
                                  (.YulHalt (.Ok yulChild childStore) value))
                              hEvalArgs hPrimEq hExecSeq
                          injection hResult with hErr
                          injection hErr with hState _hValue
                          have hStateOk :
                              (.Ok yulChild childStore : Reference.State) =
                                .Ok
                                  { sourceShared with
                                    toMachineState :=
                                      sourceShared.toMachineState.evmReturn
                                        offset size }
                                  sourceStore := by
                            simpa [sourceAfterArgs,
                              EvmYul.Yul.State.setMachineState] using hState
                          injection hStateOk with hSharedEq _hStoreEq
                          have hSharedAfterOk :
                              (Except.ok sharedAfter :
                                Except EVMException
                                  (EvmYul.SharedState .EVM)) =
                                .ok
                                  { compilerAfterArgs.shared with
                                    toMachineState :=
                                      compilerAfterArgs.shared.toMachineState.evmReturn
                                        offset size } := by
                            simpa [Locals.Source.PrimitiveSemantics.structured,
                              Structured.Terminal.step,
                              Assembly.Target.stepInstr,
                              Assembly.PrimOp.step,
                              Assembly.PrimOp.continuingStep?,
                              Assembly.HaltKind.toPrimOp,
                              Assembly.PrimOp.toEVM,
                              Locals.SourceLowering.PrimitiveSemantics.evm_step_return_eq_binaryMachineStateOp,
                              EvmYul.EVM.binaryMachineStateOp,
                              EvmYul.Stack.pop2,
                              EvmYul.EVM.State.replaceStackAndIncrPC,
                              EvmYul.EVM.State.incrPC,
                              EvmYul.EVM.State.toSharedState,
                              Id.run] using hStruct.symm
                          injection hSharedAfterOk with hSharedAfter
                          cases hSharedEq
                          cases hSharedAfter
                          cases hCompiler
                          exact
                            ⟨by simpa using hWorld,
                              by simpa using hShared.chain.substate,
                              by simpa using hShared.chain.createdAccounts⟩
                      | cons extra extras =>
                          have hPrim :=
                            PrimSemantics.primCall_return_cons_cons_cons_eq
                              fuel sourceAfterArgs offset size extra extras
                          have hResult :=
                            Reference.SourceBridgeFacts.execSeq_expr_prim_call_error_of_evalArgs_ok_primCall_error
                              (sourceFuel := fuel.succ) (source := source)
                              (sourceAfterArgs := sourceAfterArgs)
                              (yulPrim := (.System .RETURN :
                                EvmYul.Operation .Yul))
                              (args := args) (rest := rest)
                              (codeOverride := codeOverride)
                              (argValues := offset :: size :: extra :: extras)
                              (err := .InvalidArguments)
                              (sourceResult :=
                                .error
                                  (.YulHalt (.Ok yulChild childStore) value))
                              hEvalArgs hPrim hExecSeq
                          cases hResult
        · -- REVERT
          cases hTerminal
          exact False.elim (hNonRevert rfl)
        · -- SELFDESTRUCT
          cases hTerminal
          cases argFuel with
          | zero => simp [EvmYul.Yul.evalArgs] at hEvalArgs
          | succ fuel =>
              by_cases hStatic : sourceAfterArgs.executionEnv.perm = false
              · have hPrim :=
                  PrimSemantics.primCall_selfdestruct_static_eq fuel
                    sourceAfterArgs sourceValues hStatic
                have hResult :=
                  Reference.SourceBridgeFacts.execSeq_expr_prim_call_error_of_evalArgs_ok_primCall_error
                    (sourceFuel := fuel.succ) (source := source)
                    (sourceAfterArgs := sourceAfterArgs)
                    (yulPrim := (.System .SELFDESTRUCT :
                      EvmYul.Operation .Yul))
                    (args := args) (rest := rest)
                    (codeOverride := codeOverride) (argValues := sourceValues)
                    (err := .StaticModeViolation)
                    (sourceResult :=
                      .error (.YulHalt (.Ok yulChild childStore) value))
                    hEvalArgs hPrim hExecSeq
                cases hResult
              · cases sourceValues with
                | nil =>
                    have hPrim :=
                      PrimSemantics.primCall_selfdestruct_nil_eq fuel
                        sourceAfterArgs hStatic
                    have hResult :=
                      Reference.SourceBridgeFacts.execSeq_expr_prim_call_error_of_evalArgs_ok_primCall_error
                        (sourceFuel := fuel.succ) (source := source)
                        (sourceAfterArgs := sourceAfterArgs)
                        (yulPrim := (.System .SELFDESTRUCT :
                          EvmYul.Operation .Yul))
                        (args := args) (rest := rest)
                        (codeOverride := codeOverride) (argValues := [])
                        (err := .InvalidArguments)
                        (sourceResult :=
                          .error (.YulHalt (.Ok yulChild childStore) value))
                        hEvalArgs hPrim hExecSeq
                    cases hResult
                | cons recipient more =>
                    cases more with
                    | nil =>
                        have hPrim :
                            EvmYul.Yul.primCall fuel.succ sourceAfterArgs
                                ((.System .SELFDESTRUCT :
                                  EvmYul.Operation .Yul))
                                [recipient] =
                              .error
                                (.YulHalt
                                  (PrimSemantics.selfdestructState
                                    sourceAfterArgs recipient)
                                  (EvmYul.UInt256.ofNat 0)) := by
                          simp [EvmYul.Yul.primCall, hStatic,
                            PrimSemantics.step_selfdestruct_lit_eq]
                        have hResult :=
                          Reference.SourceBridgeFacts.execSeq_expr_prim_call_error_of_evalArgs_ok_primCall_error
                            (sourceFuel := fuel.succ) (source := source)
                            (sourceAfterArgs := sourceAfterArgs)
                            (yulPrim := (.System .SELFDESTRUCT :
                              EvmYul.Operation .Yul))
                            (args := args) (rest := rest)
                            (codeOverride := codeOverride)
                            (argValues := [recipient])
                            (err :=
                              .YulHalt
                                (PrimSemantics.selfdestructState
                                  sourceAfterArgs recipient)
                                (EvmYul.UInt256.ofNat 0))
                            (sourceResult :=
                              .error
                                (.YulHalt (.Ok yulChild childStore) value))
                            hEvalArgs hPrim hExecSeq
                        injection hResult with hErr
                        injection hErr with hState _hValue
                        have hStateOk :
                            (.Ok yulChild childStore : Reference.State) =
                              PrimSemantics.selfdestructState
                                sourceAfterArgs recipient := by
                          exact hState
                        have hYulChild :
                            yulChild =
                              (PrimSemantics.selfdestructState
                                sourceAfterArgs recipient).toSharedState := by
                          simpa using
                            congrArg EvmYul.Yul.State.toSharedState hStateOk
                        have hSharedAfter :
                            sharedAfter =
                                (Locals.SourceLowering.PrimitiveSemantics.selfdestructTerminalState
                                    { toSharedState := compilerAfterArgs.shared,
                                      pc := EvmYul.UInt256.ofNat 0,
                                      stack := [recipient],
                                      execLength := 0 }
                                    recipient []).toSharedState := by
                          let iso : EVMState :=
                            { toSharedState := compilerAfterArgs.shared,
                              pc := EvmYul.UInt256.ofNat 0,
                              stack := [recipient],
                              execLength := 0 }
                          have hStep :
                              Structured.Terminal.step .selfdestruct iso =
                                .ok
                                  (Locals.SourceLowering.PrimitiveSemantics.selfdestructTerminalState
                                      iso recipient []) := by
                            apply
                              Locals.SourceLowering.PrimitiveSemantics.structured_terminal_step_selfdestruct_of_stack
                            simp [iso]
                          simpa [Locals.Source.PrimitiveSemantics.structured,
                            iso, hStep] using hStruct.symm
                        cases hCompiler
                        rw [hSharedAfter]
                        have hMerge :=
                          ExternalChildMergeRel.selfdestruct_of_sharedStateRel
                            hShared hWorld recipient sourceStore
                            (EvmYul.UInt256.ofNat 0) [recipient] [] 0
                        simpa [hYulChild, PrimSemantics.selfdestructState,
                          sourceAfterArgs] using hMerge
                    | cons extra extras =>
                        have hPrim :=
                          PrimSemantics.primCall_selfdestruct_cons_cons_eq
                            fuel sourceAfterArgs recipient extra extras hStatic
                        have hResult :=
                          Reference.SourceBridgeFacts.execSeq_expr_prim_call_error_of_evalArgs_ok_primCall_error
                            (sourceFuel := fuel.succ) (source := source)
                            (sourceAfterArgs := sourceAfterArgs)
                            (yulPrim := (.System .SELFDESTRUCT :
                              EvmYul.Operation .Yul))
                            (args := args) (rest := rest)
                            (codeOverride := codeOverride)
                            (argValues := recipient :: extra :: extras)
                            (err := .InvalidArguments)
                            (sourceResult :=
                              .error
                                (.YulHalt (.Ok yulChild childStore) value))
                            hEvalArgs hPrim hExecSeq
                        cases hResult

theorem wholeProgramOutcomeRel_halt_externalChildMergeRel
    {yul : EvmYul.SharedState .Yul}
    {kind : Assembly.HaltKind} {source : Objects.Source.State}
    {halt : Assembly.Halt}
    (hChild : ExternalChildMergeRel yul source.shared)
    (hRel :
      SourceLowered.WholeProgramOutcomeRel
        (Functions.Source.Outcome.halt kind source) (.halted halt)) :
    ExternalChildMergeRel yul halt.state.toSharedState := by
  rcases hRel with ⟨direct, hBlock, hStructured⟩
  cases direct with
  | mk directState directMode =>
      cases directMode <;>
        simp [Functions.SourceDirect.BlockScopedOutcomeRel,
          Functions.SourceDirect.StmtOutcomeRel,
          Structured.Preservation.WholeProgramOutcomeRel,
          Functions.Source.Outcome.halt,
          Locals.Source.Outcome.halt] at hBlock hStructured
      rename_i directKind
      rcases hStructured with ⟨_hKind, tokens, hFrame⟩
      have hTargetAccountMap :
          halt.state.accountMap = directState.evm.accountMap := by
        simpa [Structured.Preservation.eraseControl, Assembly.eraseGas] using
          congrArg (fun state : EVMState => state.accountMap)
            hFrame.dataRel
      have hDirectAccountMap :
          directState.evm.accountMap = source.shared.accountMap := by
        simpa using
          congrArg (fun shared : EvmYul.SharedState .EVM =>
            shared.accountMap) hBlock.2.symm
      have hAccountMap :
          CompiledAccountMapRel yul.accountMap halt.state.accountMap := by
        simpa [hTargetAccountMap, hDirectAccountMap] using hChild.accountMap
      have hTargetSubstate :
          halt.state.substate = directState.evm.substate := by
        simpa [Structured.Preservation.eraseControl, Assembly.eraseGas] using
          congrArg (fun state : EVMState => state.substate)
            hFrame.dataRel
      have hDirectSubstate :
          directState.evm.substate = source.shared.substate := by
        simpa using
          congrArg (fun shared : EvmYul.SharedState .EVM =>
            shared.substate) hBlock.2.symm
      have hSubstate : yul.substate = halt.state.substate := by
        calc
          yul.substate = source.shared.substate := hChild.substate
          _ = directState.evm.substate := hDirectSubstate.symm
          _ = halt.state.substate := hTargetSubstate.symm
      have hTargetCreated :
          halt.state.createdAccounts =
            directState.evm.createdAccounts := by
        simpa [Structured.Preservation.eraseControl, Assembly.eraseGas] using
          congrArg (fun state : EVMState => state.createdAccounts)
            hFrame.dataRel
      have hDirectCreated :
          directState.evm.createdAccounts =
            source.shared.createdAccounts := by
        simpa using
          congrArg (fun shared : EvmYul.SharedState .EVM =>
            shared.createdAccounts) hBlock.2.symm
      have hCreated : yul.createdAccounts = halt.state.createdAccounts := by
        calc
          yul.createdAccounts = source.shared.createdAccounts :=
            hChild.createdAccounts
          _ = directState.evm.createdAccounts := hDirectCreated.symm
          _ = halt.state.createdAccounts := hTargetCreated.symm
      exact ⟨hAccountMap, hSubstate, hCreated⟩

theorem wholeProgramOutcomeRel_halt_H_return
    {yul : EvmYul.SharedState .Yul}
    {kind : Assembly.HaltKind} {source : Objects.Source.State}
    {halt : Assembly.Halt}
    (hChild :
      yul.toMachineState.H_return =
        source.shared.toMachineState.H_return)
    (hRel :
      SourceLowered.WholeProgramOutcomeRel
        (Functions.Source.Outcome.halt kind source) (.halted halt)) :
    yul.toMachineState.H_return =
      halt.state.toMachineState.H_return := by
  rcases hRel with ⟨direct, hBlock, hStructured⟩
  cases direct with
  | mk directState directMode =>
      cases directMode <;>
        simp [Functions.SourceDirect.BlockScopedOutcomeRel,
          Functions.SourceDirect.StmtOutcomeRel,
          Structured.Preservation.WholeProgramOutcomeRel,
          Functions.Source.Outcome.halt,
          Locals.Source.Outcome.halt] at hBlock hStructured
      rename_i directKind
      rcases hStructured with ⟨_hKind, tokens, hFrame⟩
      have hTargetHReturn :
          halt.state.toMachineState.H_return =
            directState.evm.toMachineState.H_return := by
        simpa [Structured.Preservation.eraseControl, Assembly.eraseGas] using
          congrArg
            (fun state : EVMState => state.toMachineState.H_return)
            hFrame.dataRel
      have hDirectHReturn :
          directState.evm.toMachineState.H_return =
            source.shared.toMachineState.H_return := by
        simpa using
          congrArg
            (fun shared : EvmYul.SharedState .EVM =>
              shared.toMachineState.H_return)
            hBlock.2.symm
      calc
        yul.toMachineState.H_return =
            source.shared.toMachineState.H_return := hChild
        _ = directState.evm.toMachineState.H_return :=
            hDirectHReturn.symm
        _ = halt.state.toMachineState.H_return := hTargetHReturn.symm

theorem dispatcherOutcomeRel_yulHalt_ok_whole_childMergeRelations
    {varStackRel : Reference.VarStackRel}
    {terminalCfgRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop}
    {revertCfgRel : Reference.State → EVMState → Prop}
    {gasAvailableRel : Word → Word → Prop}
    {gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm}
    {totalGasRel : Nat → Nat → Prop}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {program : Program}
    {initialShared finalShared : EvmYul.SharedState .Yul}
    {initialStore finalStore : EvmYul.Yul.VarStore}
    {value : Word}
    {sourceOutcome : Objects.Source.Outcome}
    {targetOutcome : Assembly.StepResult}
    (hOutcomeRel :
      Program.RecursiveBridgeSemanticContracts.dispatcherOutcomeRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        terminalRel revertRel program (.Ok initialShared initialStore)
        (.yulHalt (.Ok finalShared finalStore) value) sourceOutcome)
    (hWhole :
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome)
    (hTerminalChild :
      ∀ {kind compiler},
        terminalRel kind value (.Ok finalShared finalStore) compiler →
          ExternalChildMergeRel finalShared compiler.shared) :
    ∃ kind compiler halt,
      terminalRel kind value (.Ok finalShared finalStore) compiler ∧
        sourceOutcome = Functions.Source.Outcome.halt kind compiler ∧
        targetOutcome = .halted halt ∧
        halt.kind = kind ∧
        ExternalChildMergeRel finalShared halt.state.toSharedState := by
  rcases dispatcherOutcomeRel_yulHalt_whole_halted hOutcomeRel hWhole with
    ⟨kind, compiler, halt, hTerminal, hSource, hTarget, hKind⟩
  have hWholeHalt :
      SourceLowered.WholeProgramOutcomeRel
        (Functions.Source.Outcome.halt kind compiler) (.halted halt) := by
    simpa [hSource, hTarget] using hWhole
  exact
    ⟨kind, compiler, halt, hTerminal, hSource, hTarget, hKind,
      wholeProgramOutcomeRel_halt_externalChildMergeRel
        (hTerminalChild hTerminal) hWholeHalt⟩

theorem restoreSuccessfulContractCallState_childEvm_rel
    {cfg : Reference.StateRelConfig}
    {yulParent : EvmYul.SharedState .Yul}
    {evmParent : EvmYul.SharedState .EVM}
    (hParent : Reference.SharedStateRel cfg yulParent evmParent)
    (hParentWorld :
      CompiledAccountMapRel yulParent.accountMap evmParent.accountMap)
    (hCfgAccountMap :
      ∀ {yulMap : EvmYul.AccountMap .Yul}
        {evmMap : EvmYul.AccountMap .EVM},
        CompiledAccountMapRel yulMap evmMap →
          cfg.accountMapRel yulMap evmMap)
    (parentStore childStore restoreStore : EvmYul.Yul.VarStore)
    {yulChild : EvmYul.SharedState .Yul}
    {evmChild : EVMState}
    (hChild :
      Reference.SharedStateRel cfg yulChild evmChild.toSharedState)
    (hChildWorld :
      CompiledAccountMapRel yulChild.accountMap evmChild.accountMap)
    (returnData : ByteArray)
    (inOffset inSize outOffset outSize : EvmYul.UInt256)
    {targetGas : EvmYul.UInt256}
    (hGas :
      cfg.gasAvailableRel
        (yulParent.toMachineState.finishExternalCall returnData
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    ∃ yulAfter,
      EvmYul.Yul.restoreSuccessfulContractCallState
          (.Ok yulParent parentStore)
          (.Ok yulChild childStore)
          restoreStore returnData inOffset inSize outOffset outSize =
        .ok (.Ok yulAfter restoreStore, [⟨1⟩]) ∧
      Reference.SharedStateRel cfg yulAfter
        { evmParent with
          toMachineState :=
            { evmParent.toMachineState.finishExternalCall returnData
                inOffset inSize outOffset outSize with
              gasAvailable := targetGas }
          accountMap :=
            if evmChild.accountMap.isEmpty then
              evmParent.accountMap
            else
              evmChild.accountMap
          substate :=
            if evmChild.accountMap.isEmpty then
              evmParent.substate
            else
              evmChild.substate
          createdAccounts := evmChild.createdAccounts } := by
  rcases hParent with ⟨hParentChain, hParentMachine⟩
  rcases hChild with ⟨hChildChain, _hChildMachine⟩
  have hAccountMap :
      cfg.accountMapRel
        (if yulChild.accountMap.isEmpty then
          yulParent.accountMap
        else
          yulChild.accountMap)
        (if evmChild.accountMap.isEmpty then
          evmParent.accountMap
        else
          evmChild.accountMap) :=
    hCfgAccountMap <|
      CompiledAccountMapRel.if_empty_parent
        hParentWorld hChildWorld hChildWorld.isEmpty_eq
  have hSubstate :
      (if yulChild.accountMap.isEmpty then
        yulParent.substate
      else
        yulChild.substate) =
        if evmChild.accountMap.isEmpty then
          evmParent.substate
        else
          evmChild.substate := by
    cases hEvm : evmChild.accountMap.isEmpty
    · have hYul : yulChild.accountMap.isEmpty = false := by
        simpa [hEvm] using hChildWorld.isEmpty_eq
      simp [hYul, hChildChain.substate]
    · have hYul : yulChild.accountMap.isEmpty = true := by
        simpa [hEvm] using hChildWorld.isEmpty_eq
      simp [hYul, hParentChain.substate]
  exact
    restoreSuccessfulContractCallState_ok_rel
      ⟨hParentChain, hParentMachine⟩ parentStore childStore restoreStore
      (yulChild := yulChild)
      (evmChildAccountMap := evmChild.accountMap)
      (evmChildSubstate := evmChild.substate)
      (evmChildCreated := evmChild.createdAccounts)
      (targetGas := targetGas)
      hAccountMap hSubstate hChildChain.createdAccounts
      returnData inOffset inSize outOffset outSize hGas

theorem restoreSuccessfulContractCallState_childMerge_rel
    {cfg : Reference.StateRelConfig}
    {yulParent : EvmYul.SharedState .Yul}
    {evmParent : EvmYul.SharedState .EVM}
    (hParent : Reference.SharedStateRel cfg yulParent evmParent)
    (hParentWorld :
      CompiledAccountMapRel yulParent.accountMap evmParent.accountMap)
    (hCfgAccountMap :
      ∀ {yulMap : EvmYul.AccountMap .Yul}
        {evmMap : EvmYul.AccountMap .EVM},
        CompiledAccountMapRel yulMap evmMap →
          cfg.accountMapRel yulMap evmMap)
    (parentStore childStore restoreStore : EvmYul.Yul.VarStore)
    {yulChild : EvmYul.SharedState .Yul}
    {evmChild : EVMState}
    (hChild : ExternalChildMergeRel yulChild evmChild.toSharedState)
    (returnData : ByteArray)
    (inOffset inSize outOffset outSize : EvmYul.UInt256)
    {targetGas : EvmYul.UInt256}
    (hGas :
      cfg.gasAvailableRel
        (yulParent.toMachineState.finishExternalCall returnData
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    ∃ yulAfter,
      EvmYul.Yul.restoreSuccessfulContractCallState
          (.Ok yulParent parentStore)
          (.Ok yulChild childStore)
          restoreStore returnData inOffset inSize outOffset outSize =
        .ok (.Ok yulAfter restoreStore, [⟨1⟩]) ∧
      Reference.SharedStateRel cfg yulAfter
        { evmParent with
          toMachineState :=
            { evmParent.toMachineState.finishExternalCall returnData
                inOffset inSize outOffset outSize with
              gasAvailable := targetGas }
          accountMap :=
            if evmChild.accountMap.isEmpty then
              evmParent.accountMap
            else
              evmChild.accountMap
          substate :=
            if evmChild.accountMap.isEmpty then
              evmParent.substate
            else
              evmChild.substate
          createdAccounts := evmChild.createdAccounts } := by
  rcases hParent with ⟨hParentChain, hParentMachine⟩
  have hAccountMap :
      cfg.accountMapRel
        (if yulChild.accountMap.isEmpty then
          yulParent.accountMap
        else
          yulChild.accountMap)
        (if evmChild.accountMap.isEmpty then
          evmParent.accountMap
        else
          evmChild.accountMap) :=
    hCfgAccountMap <|
      CompiledAccountMapRel.if_empty_parent
        hParentWorld hChild.accountMap hChild.accountMap.isEmpty_eq
  have hSubstate :
      (if yulChild.accountMap.isEmpty then
        yulParent.substate
      else
        yulChild.substate) =
        if evmChild.accountMap.isEmpty then
          evmParent.substate
        else
          evmChild.substate := by
    cases hEvm : evmChild.accountMap.isEmpty
    · have hYul : yulChild.accountMap.isEmpty = false := by
        simpa [hEvm] using hChild.accountMap.isEmpty_eq
      simp [hYul, hChild.substate]
    · have hYul : yulChild.accountMap.isEmpty = true := by
        simpa [hEvm] using hChild.accountMap.isEmpty_eq
      simp [hYul, hParentChain.substate]
  exact
    restoreSuccessfulContractCallState_ok_rel
      ⟨hParentChain, hParentMachine⟩ parentStore childStore restoreStore
      (yulChild := yulChild)
      (evmChildAccountMap := evmChild.accountMap)
      (evmChildSubstate := evmChild.substate)
      (evmChildCreated := evmChild.createdAccounts)
      (targetGas := targetGas)
      hAccountMap hSubstate hChild.createdAccounts
      returnData inOffset inSize outOffset outSize hGas

theorem restoreSuccessfulContractCallState_of_XResultAgrees_running_success
    {cfg : Reference.StateRelConfig}
    {yulParent : EvmYul.SharedState .Yul}
    {evmParent : EvmYul.SharedState .EVM}
    (hParent : Reference.SharedStateRel cfg yulParent evmParent)
    (hParentWorld :
      CompiledAccountMapRel yulParent.accountMap evmParent.accountMap)
    (hCfgAccountMap :
      ∀ {yulMap : EvmYul.AccountMap .Yul}
        {evmMap : EvmYul.AccountMap .EVM},
        CompiledAccountMapRel yulMap evmMap →
          cfg.accountMapRel yulMap evmMap)
    (parentStore childStore restoreStore : EvmYul.Yul.VarStore)
    {yulChild : EvmYul.SharedState .Yul}
    {targetChild evmChild : EVMState}
    {returnData : ByteArray}
    (hTargetChild :
      Reference.SharedStateRel cfg yulChild targetChild.toSharedState)
    (hTargetChildWorld :
      CompiledAccountMapRel yulChild.accountMap targetChild.accountMap)
    (hAgree :
      Assembly.GasAware.XResultAgrees (.running targetChild)
        (.success evmChild returnData))
    (hChildGas :
      cfg.gasAvailableRel yulChild.toMachineState.gasAvailable
        evmChild.gasAvailable)
    (inOffset inSize outOffset outSize : EvmYul.UInt256)
    {targetGas : EvmYul.UInt256}
    (hGas :
      cfg.gasAvailableRel
        (yulParent.toMachineState.finishExternalCall returnData
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    ∃ yulAfter,
      EvmYul.Yul.restoreSuccessfulContractCallState
          (.Ok yulParent parentStore)
          (.Ok yulChild childStore)
          restoreStore returnData inOffset inSize outOffset outSize =
        .ok (.Ok yulAfter restoreStore, [⟨1⟩]) ∧
      Reference.SharedStateRel cfg yulAfter
        { evmParent with
          toMachineState :=
            { evmParent.toMachineState.finishExternalCall returnData
                inOffset inSize outOffset outSize with
              gasAvailable := targetGas }
          accountMap :=
            if evmChild.accountMap.isEmpty then
              evmParent.accountMap
            else
              evmChild.accountMap
          substate :=
            if evmChild.accountMap.isEmpty then
              evmParent.substate
            else
              evmChild.substate
          createdAccounts := evmChild.createdAccounts } := by
  have hErase : Assembly.eraseGas evmChild = Assembly.eraseGas targetChild := by
    exact hAgree.1
  exact
    restoreSuccessfulContractCallState_childEvm_rel
      hParent hParentWorld hCfgAccountMap
      parentStore childStore restoreStore
      (sharedStateRel_of_XResultAgrees_running_success
        hTargetChild hAgree hChildGas)
      (hTargetChildWorld.of_eraseGas_eq hErase)
      returnData inOffset inSize outOffset outSize hGas

theorem restoreSuccessfulContractCallState_of_XResultAgrees_running_success_empty_output
    {cfg : Reference.StateRelConfig}
    {yulParent : EvmYul.SharedState .Yul}
    {evmParent : EvmYul.SharedState .EVM}
    (hParent : Reference.SharedStateRel cfg yulParent evmParent)
    (hParentWorld :
      CompiledAccountMapRel yulParent.accountMap evmParent.accountMap)
    (hCfgAccountMap :
      ∀ {yulMap : EvmYul.AccountMap .Yul}
        {evmMap : EvmYul.AccountMap .EVM},
        CompiledAccountMapRel yulMap evmMap →
          cfg.accountMapRel yulMap evmMap)
    (parentStore childStore restoreStore : EvmYul.Yul.VarStore)
    {yulChild : EvmYul.SharedState .Yul}
    {targetChild evmChild : EVMState}
    {output : ByteArray}
    (hTargetChild :
      Reference.SharedStateRel cfg yulChild targetChild.toSharedState)
    (hTargetChildWorld :
      CompiledAccountMapRel yulChild.accountMap targetChild.accountMap)
    (hAgree :
      Assembly.GasAware.XResultAgrees (.running targetChild)
        (.success evmChild output))
    (hChildGas :
      cfg.gasAvailableRel yulChild.toMachineState.gasAvailable
        evmChild.gasAvailable)
    (inOffset inSize outOffset outSize : EvmYul.UInt256)
    {targetGas : EvmYul.UInt256}
    (hGas :
      cfg.gasAvailableRel
        (yulParent.toMachineState.finishExternalCall ByteArray.empty
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    ∃ yulAfter,
      EvmYul.Yul.restoreSuccessfulContractCallState
          (.Ok yulParent parentStore)
          (.Ok yulChild childStore)
          restoreStore ByteArray.empty inOffset inSize outOffset outSize =
        .ok (.Ok yulAfter restoreStore, [⟨1⟩]) ∧
      Reference.SharedStateRel cfg yulAfter
        { evmParent with
          toMachineState :=
            { evmParent.toMachineState.finishExternalCall output
                inOffset inSize outOffset outSize with
              gasAvailable := targetGas }
          accountMap :=
            if evmChild.accountMap.isEmpty then
              evmParent.accountMap
            else
              evmChild.accountMap
          substate :=
            if evmChild.accountMap.isEmpty then
              evmParent.substate
            else
              evmChild.substate
          createdAccounts := evmChild.createdAccounts } := by
  have hOutput := XResultAgrees_running_success_output_empty hAgree
  subst output
  exact
    restoreSuccessfulContractCallState_of_XResultAgrees_running_success
      hParent hParentWorld hCfgAccountMap
      parentStore childStore restoreStore hTargetChild hTargetChildWorld
      hAgree hChildGas inOffset inSize outOffset outSize hGas

theorem restoreSuccessfulContractCallState_of_XResultAgrees_halted_success
    {cfg : Reference.StateRelConfig}
    {yulParent : EvmYul.SharedState .Yul}
    {evmParent : EvmYul.SharedState .EVM}
    (hParent : Reference.SharedStateRel cfg yulParent evmParent)
    (hParentWorld :
      CompiledAccountMapRel yulParent.accountMap evmParent.accountMap)
    (hCfgAccountMap :
      ∀ {yulMap : EvmYul.AccountMap .Yul}
        {evmMap : EvmYul.AccountMap .EVM},
        CompiledAccountMapRel yulMap evmMap →
          cfg.accountMapRel yulMap evmMap)
    (parentStore childStore restoreStore : EvmYul.Yul.VarStore)
    {yulChild : EvmYul.SharedState .Yul}
    {halt : Assembly.Halt}
    {evmChild : EVMState}
    {returnData : ByteArray}
    (hTargetChild :
      Reference.SharedStateRel cfg yulChild halt.state.toSharedState)
    (hTargetChildWorld :
      CompiledAccountMapRel yulChild.accountMap halt.state.accountMap)
    (hAgree :
      Assembly.GasAware.XResultAgrees (.halted halt)
        (.success evmChild returnData))
    (hChildGas :
      cfg.gasAvailableRel yulChild.toMachineState.gasAvailable
        evmChild.gasAvailable)
    (inOffset inSize outOffset outSize : EvmYul.UInt256)
    {targetGas : EvmYul.UInt256}
    (hGas :
      cfg.gasAvailableRel
        (yulParent.toMachineState.finishExternalCall returnData
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    halt.kind ≠ .revert ∧
      ∃ yulAfter,
        EvmYul.Yul.restoreSuccessfulContractCallState
            (.Ok yulParent parentStore)
            (.Ok yulChild childStore)
            restoreStore returnData inOffset inSize outOffset outSize =
          .ok (.Ok yulAfter restoreStore, [⟨1⟩]) ∧
        Reference.SharedStateRel cfg yulAfter
          { evmParent with
            toMachineState :=
              { evmParent.toMachineState.finishExternalCall returnData
                  inOffset inSize outOffset outSize with
                gasAvailable := targetGas }
            accountMap :=
              if evmChild.accountMap.isEmpty then
                evmParent.accountMap
              else
                evmChild.accountMap
            substate :=
              if evmChild.accountMap.isEmpty then
                evmParent.substate
              else
                evmChild.substate
            createdAccounts := evmChild.createdAccounts } := by
  rcases hAgree with ⟨hNotRevert, hErase, _hOutput⟩
  exact
    ⟨hNotRevert,
      restoreSuccessfulContractCallState_childEvm_rel
        hParent hParentWorld hCfgAccountMap
        parentStore childStore restoreStore
        (sharedStateRel_of_eraseGas_eq hTargetChild hErase hChildGas)
        (hTargetChildWorld.of_eraseGas_eq hErase)
        returnData inOffset inSize outOffset outSize hGas⟩

theorem restoreSuccessfulContractCallState_of_XResultAgrees_halted_success_merge
    {cfg : Reference.StateRelConfig}
    {yulParent : EvmYul.SharedState .Yul}
    {evmParent : EvmYul.SharedState .EVM}
    (hParent : Reference.SharedStateRel cfg yulParent evmParent)
    (hParentWorld :
      CompiledAccountMapRel yulParent.accountMap evmParent.accountMap)
    (hCfgAccountMap :
      ∀ {yulMap : EvmYul.AccountMap .Yul}
        {evmMap : EvmYul.AccountMap .EVM},
        CompiledAccountMapRel yulMap evmMap →
          cfg.accountMapRel yulMap evmMap)
    (parentStore childStore restoreStore : EvmYul.Yul.VarStore)
    {yulChild : EvmYul.SharedState .Yul}
    {halt : Assembly.Halt}
    {evmChild : EVMState}
    {returnData : ByteArray}
    (hTargetChild :
      ExternalChildMergeRel yulChild halt.state.toSharedState)
    (hAgree :
      Assembly.GasAware.XResultAgrees (.halted halt)
        (.success evmChild returnData))
    (inOffset inSize outOffset outSize : EvmYul.UInt256)
    {targetGas : EvmYul.UInt256}
    (hGas :
      cfg.gasAvailableRel
        (yulParent.toMachineState.finishExternalCall returnData
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    halt.kind ≠ .revert ∧
      ∃ yulAfter,
        EvmYul.Yul.restoreSuccessfulContractCallState
            (.Ok yulParent parentStore)
            (.Ok yulChild childStore)
            restoreStore returnData inOffset inSize outOffset outSize =
          .ok (.Ok yulAfter restoreStore, [⟨1⟩]) ∧
        Reference.SharedStateRel cfg yulAfter
          { evmParent with
            toMachineState :=
              { evmParent.toMachineState.finishExternalCall returnData
                  inOffset inSize outOffset outSize with
                gasAvailable := targetGas }
            accountMap :=
              if evmChild.accountMap.isEmpty then
                evmParent.accountMap
              else
                evmChild.accountMap
            substate :=
              if evmChild.accountMap.isEmpty then
                evmParent.substate
              else
                evmChild.substate
            createdAccounts := evmChild.createdAccounts } := by
  rcases hAgree with ⟨hNotRevert, hErase, _hOutput⟩
  exact
    ⟨hNotRevert,
      restoreSuccessfulContractCallState_childMerge_rel
        hParent hParentWorld hCfgAccountMap
        parentStore childStore restoreStore
        (hTargetChild.of_eraseGas_eq hErase)
        returnData inOffset inSize outOffset outSize hGas⟩

theorem sharedStateRel_freshExternalCallWithWorld
    {cfg : Reference.StateRelConfig}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.SharedState .EVM}
    (hShared : Reference.SharedStateRel cfg yul evm)
    {yulAccountMap : EvmYul.AccountMap .Yul}
    {evmAccountMap : EvmYul.AccountMap .EVM}
    {yulSubstate evmSubstate : EvmYul.Substate}
    {yulEnv : EvmYul.ExecutionEnv .Yul}
    {evmEnv : EvmYul.ExecutionEnv .EVM}
    {yulCreated evmCreated : Batteries.RBSet EvmYul.AccountAddress compare}
    {yulGas evmGas : EvmYul.UInt256}
    (hAccountMap : cfg.accountMapRel yulAccountMap evmAccountMap)
    (hSubstate : yulSubstate = evmSubstate)
    (hExecutionEnv : Reference.ExecutionEnvRel cfg yulEnv evmEnv)
    (hCreated : yulCreated = evmCreated)
    (hGas : cfg.gasAvailableRel yulGas evmGas) :
    Reference.SharedStateRel cfg
      { yul with
        toMachineState := EvmYul.MachineState.freshExternalCall yulGas
        accountMap := yulAccountMap
        substate := yulSubstate
        executionEnv := yulEnv
        createdAccounts := yulCreated }
      { evm with
        toMachineState := EvmYul.MachineState.freshExternalCall evmGas
        accountMap := evmAccountMap
        substate := evmSubstate
        executionEnv := evmEnv
        createdAccounts := evmCreated } := by
  rcases hShared with ⟨hChain, _hMachine⟩
  rcases hChain with
    ⟨_hAccountMap, hSigma, hTotal, hReceipts, _hSubstate, _hEnv,
      hBlocks, hGenesis, _hCreated⟩
  constructor
  · constructor
    · exact hAccountMap
    · simpa using hSigma
    · simpa using hTotal
    · simpa using hReceipts
    · exact hSubstate
    · exact hExecutionEnv
    · simpa using hBlocks
    · simpa using hGenesis
    · exact hCreated
  · exact machineStateRel_freshExternalCall hGas

theorem sharedStateRel_freshExternalCallWithWorldFromFreshEvmFrame
    {cfg : Reference.StateRelConfig}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.SharedState .EVM}
    (hShared : Reference.SharedStateRel cfg yul evm)
    {yulAccountMap : EvmYul.AccountMap .Yul}
    {evmAccountMap : EvmYul.AccountMap .EVM}
    {yulSubstate evmSubstate : EvmYul.Substate}
    {yulEnv : EvmYul.ExecutionEnv .Yul}
    {evmEnv : EvmYul.ExecutionEnv .EVM}
    {yulCreated evmCreated : Batteries.RBSet EvmYul.AccountAddress compare}
    {yulGas evmGas : EvmYul.UInt256}
    (hAccountMap : cfg.accountMapRel yulAccountMap evmAccountMap)
    (hSubstate : yulSubstate = evmSubstate)
    (hExecutionEnv : Reference.ExecutionEnvRel cfg yulEnv evmEnv)
    (hCreated : yulCreated = evmCreated)
    (hGas : cfg.gasAvailableRel yulGas evmGas) :
    Reference.SharedStateRel cfg
      { yul with
        toMachineState := EvmYul.MachineState.freshExternalCall yulGas
        accountMap := yulAccountMap
        substate := yulSubstate
        executionEnv := yulEnv
        createdAccounts := yulCreated }
      ({ (default : EvmYul.EVM.State) with
        accountMap := evmAccountMap
        σ₀ := evm.σ₀
        totalGasUsedInBlock := evm.totalGasUsedInBlock
        transactionReceipts := evm.transactionReceipts
        substate := evmSubstate
        executionEnv := evmEnv
        blocks := evm.blocks
        genesisBlockHeader := evm.genesisBlockHeader
        createdAccounts := evmCreated
        toMachineState := EvmYul.MachineState.freshExternalCall evmGas }
        : EvmYul.EVM.State).toSharedState := by
  rcases hShared with ⟨hChain, _hMachine⟩
  rcases hChain with
    ⟨_hAccountMap, hSigma, hTotal, hReceipts, _hSubstate, _hEnv,
      hBlocks, hGenesis, _hCreated⟩
  constructor
  · constructor
    · exact hAccountMap
    · simpa using hSigma
    · simpa using hTotal
    · simpa using hReceipts
    · exact hSubstate
    · exact hExecutionEnv
    · simpa using hBlocks
    · simpa using hGenesis
    · exact hCreated
  · exact machineStateRel_freshExternalCall hGas

theorem sharedStateRel_callFrameFromFreshEvmFrame
    {cfg : Reference.StateRelConfig}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.SharedState .EVM}
    (hShared : Reference.SharedStateRel cfg yul evm)
    {yulAccountMap : EvmYul.AccountMap .Yul}
    {evmAccountMap : EvmYul.AccountMap .EVM}
    {yulSubstate evmSubstate : EvmYul.Substate}
    {yulCreated evmCreated : Batteries.RBSet EvmYul.AccountAddress compare}
    {yulGas evmGas : EvmYul.UInt256}
    {yulCode : AstContract} {evmCode : ByteArray}
    (hAccountMap : cfg.accountMapRel yulAccountMap evmAccountMap)
    (hSubstate : yulSubstate = evmSubstate)
    (hCode : cfg.codeRel yulCode evmCode)
    (hCreated : yulCreated = evmCreated)
    (hGas : cfg.gasAvailableRel yulGas evmGas)
    (codeOwner sender source : EvmYul.AccountAddress)
    (weiValue : EvmYul.UInt256)
    (calldata : ByteArray)
    (gasPrice depth : Nat)
      (header : EvmYul.BlockHeader)
      (perm : Bool)
      (blobVersionedHashes : List ByteArray)
      (yulCodeBytes evmCodeBytes : ByteArray)
      (hCodeBytes : yulCodeBytes = evmCode) :
    Reference.SharedStateRel cfg
      { yul with
        toMachineState := EvmYul.MachineState.freshExternalCall yulGas
        accountMap := yulAccountMap
        substate := yulSubstate
        executionEnv :=
          { codeOwner := codeOwner
            sender := sender
            source := source
            weiValue := weiValue
            calldata := calldata
            code := yulCode
            gasPrice := gasPrice
            header := header
            depth := depth
            perm := perm
            blobVersionedHashes := blobVersionedHashes
            codeBytes := yulCodeBytes }
        createdAccounts := yulCreated }
      ({ (default : EvmYul.EVM.State) with
        accountMap := evmAccountMap
        σ₀ := evm.σ₀
        totalGasUsedInBlock := evm.totalGasUsedInBlock
        transactionReceipts := evm.transactionReceipts
        substate := evmSubstate
        executionEnv :=
          { codeOwner := codeOwner
            sender := sender
            source := source
            weiValue := weiValue
            calldata := calldata
            code := evmCode
            gasPrice := gasPrice
            header := header
            depth := depth
            perm := perm
            blobVersionedHashes := blobVersionedHashes
            codeBytes := evmCodeBytes }
        blocks := evm.blocks
        genesisBlockHeader := evm.genesisBlockHeader
        createdAccounts := evmCreated
        toMachineState := EvmYul.MachineState.freshExternalCall evmGas }
        : EvmYul.EVM.State).toSharedState := by
  exact
    sharedStateRel_freshExternalCallWithWorldFromFreshEvmFrame hShared
      hAccountMap hSubstate
        (executionEnvRel_callFrame hCode codeOwner sender source weiValue
          calldata gasPrice depth header perm blobVersionedHashes
          yulCodeBytes evmCodeBytes hCodeBytes)
      hCreated hGas

def xiInitialState
    (createdAccounts : Batteries.RBSet EvmYul.AccountAddress compare)
    (genesisBlockHeader : EvmYul.BlockHeader)
    (blocks : EvmYul.ProcessedBlocks)
    (accountMap sigma0 : EvmYul.AccountMap .EVM)
    (chainContext : EvmYul.EVM.ChildFrameChainContext)
    (gas : EvmYul.UInt256) (substate : EvmYul.Substate)
    (env : EvmYul.ExecutionEnv .EVM) : EVMState :=
  { (default : EVMState) with
    accountMap := accountMap
    σ₀ := sigma0
    totalGasUsedInBlock := chainContext.totalGasUsedInBlock
    transactionReceipts := chainContext.transactionReceipts
    executionEnv := env
    substate := substate
    createdAccounts := createdAccounts
    gasAvailable := gas
    blocks := blocks
    genesisBlockHeader := genesisBlockHeader }

theorem xiInitialState_toSharedState_eq_freshExternalCall
    (createdAccounts : Batteries.RBSet EvmYul.AccountAddress compare)
    (genesisBlockHeader : EvmYul.BlockHeader)
    (blocks : EvmYul.ProcessedBlocks)
    (accountMap sigma0 : EvmYul.AccountMap .EVM)
    (chainContext : EvmYul.EVM.ChildFrameChainContext)
    (gas : EvmYul.UInt256) (substate : EvmYul.Substate)
    (env : EvmYul.ExecutionEnv .EVM) :
    (xiInitialState createdAccounts genesisBlockHeader blocks accountMap sigma0
        chainContext gas substate env).toSharedState =
      ({ (default : EVMState) with
        accountMap := accountMap
        σ₀ := sigma0
        totalGasUsedInBlock := chainContext.totalGasUsedInBlock
        transactionReceipts := chainContext.transactionReceipts
        substate := substate
        executionEnv := env
        blocks := blocks
        genesisBlockHeader := genesisBlockHeader
        createdAccounts := createdAccounts
        toMachineState := EvmYul.MachineState.freshExternalCall gas }
        : EVMState).toSharedState := by
  simp [xiInitialState, EvmYul.MachineState.freshExternalCall]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem sharedStateRel_freshExternalCallWithWorldFromXiInitialState
    {cfg : Reference.StateRelConfig}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.SharedState .EVM}
    (hShared : Reference.SharedStateRel cfg yul evm)
    {yulAccountMap : EvmYul.AccountMap .Yul}
    {evmAccountMap : EvmYul.AccountMap .EVM}
    {yulSubstate evmSubstate : EvmYul.Substate}
    {yulEnv : EvmYul.ExecutionEnv .Yul}
    {evmEnv : EvmYul.ExecutionEnv .EVM}
    {yulCreated evmCreated : Batteries.RBSet EvmYul.AccountAddress compare}
    {yulGas evmGas : EvmYul.UInt256}
    (hAccountMap : cfg.accountMapRel yulAccountMap evmAccountMap)
    (hSubstate : yulSubstate = evmSubstate)
    (hExecutionEnv : Reference.ExecutionEnvRel cfg yulEnv evmEnv)
    (hCreated : yulCreated = evmCreated)
    (hGas : cfg.gasAvailableRel yulGas evmGas) :
    Reference.SharedStateRel cfg
      { yul with
        toMachineState := EvmYul.MachineState.freshExternalCall yulGas
        accountMap := yulAccountMap
        substate := yulSubstate
        executionEnv := yulEnv
        createdAccounts := yulCreated }
      (xiInitialState evmCreated evm.genesisBlockHeader evm.blocks
        evmAccountMap evm.σ₀
        { totalGasUsedInBlock := evm.totalGasUsedInBlock
          transactionReceipts := evm.transactionReceipts }
        evmGas evmSubstate evmEnv).toSharedState := by
  rw [xiInitialState_toSharedState_eq_freshExternalCall]
  exact
    sharedStateRel_freshExternalCallWithWorldFromFreshEvmFrame hShared
      hAccountMap hSubstate hExecutionEnv hCreated hGas

theorem Xi_succ_eq_X
    (fuel : Nat)
    (createdAccounts : Batteries.RBSet EvmYul.AccountAddress compare)
    (genesisBlockHeader : EvmYul.BlockHeader)
    (blocks : EvmYul.ProcessedBlocks)
    (accountMap sigma0 : EvmYul.AccountMap .EVM)
    (chainContext : EvmYul.EVM.ChildFrameChainContext)
    (gas : EvmYul.UInt256) (substate : EvmYul.Substate)
    (env : EvmYul.ExecutionEnv .EVM) :
    EvmYul.EVM.Ξ fuel.succ createdAccounts genesisBlockHeader blocks
        accountMap sigma0 chainContext gas substate env =
      match EvmYul.EVM.X fuel (EvmYul.EVM.D_J env.code ⟨0⟩)
          (xiInitialState createdAccounts genesisBlockHeader blocks
            accountMap sigma0 chainContext gas substate env) with
      | .error err => .error err
      | .ok (.success evmState' output) =>
          .ok (.success
            (evmState'.createdAccounts, evmState'.accountMap,
              evmState'.gasAvailable, evmState'.substate) output)
      | .ok (.revert returnedGas output) =>
          .ok (.revert returnedGas output) := by
  simp only [EvmYul.EVM.Ξ]
  change
    (do
      let result ← EvmYul.EVM.X fuel (EvmYul.EVM.D_J env.code ⟨0⟩)
        (xiInitialState createdAccounts genesisBlockHeader blocks
          accountMap sigma0 chainContext gas substate env)
      match result with
      | EvmYul.EVM.ExecutionResult.success evmState' output =>
          .ok (EvmYul.EVM.ExecutionResult.success
            (evmState'.createdAccounts, evmState'.accountMap,
              evmState'.gasAvailable, evmState'.substate) output)
      | EvmYul.EVM.ExecutionResult.revert returnedGas output =>
          .ok (EvmYul.EVM.ExecutionResult.revert returnedGas output)) =
    _
  cases EvmYul.EVM.X fuel (EvmYul.EVM.D_J env.code ⟨0⟩)
      (xiInitialState createdAccounts genesisBlockHeader blocks
        accountMap sigma0 chainContext gas substate env) with
  | error err => rfl
  | ok result =>
      cases result <;> rfl

theorem Xi_emptyCode_STOP_success
    {fuel : Nat}
    {createdAccounts : Batteries.RBSet EvmYul.AccountAddress compare}
    {genesisBlockHeader : EvmYul.BlockHeader}
    {blocks : EvmYul.ProcessedBlocks}
    {accountMap sigma0 : EvmYul.AccountMap .EVM}
    {chainContext : EvmYul.EVM.ChildFrameChainContext}
    {gas : EvmYul.UInt256}
    {substate : EvmYul.Substate}
    {env : EvmYul.ExecutionEnv .EVM}
    (hCode : env.code = default) :
    EvmYul.EVM.Ξ fuel.succ.succ.succ createdAccounts genesisBlockHeader
        blocks accountMap sigma0 chainContext gas substate env =
      .ok (.success (createdAccounts, accountMap, gas, substate)
        ByteArray.empty) := by
  rw [Xi_succ_eq_X]
  rw [EVM_X_emptyCode_STOP_success]
  · simp [EVM_stopState, xiInitialState,
      EvmYul.MachineState.setReturnData, EvmYul.MachineState.setHReturn]
  · simp [xiInitialState, hCode]
  · rfl

theorem xiInitialState_eq_installCodeAndGas
    (target : Assembly.TargetProgram) (gasNat : Nat)
    (createdAccounts : Batteries.RBSet EvmYul.AccountAddress compare)
    (genesisBlockHeader : EvmYul.BlockHeader)
    (blocks : EvmYul.ProcessedBlocks)
    (accountMap sigma0 : EvmYul.AccountMap .EVM)
    (chainContext : EvmYul.EVM.ChildFrameChainContext)
    (initialGas : EvmYul.UInt256) (substate : EvmYul.Substate)
    (env : EvmYul.ExecutionEnv .EVM) :
    xiInitialState createdAccounts genesisBlockHeader blocks accountMap sigma0
        chainContext (EvmYul.UInt256.ofNat gasNat) substate
        { env with code := Assembly.Bytecode.encodeTarget target } =
      Assembly.GasAware.installCodeAndGas target gasNat
        { xiInitialState createdAccounts genesisBlockHeader blocks accountMap
            sigma0 chainContext initialGas substate env with
          pc := Assembly.Program.pcAfter []
          stack := [] } := by
  simp [xiInitialState, Assembly.GasAware.installCodeAndGas,
    Assembly.Program.pcAfter]
  constructor <;> rfl

theorem Xi_succ_eq_X_installedCode
    (fuel gasNat : Nat)
    (createdAccounts : Batteries.RBSet EvmYul.AccountAddress compare)
    (genesisBlockHeader : EvmYul.BlockHeader)
    (blocks : EvmYul.ProcessedBlocks)
    (accountMap sigma0 : EvmYul.AccountMap .EVM)
    (chainContext : EvmYul.EVM.ChildFrameChainContext)
    (initialGas : EvmYul.UInt256) (substate : EvmYul.Substate)
    (env : EvmYul.ExecutionEnv .EVM)
    (target : Assembly.TargetProgram) :
    EvmYul.EVM.Ξ fuel.succ createdAccounts genesisBlockHeader blocks
        accountMap sigma0 chainContext (EvmYul.UInt256.ofNat gasNat) substate
        { env with code := Assembly.Bytecode.encodeTarget target } =
      match EvmYul.EVM.X fuel (Assembly.GasAware.validJumps target)
          (Assembly.GasAware.installCodeAndGas target gasNat
            { xiInitialState createdAccounts genesisBlockHeader blocks
                accountMap sigma0 chainContext initialGas substate env with
              pc := Assembly.Program.pcAfter []
              stack := [] }) with
      | .error err => .error err
      | .ok (.success evmState' output) =>
          .ok (.success
            (evmState'.createdAccounts, evmState'.accountMap,
              evmState'.gasAvailable, evmState'.substate) output)
      | .ok (.revert returnedGas output) =>
          .ok (.revert returnedGas output) := by
  rw [Xi_succ_eq_X]
  rw [xiInitialState_eq_installCodeAndGas (initialGas := initialGas)]
  have hZero : (⟨0⟩ : EvmYul.UInt256) = EvmYul.UInt256.ofNat 0 := rfl
  simp [Assembly.GasAware.validJumps, hZero]

theorem Theta_code_succ_eq_Xi
    (fuel : Nat)
    (blobVersionedHashes : List ByteArray)
    (createdAccounts : Batteries.RBSet EvmYul.AccountAddress compare)
    (genesisBlockHeader : EvmYul.BlockHeader)
    (blocks : EvmYul.ProcessedBlocks)
    (accountMap sigma0 : EvmYul.AccountMap .EVM)
    (chainContext : EvmYul.EVM.ChildFrameChainContext)
    (substate : EvmYul.Substate)
    (source origin recipient : EvmYul.AccountAddress)
    (code : ByteArray)
    (gas gasPrice value weiValue : EvmYul.UInt256)
    (calldata : ByteArray)
    (depth : Nat)
    (header : EvmYul.BlockHeader)
    (perm : Bool) :
    EvmYul.EVM.Θ fuel.succ blobVersionedHashes createdAccounts
        genesisBlockHeader blocks accountMap sigma0 chainContext substate
        source origin recipient (.Code code) gas gasPrice value weiValue
        calldata depth header perm =
      match EvmYul.EVM.Ξ fuel createdAccounts genesisBlockHeader blocks
          (EvmYul.EVM.thetaCallTransfer accountMap source recipient value)
          sigma0 chainContext gas substate
          (EvmYul.EVM.thetaCallExecutionEnv blobVersionedHashes source origin
            recipient (.Code code) gasPrice weiValue calldata depth header
            perm) with
      | .error err =>
          if err == EvmYul.EVM.ExecutionException.OutOfFuel then
            .error EvmYul.EVM.ExecutionException.OutOfFuel
          else
            .ok (createdAccounts, accountMap, ⟨0⟩, substate, false,
              ByteArray.empty)
      | .ok (.revert returnedGas output) =>
          .ok (createdAccounts, accountMap, returnedGas, substate, false,
            output)
      | .ok (.success (createdAccounts', accountMap', returnedGas,
          substate') output) =>
          .ok (createdAccounts',
            if accountMap'.isEmpty then accountMap else accountMap',
            returnedGas,
            if accountMap'.isEmpty then substate else substate',
            true, output) := by
  simp only [EvmYul.EVM.Θ]
  generalize hChild :
    EvmYul.EVM.Ξ fuel createdAccounts genesisBlockHeader blocks
      (EvmYul.EVM.thetaCallTransfer accountMap source recipient value)
      sigma0 chainContext gas substate
      (EvmYul.EVM.thetaCallExecutionEnv blobVersionedHashes source origin
        recipient (EvmYul.ToExecute.Code code) gasPrice weiValue calldata
        depth header perm) = child
  cases child with
  | error err =>
      by_cases hErr : err == EvmYul.EVM.ExecutionException.OutOfFuel
      · simp [hErr]
        rfl
      · simp [hErr]
  | ok result =>
      cases result with
      | success data output =>
          rcases data with
            ⟨createdAccounts', accountMap', returnedGas, substate'⟩
          simp
      | revert returnedGas output =>
          simp

theorem Theta_emptyCode_STOP_success
    (fuel : Nat)
    (blobVersionedHashes : List ByteArray)
    (createdAccounts : Batteries.RBSet EvmYul.AccountAddress compare)
    (genesisBlockHeader : EvmYul.BlockHeader)
    (blocks : EvmYul.ProcessedBlocks)
    (accountMap sigma0 : EvmYul.AccountMap .EVM)
    (chainContext : EvmYul.EVM.ChildFrameChainContext)
    (substate : EvmYul.Substate)
    (source origin recipient : EvmYul.AccountAddress)
    (gas gasPrice value weiValue : EvmYul.UInt256)
    (calldata : ByteArray)
    (depth : Nat)
    (header : EvmYul.BlockHeader)
    (perm : Bool) :
    let accountMapAfter :=
      EvmYul.EVM.thetaCallTransfer accountMap source recipient value
    EvmYul.EVM.Θ fuel.succ.succ.succ.succ blobVersionedHashes
        createdAccounts genesisBlockHeader blocks accountMap sigma0
        chainContext substate source origin recipient (.Code default)
        gas gasPrice value weiValue calldata depth header perm =
      .ok (createdAccounts,
        if accountMapAfter.isEmpty then accountMap else accountMapAfter,
        gas, substate, true, ByteArray.empty) := by
  dsimp
  rw [Theta_code_succ_eq_Xi]
  rw [Xi_emptyCode_STOP_success]
  · simp
  · simp [EvmYul.EVM.thetaCallExecutionEnv]

theorem EVM_call_noCode_success_eq
    {fuel gasCost : Nat}
    {blobVersionedHashes : List ByteArray}
    {evm : EvmYul.EVM.State}
    {gas address value inOffset inSize outOffset outSize : EvmYul.UInt256}
    (hEnough :
      value ≤
        (evm.accountMap.find? evm.executionEnv.codeOwner |>.option ⟨0⟩
          (·.balance)))
    (hDepth : evm.executionEnv.depth < 1024)
    (hNotPrecompile :
      EvmYul.PrecompiledContract.ofAddress?
        (EvmYul.AccountAddress.ofUInt256 address) = none)
    (hMissing :
      evm.accountMap.find?
        (EvmYul.AccountAddress.ofUInt256 address) = none) :
    let target := EvmYul.AccountAddress.ofUInt256 address
    let callMap :=
      evmCallTransfer evm.accountMap evm.executionEnv.codeOwner target value
    let callGas :=
      EvmYul.EVM.Ccallgas target target value gas evm.accountMap
        evm.toMachineState evm.substate
    let charged : EvmYul.EVM.State :=
      { evm with gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
    let targetGas :=
      (charged.toMachineState.finishExternalCall ByteArray.empty
        inOffset inSize outOffset outSize).gasAvailable +
        EvmYul.UInt256.ofNat callGas
    EvmYul.EVM.call fuel.succ.succ.succ.succ.succ gasCost
        blobVersionedHashes gas
        (EvmYul.UInt256.ofNat evm.executionEnv.codeOwner) address address
        value value inOffset inSize outOffset outSize evm.executionEnv.perm
        evm =
      .ok (⟨1⟩,
        { charged with
          toMachineState :=
            { charged.toMachineState.finishExternalCall ByteArray.empty
                inOffset inSize outOffset outSize with
              gasAvailable := targetGas }
          accountMap :=
            if callMap.isEmpty then evm.accountMap else callMap
          substate :=
            (EvmYul.State.addAccessedAccount charged.toState target).substate }) := by
  dsimp
  have hSource :
      EvmYul.AccountAddress.ofUInt256
          (EvmYul.UInt256.ofNat evm.executionEnv.codeOwner) =
        evm.executionEnv.codeOwner :=
    AccountAddress_ofUInt256_ofNat evm.executionEnv.codeOwner
  have hFuel : fuel + 4 = fuel.succ.succ.succ.succ := by
    omega
  simp [EvmYul.EVM.call, hEnough, hDepth, EvmYul.toExecute,
    hNotPrecompile, hMissing, hSource]
  rw [hFuel]
  rw [show
    (Id.run (EvmYul.ToExecute.Code default) :
      EvmYul.ToExecute .EVM) = EvmYul.ToExecute.Code default from rfl]
  rw [Theta_emptyCode_STOP_success]
  have hNotLt :
      ¬ ((evm.accountMap.find? evm.executionEnv.codeOwner).elim
          ⟨0⟩ fun account => account.balance) < value := by
    intro hLt
    cases hFind : evm.accountMap.find? evm.executionEnv.codeOwner with
    | none =>
        simp [hFind, Option.option] at hEnough hLt
        change value.val ≤ 0 at hEnough
        change 0 < value.val at hLt
        omega
    | some account =>
        simp [hFind, Option.option] at hEnough hLt
        change value.val ≤ account.balance.val at hEnough
        change account.balance.val < value.val at hLt
        omega
  have hNotDepthEq : ¬ evm.executionEnv.depth = 1024 := by
    omega
  simp [evmCallTransfer_eq_thetaCallTransfer, hNotLt, hNotDepthEq]

theorem EVM_call_existingDefaultCode_success_eq
    {fuel gasCost : Nat}
    {blobVersionedHashes : List ByteArray}
    {evm : EvmYul.EVM.State}
    {gas address value inOffset inSize outOffset outSize : EvmYul.UInt256}
    {evmRecipient : EvmYul.Account .EVM}
    (hEnough :
      value ≤
        (evm.accountMap.find? evm.executionEnv.codeOwner |>.option ⟨0⟩
          (·.balance)))
    (hDepth : evm.executionEnv.depth < 1024)
    (hNotPrecompile :
      EvmYul.PrecompiledContract.ofAddress?
        (EvmYul.AccountAddress.ofUInt256 address) = none)
    (hFind :
      evm.accountMap.find?
        (EvmYul.AccountAddress.ofUInt256 address) = some evmRecipient)
    (hCode : evmRecipient.code = default) :
    let target := EvmYul.AccountAddress.ofUInt256 address
    let callMap :=
      evmCallTransfer evm.accountMap evm.executionEnv.codeOwner target value
    let callGas :=
      EvmYul.EVM.Ccallgas target target value gas evm.accountMap
        evm.toMachineState evm.substate
    let charged : EvmYul.EVM.State :=
      { evm with gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
    let targetGas :=
      (charged.toMachineState.finishExternalCall ByteArray.empty
        inOffset inSize outOffset outSize).gasAvailable +
        EvmYul.UInt256.ofNat callGas
    EvmYul.EVM.call fuel.succ.succ.succ.succ.succ gasCost
        blobVersionedHashes gas
        (EvmYul.UInt256.ofNat evm.executionEnv.codeOwner) address address
        value value inOffset inSize outOffset outSize evm.executionEnv.perm
        evm =
      .ok (⟨1⟩,
        { charged with
          toMachineState :=
            { charged.toMachineState.finishExternalCall ByteArray.empty
                inOffset inSize outOffset outSize with
              gasAvailable := targetGas }
          accountMap :=
            if callMap.isEmpty then evm.accountMap else callMap
          substate :=
            (EvmYul.State.addAccessedAccount charged.toState target).substate }) := by
  dsimp
  have hSource :
      EvmYul.AccountAddress.ofUInt256
          (EvmYul.UInt256.ofNat evm.executionEnv.codeOwner) =
        evm.executionEnv.codeOwner :=
    AccountAddress_ofUInt256_ofNat evm.executionEnv.codeOwner
  have hFuel : fuel + 4 = fuel.succ.succ.succ.succ := by
    omega
  simp [EvmYul.EVM.call, hEnough, hDepth, EvmYul.toExecute,
    hNotPrecompile, hFind, hCode, hSource]
  rw [hFuel]
  rw [show
    (Id.run (EvmYul.ToExecute.Code default) :
      EvmYul.ToExecute .EVM) = EvmYul.ToExecute.Code default from rfl]
  rw [Theta_emptyCode_STOP_success]
  have hNotLt :
      ¬ ((evm.accountMap.find? evm.executionEnv.codeOwner).elim
          ⟨0⟩ fun account => account.balance) < value := by
    intro hLt
    cases hFindOwner : evm.accountMap.find? evm.executionEnv.codeOwner with
    | none =>
        simp [hFindOwner, Option.option] at hEnough hLt
        change value.val ≤ 0 at hEnough
        change 0 < value.val at hLt
        omega
    | some account =>
        simp [hFindOwner, Option.option] at hEnough hLt
        change value.val ≤ account.balance.val at hEnough
        change account.balance.val < value.val at hLt
        omega
  have hNotDepthEq : ¬ evm.executionEnv.depth = 1024 := by
    omega
  simp [evmCallTransfer_eq_thetaCallTransfer, hNotLt, hNotDepthEq]

theorem callDispatcher_defaultCode_ok
    {fuel : Nat} {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    (hCode : shared.executionEnv.code = (default : AstContract)) :
    EvmYul.Yul.callDispatcher fuel.succ.succ.succ.succ.succ
        (some (default : AstContract)) (.Ok shared store) =
      .ok (.Ok shared store, []) := by
  rw [Reference.Imported.callDispatcher_succ]
  simp [EvmYul.Yul.State.executionEnv, EvmYul.Yul.State.initcall,
    EvmYul.Yul.State.mkOk, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.zeroFill, EvmYul.Yul.State.multifill,
    EvmYul.Yul.Ast.FunctionDefinition.params,
    EvmYul.Yul.Ast.FunctionDefinition.rets,
    EvmYul.Yul.Ast.FunctionDefinition.body, hCode]
  rw [show (default : AstContract).dispatcher =
    EvmYul.Yul.Ast.Stmt.Block [] from rfl]
  have hFuel : fuel + 3 + 1 = fuel.succ.succ.succ.succ := by
    omega
  rw [hFuel]
  rw [Reference.SourceBridgeFacts.exec_block_block_empty_succ_succ_succ_succ]
  simp [EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?]

theorem call_noCode_emptyReturn_rel
    {cfg : Reference.StateRelConfig}
    {fuel gasCost : Nat}
    {blobVersionedHashes : List ByteArray}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.EVM.State}
    (hShared : Reference.SharedStateRel cfg yul evm.toSharedState)
    (hParentWorld : CompiledAccountMapRel yul.accountMap evm.accountMap)
    (hCfgAccountMap :
      ∀ {yulMap : EvmYul.AccountMap .Yul}
        {evmMap : EvmYul.AccountMap .EVM},
        CompiledAccountMapRel yulMap evmMap →
          cfg.accountMapRel yulMap evmMap)
    (store : EvmYul.Yul.VarStore)
    {gas address value inOffset inSize outOffset outSize : EvmYul.UInt256}
    (hEnough :
      value ≤
        (evm.accountMap.find? evm.executionEnv.codeOwner |>.option ⟨0⟩
          (·.balance)))
    (hDepth : evm.executionEnv.depth < 1024)
    (hNotPrecompile :
      EvmYul.PrecompiledContract.ofAddress?
        (EvmYul.AccountAddress.ofUInt256 address) = none)
    (hMissing :
      evm.accountMap.find?
        (EvmYul.AccountAddress.ofUInt256 address) = none)
    (hGas :
      let target := EvmYul.AccountAddress.ofUInt256 address
      let callGas :=
        EvmYul.EVM.Ccallgas target target value gas evm.accountMap
          evm.toMachineState evm.substate
      let charged : EvmYul.EVM.State :=
        { evm with
          gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
      let targetGas :=
        (charged.toMachineState.finishExternalCall ByteArray.empty
          inOffset inSize outOffset outSize).gasAvailable +
          EvmYul.UInt256.ofNat callGas
      cfg.gasAvailableRel
        (yul.toMachineState.finishExternalCall ByteArray.empty
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    let target := EvmYul.AccountAddress.ofUInt256 address
    let callMap :=
      evmCallTransfer evm.accountMap evm.executionEnv.codeOwner target value
    let callGas :=
      EvmYul.EVM.Ccallgas target target value gas evm.accountMap
        evm.toMachineState evm.substate
    let charged : EvmYul.EVM.State :=
      { evm with gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
    let targetGas :=
      (charged.toMachineState.finishExternalCall ByteArray.empty
        inOffset inSize outOffset outSize).gasAvailable +
        EvmYul.UInt256.ofNat callGas
    let evmAfter : EvmYul.EVM.State :=
      { charged with
        toMachineState :=
          { charged.toMachineState.finishExternalCall ByteArray.empty
              inOffset inSize outOffset outSize with
            gasAvailable := targetGas }
        accountMap :=
          if callMap.isEmpty then evm.accountMap else callMap
        substate :=
          (EvmYul.State.addAccessedAccount charged.toState target).substate }
    EvmYul.EVM.call fuel.succ.succ.succ.succ.succ gasCost
        blobVersionedHashes gas
        (EvmYul.UInt256.ofNat evm.executionEnv.codeOwner) address address
        value value inOffset inSize outOffset outSize evm.executionEnv.perm
        evm =
      .ok (⟨1⟩, evmAfter) ∧
      ∃ yulCallMap,
        EvmYul.Yul.callTransferAccountMap? yul.accountMap
            yul.executionEnv.codeOwner target value =
          some yulCallMap ∧
        CompiledAccountMapRel yulCallMap
          (if callMap.isEmpty then evm.accountMap else callMap) ∧
        yul.accountMap.find? target = none ∧
        EvmYul.PrecompiledContract.ofAddress? target = none ∧
        ∃ yulAfter,
          EvmYul.Yul.buildContractCallEmptyReturnState
              (EvmYul.Yul.addAccessedAccount (.Ok yul store) target)
              (some yulCallMap)
              inOffset inSize outOffset outSize ⟨1⟩ =
            .ok (.Ok yulAfter store, [⟨1⟩]) ∧
          Reference.SharedStateRel cfg yulAfter evmAfter.toSharedState := by
  dsimp at hGas ⊢
  constructor
  · exact
      EVM_call_noCode_success_eq hEnough hDepth hNotPrecompile hMissing
  · have hOwner :
        yul.executionEnv.codeOwner = evm.executionEnv.codeOwner := by
      rcases hShared with ⟨hChain, _hMachine⟩
      simpa using hChain.executionEnv.codeOwner
    have hMissingYul :
        yul.accountMap.find? (EvmYul.AccountAddress.ofUInt256 address) =
          none :=
      hParentWorld.not_find_yul_of_not_find_evm hMissing
    rcases
        hParentWorld.callTransferAccountMap?_of_evm_enough_merge
          (source := yul.executionEnv.codeOwner)
          (recipient := EvmYul.AccountAddress.ofUInt256 address)
          (value := value)
          (by simpa [hOwner] using hEnough) with
      ⟨yulCallMap, hTransfer, hCallMapRel⟩
    refine ⟨yulCallMap, hTransfer, ?_, hMissingYul, hNotPrecompile, ?_⟩
    · simpa [hOwner] using hCallMapRel
    · exact
        buildContractCallEmptyReturnState_afterAccess_some_rel
          hShared store (EvmYul.AccountAddress.ofUInt256 address)
          (hCfgAccountMap (by simpa [hOwner] using hCallMapRel))
          inOffset inSize outOffset outSize ⟨1⟩ hGas

theorem primCall_CALL_noCode_emptyReturn_rel
    {cfg : Reference.StateRelConfig}
    {fuel gasCost : Nat}
    {blobVersionedHashes : List ByteArray}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.EVM.State}
    (hShared : Reference.SharedStateRel cfg yul evm.toSharedState)
    (hParentWorld : CompiledAccountMapRel yul.accountMap evm.accountMap)
    (hCfgAccountMap :
      ∀ {yulMap : EvmYul.AccountMap .Yul}
        {evmMap : EvmYul.AccountMap .EVM},
        CompiledAccountMapRel yulMap evmMap →
          cfg.accountMapRel yulMap evmMap)
    (store : EvmYul.Yul.VarStore)
    {gas address value inOffset inSize outOffset outSize : EvmYul.UInt256}
    (hStaticAllowed :
      ¬ (¬ yul.executionEnv.perm ∧ value ≠ ⟨0⟩))
    (hEnough :
      value ≤
        (evm.accountMap.find? evm.executionEnv.codeOwner |>.option ⟨0⟩
          (·.balance)))
    (hDepth : evm.executionEnv.depth < 1024)
    (hNotPrecompile :
      EvmYul.PrecompiledContract.ofAddress?
        (EvmYul.AccountAddress.ofUInt256 address) = none)
    (hMissing :
      evm.accountMap.find?
        (EvmYul.AccountAddress.ofUInt256 address) = none)
    (hGas :
      let target := EvmYul.AccountAddress.ofUInt256 address
      let callGas :=
        EvmYul.EVM.Ccallgas target target value gas evm.accountMap
          evm.toMachineState evm.substate
      let charged : EvmYul.EVM.State :=
        { evm with
          gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
      let targetGas :=
        (charged.toMachineState.finishExternalCall ByteArray.empty
          inOffset inSize outOffset outSize).gasAvailable +
          EvmYul.UInt256.ofNat callGas
      cfg.gasAvailableRel
        (yul.toMachineState.finishExternalCall ByteArray.empty
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    let target := EvmYul.AccountAddress.ofUInt256 address
    let callMap :=
      evmCallTransfer evm.accountMap evm.executionEnv.codeOwner target value
    let callGas :=
      EvmYul.EVM.Ccallgas target target value gas evm.accountMap
        evm.toMachineState evm.substate
    let charged : EvmYul.EVM.State :=
      { evm with gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
    let targetGas :=
      (charged.toMachineState.finishExternalCall ByteArray.empty
        inOffset inSize outOffset outSize).gasAvailable +
        EvmYul.UInt256.ofNat callGas
    let evmAfter : EvmYul.EVM.State :=
      { charged with
        toMachineState :=
          { charged.toMachineState.finishExternalCall ByteArray.empty
              inOffset inSize outOffset outSize with
            gasAvailable := targetGas }
        accountMap :=
          if callMap.isEmpty then evm.accountMap else callMap
        substate :=
          (EvmYul.State.addAccessedAccount charged.toState target).substate }
    EvmYul.EVM.call fuel.succ.succ.succ.succ.succ gasCost
        blobVersionedHashes gas
        (EvmYul.UInt256.ofNat evm.executionEnv.codeOwner) address address
        value value inOffset inSize outOffset outSize evm.executionEnv.perm
        evm =
      .ok (⟨1⟩, evmAfter) ∧
      ∃ yulAfter,
        EvmYul.Yul.primCall fuel.succ (.Ok yul store) .CALL
            [gas, address, value, inOffset, inSize, outOffset, outSize] =
          .ok (.Ok yulAfter store, [⟨1⟩]) ∧
        Reference.SharedStateRel cfg yulAfter evmAfter.toSharedState := by
  dsimp at hGas ⊢
  rcases
      call_noCode_emptyReturn_rel hShared hParentWorld hCfgAccountMap store
        hEnough hDepth hNotPrecompile hMissing hGas with
    ⟨hEvm, yulCallMap, hTransfer, _hCallMapRel, hMissingYul,
      hNotPrecompileYul, yulAfter, hBuild, hRel⟩
  refine ⟨hEvm, yulAfter, ?_, hRel⟩
  have hDepthEq :
      yul.executionEnv.depth = evm.executionEnv.depth := by
    rcases hShared with ⟨hChain, _hMachine⟩
    simpa using hChain.executionEnv.depth
  have hNotDepthLimit : ¬ yul.executionEnv.depth ≥ 1024 := by
    omega
  have hStaticAllowed' :
      ¬ (yul.executionEnv.perm = false ∧ ¬ value = ⟨0⟩) := by
    intro hStatic
    exact hStaticAllowed (by simpa using hStatic)
  simpa [EvmYul.Yul.primCall, hStaticAllowed', hTransfer,
    hNotDepthLimit, hNotPrecompileYul, hMissingYul,
    EvmYul.toExecute, EvmYul.Yul.addAccessedAccount,
    EvmYul.Yul.State.sharedState,
    EvmYul.Yul.State.executionEnv,
    EvmYul.Yul.State.setState, EvmYul.Yul.State.toState,
    EvmYul.Yul.State.toSharedState, EvmYul.Yul.State.toMachineState] using
    hBuild

theorem primCall_CALL_noCode_emptyReturn_rel_stateRelConfig
    {varStackRel : Reference.VarStackRel}
    {terminalCfgRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop}
    {revertCfgRel : Reference.State → EVMState → Prop}
    {gasAvailableRel : Word → Word → Prop}
    {gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm}
    {totalGasRel : Nat → Nat → Prop}
    {fuel gasCost : Nat}
    {blobVersionedHashes : List ByteArray}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.EVM.State}
    (hShared :
      Reference.SharedStateRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        yul evm.toSharedState)
    (store : EvmYul.Yul.VarStore)
    {gas address value inOffset inSize outOffset outSize : EvmYul.UInt256}
    (hStaticAllowed :
      ¬ (¬ yul.executionEnv.perm ∧ value ≠ ⟨0⟩))
    (hEnough :
      value ≤
        (evm.accountMap.find? evm.executionEnv.codeOwner |>.option ⟨0⟩
          (·.balance)))
    (hDepth : evm.executionEnv.depth < 1024)
    (hNotPrecompile :
      EvmYul.PrecompiledContract.ofAddress?
        (EvmYul.AccountAddress.ofUInt256 address) = none)
    (hMissing :
      evm.accountMap.find?
        (EvmYul.AccountAddress.ofUInt256 address) = none)
    (hGas :
      let target := EvmYul.AccountAddress.ofUInt256 address
      let callGas :=
        EvmYul.EVM.Ccallgas target target value gas evm.accountMap
          evm.toMachineState evm.substate
      let charged : EvmYul.EVM.State :=
        { evm with
          gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
      let targetGas :=
        (charged.toMachineState.finishExternalCall ByteArray.empty
          inOffset inSize outOffset outSize).gasAvailable +
          EvmYul.UInt256.ofNat callGas
      gasAvailableRel
        (yul.toMachineState.finishExternalCall ByteArray.empty
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    let target := EvmYul.AccountAddress.ofUInt256 address
    let callMap :=
      evmCallTransfer evm.accountMap evm.executionEnv.codeOwner target value
    let callGas :=
      EvmYul.EVM.Ccallgas target target value gas evm.accountMap
        evm.toMachineState evm.substate
    let charged : EvmYul.EVM.State :=
      { evm with gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
    let targetGas :=
      (charged.toMachineState.finishExternalCall ByteArray.empty
        inOffset inSize outOffset outSize).gasAvailable +
        EvmYul.UInt256.ofNat callGas
    let evmAfter : EvmYul.EVM.State :=
      { charged with
        toMachineState :=
          { charged.toMachineState.finishExternalCall ByteArray.empty
              inOffset inSize outOffset outSize with
            gasAvailable := targetGas }
        accountMap :=
          if callMap.isEmpty then evm.accountMap else callMap
        substate :=
          (EvmYul.State.addAccessedAccount charged.toState target).substate }
    EvmYul.EVM.call fuel.succ.succ.succ.succ.succ gasCost
        blobVersionedHashes gas
        (EvmYul.UInt256.ofNat evm.executionEnv.codeOwner) address address
        value value inOffset inSize outOffset outSize evm.executionEnv.perm
        evm =
      .ok (⟨1⟩, evmAfter) ∧
      ∃ yulAfter,
        EvmYul.Yul.primCall fuel.succ (.Ok yul store) .CALL
            [gas, address, value, inOffset, inSize, outOffset, outSize] =
          .ok (.Ok yulAfter store, [⟨1⟩]) ∧
        Reference.SharedStateRel
          (stateRelConfig varStackRel terminalCfgRel revertCfgRel
            gasAvailableRel gasValueRel totalGasRel)
          yulAfter evmAfter.toSharedState := by
  exact
    primCall_CALL_noCode_emptyReturn_rel
      (cfg :=
        stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
      hShared
      (compiledAccountMapRel_of_sharedStateRel_stateRelConfig hShared)
      (fun hRel => stateRelConfig_accountMapRel_of_compiledAccountMapRel hRel)
      store hStaticAllowed hEnough hDepth hNotPrecompile hMissing hGas

theorem CALLPrimitiveRel.noCode_stateRelConfig
    {varStackRel : Reference.VarStackRel}
    {terminalCfgRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop}
    {revertCfgRel : Reference.State → EVMState → Prop}
    {gasAvailableRel : Word → Word → Prop}
    {gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm}
    {totalGasRel : Nat → Nat → Prop}
    {fuel gasCost : Nat}
    {blobVersionedHashes : List ByteArray}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.EVM.State}
    (hShared :
      Reference.SharedStateRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        yul evm.toSharedState)
    (store : EvmYul.Yul.VarStore)
    {gas address value inOffset inSize outOffset outSize : EvmYul.UInt256}
    (hStaticAllowed :
      ¬ (¬ yul.executionEnv.perm ∧ value ≠ ⟨0⟩))
    (hEnough :
      value ≤
        (evm.accountMap.find? evm.executionEnv.codeOwner |>.option ⟨0⟩
          (·.balance)))
    (hDepth : evm.executionEnv.depth < 1024)
    (hNotPrecompile :
      EvmYul.PrecompiledContract.ofAddress?
        (EvmYul.AccountAddress.ofUInt256 address) = none)
    (hMissing :
      evm.accountMap.find?
        (EvmYul.AccountAddress.ofUInt256 address) = none)
    (hGas :
      let target := EvmYul.AccountAddress.ofUInt256 address
      let callGas :=
        EvmYul.EVM.Ccallgas target target value gas evm.accountMap
          evm.toMachineState evm.substate
      let charged : EvmYul.EVM.State :=
        { evm with
          gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
      let targetGas :=
        (charged.toMachineState.finishExternalCall ByteArray.empty
          inOffset inSize outOffset outSize).gasAvailable +
          EvmYul.UInt256.ofNat callGas
      gasAvailableRel
        (yul.toMachineState.finishExternalCall ByteArray.empty
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    CALLPrimitiveRel
      (stateRelConfig varStackRel terminalCfgRel revertCfgRel
        gasAvailableRel gasValueRel totalGasRel)
      fuel.succ fuel.succ.succ.succ.succ.succ gasCost
      blobVersionedHashes yul evm store
      gas address value inOffset inSize outOffset outSize := by
  let target := EvmYul.AccountAddress.ofUInt256 address
  let callMap :=
    evmCallTransfer evm.accountMap evm.executionEnv.codeOwner target value
  let callGas :=
    EvmYul.EVM.Ccallgas target target value gas evm.accountMap
      evm.toMachineState evm.substate
  let charged : EvmYul.EVM.State :=
    { evm with gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
  let targetGas :=
    (charged.toMachineState.finishExternalCall ByteArray.empty
      inOffset inSize outOffset outSize).gasAvailable +
      EvmYul.UInt256.ofNat callGas
  let evmAfter : EvmYul.EVM.State :=
    { charged with
      toMachineState :=
        { charged.toMachineState.finishExternalCall ByteArray.empty
            inOffset inSize outOffset outSize with
          gasAvailable := targetGas }
      accountMap :=
        if callMap.isEmpty then evm.accountMap else callMap
      substate :=
        (EvmYul.State.addAccessedAccount charged.toState target).substate }
  rcases
      primCall_CALL_noCode_emptyReturn_rel_stateRelConfig
        hShared store hStaticAllowed hEnough hDepth hNotPrecompile hMissing
        hGas with
    ⟨hEvm, yulAfter, hYul, hRel⟩
  refine ⟨⟨1⟩, evmAfter, yulAfter, ?_, ?_, ?_⟩
  · simpa [evmAfter, targetGas, charged, callGas, callMap, target] using hEvm
  · exact hYul
  · simpa [evmAfter, targetGas, charged, callGas, callMap, target] using hRel

theorem EVM_call_precompiled_success_eq
    {fuel gasCost : Nat}
    {blobVersionedHashes : List ByteArray}
    {evm : EvmYul.EVM.State}
    {gas address value inOffset inSize outOffset outSize : EvmYul.UInt256}
    {precompiled : EvmYul.PrecompiledContract}
    (hEnough :
      value ≤
        (evm.accountMap.find? evm.executionEnv.codeOwner |>.option ⟨0⟩
          (·.balance)))
    (hDepth : evm.executionEnv.depth < 1024)
    (hPrecompile :
      EvmYul.PrecompiledContract.ofAddress?
        (EvmYul.AccountAddress.ofUInt256 address) = some precompiled)
    (hSuccess :
      let target := EvmYul.AccountAddress.ofUInt256 address
      let callMap :=
        evmCallTransfer evm.accountMap evm.executionEnv.codeOwner target value
      let callGas :=
        EvmYul.EVM.Ccallgas target target value gas evm.accountMap
          evm.toMachineState evm.substate
      let accessedSubstate :=
        (EvmYul.State.addAccessedAccount evm.toState target).substate
      let childEnv :=
        EvmYul.EVM.thetaCallExecutionEnv blobVersionedHashes
          evm.executionEnv.codeOwner evm.executionEnv.sender target
          (.Precompiled precompiled)
          (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice)
          value
          (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
          (evm.executionEnv.depth + 1) evm.executionEnv.header
          evm.executionEnv.perm
      (runPrecompiledContract precompiled callMap
        (EvmYul.UInt256.ofNat callGas) accessedSubstate childEnv).1 =
        true) :
    let target := EvmYul.AccountAddress.ofUInt256 address
    let callMap :=
      evmCallTransfer evm.accountMap evm.executionEnv.codeOwner target value
    let callGas :=
      EvmYul.EVM.Ccallgas target target value gas evm.accountMap
        evm.toMachineState evm.substate
    let charged : EvmYul.EVM.State :=
      { evm with gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
    let accessedSubstate :=
      (EvmYul.State.addAccessedAccount charged.toState target).substate
    let childEnv :=
      EvmYul.EVM.thetaCallExecutionEnv blobVersionedHashes
        evm.executionEnv.codeOwner evm.executionEnv.sender target
        (.Precompiled precompiled)
        (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice)
        value
        (charged.memory.readWithPadding inOffset.toNat inSize.toNat)
        (evm.executionEnv.depth + 1) evm.executionEnv.header
        evm.executionEnv.perm
    let precompileResult :=
      runPrecompiledContract precompiled callMap
        (EvmYul.UInt256.ofNat callGas) accessedSubstate childEnv
    let targetGas :=
      (charged.toMachineState.finishExternalCall precompileResult.2.2.2.2
        inOffset inSize outOffset outSize).gasAvailable +
        precompileResult.2.2.1
    EvmYul.EVM.call fuel.succ.succ gasCost blobVersionedHashes gas
        (EvmYul.UInt256.ofNat evm.executionEnv.codeOwner) address address
        value value inOffset inSize outOffset outSize evm.executionEnv.perm
        evm =
      .ok (⟨1⟩,
        { charged with
          toMachineState :=
            { charged.toMachineState.finishExternalCall
                precompileResult.2.2.2.2 inOffset inSize outOffset outSize with
              gasAvailable := targetGas }
          accountMap :=
            if precompileResult.2.1.isEmpty then evm.accountMap
            else precompileResult.2.1
          substate :=
            if precompileResult.2.1.isEmpty then accessedSubstate
            else precompileResult.2.2.2.1 }) := by
  dsimp at hSuccess ⊢
  have hSource :
      EvmYul.AccountAddress.ofUInt256
          (EvmYul.UInt256.ofNat evm.executionEnv.codeOwner) =
        evm.executionEnv.codeOwner :=
    AccountAddress_ofUInt256_ofNat evm.executionEnv.codeOwner
  simp [EvmYul.EVM.call, EvmYul.toExecute, hEnough, hDepth,
    hPrecompile, hSource, evmCallTransfer_eq_thetaCallTransfer] at hSuccess ⊢
  have hNotLt :
      ¬ ((evm.accountMap.find? evm.executionEnv.codeOwner).elim
          ⟨0⟩ fun account => account.balance) < value := by
    intro hLt
    cases hFind : evm.accountMap.find? evm.executionEnv.codeOwner with
    | none =>
        simp [hFind, Option.option] at hEnough hLt
        change value.val ≤ 0 at hEnough
        change 0 < value.val at hLt
        omega
    | some account =>
        simp [hFind, Option.option] at hEnough hLt
        change value.val ≤ account.balance.val at hEnough
        change account.balance.val < value.val at hLt
        omega
  have hNotDepthEq : ¬ evm.executionEnv.depth = 1024 := by
    omega
  simpa [EvmYul.EVM.Θ, hNotLt, hNotDepthEq] using hSuccess

theorem EVM_call_precompiled_failure_eq
    {fuel gasCost : Nat}
    {blobVersionedHashes : List ByteArray}
    {evm : EvmYul.EVM.State}
    {gas address value inOffset inSize outOffset outSize : EvmYul.UInt256}
    {precompiled : EvmYul.PrecompiledContract}
    (hEnough :
      value ≤
        (evm.accountMap.find? evm.executionEnv.codeOwner |>.option ⟨0⟩
          (·.balance)))
    (hDepth : evm.executionEnv.depth < 1024)
    (hPrecompile :
      EvmYul.PrecompiledContract.ofAddress?
        (EvmYul.AccountAddress.ofUInt256 address) = some precompiled)
    (hFailure :
      let target := EvmYul.AccountAddress.ofUInt256 address
      let callMap :=
        evmCallTransfer evm.accountMap evm.executionEnv.codeOwner target value
      let callGas :=
        EvmYul.EVM.Ccallgas target target value gas evm.accountMap
          evm.toMachineState evm.substate
      let accessedSubstate :=
        (EvmYul.State.addAccessedAccount evm.toState target).substate
      let childEnv :=
        EvmYul.EVM.thetaCallExecutionEnv blobVersionedHashes
          evm.executionEnv.codeOwner evm.executionEnv.sender target
          (.Precompiled precompiled)
          (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice)
          value
          (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
          (evm.executionEnv.depth + 1) evm.executionEnv.header
          evm.executionEnv.perm
      (runPrecompiledContract precompiled callMap
        (EvmYul.UInt256.ofNat callGas) accessedSubstate childEnv).1 =
        false) :
    let target := EvmYul.AccountAddress.ofUInt256 address
    let callMap :=
      evmCallTransfer evm.accountMap evm.executionEnv.codeOwner target value
    let callGas :=
      EvmYul.EVM.Ccallgas target target value gas evm.accountMap
        evm.toMachineState evm.substate
    let charged : EvmYul.EVM.State :=
      { evm with gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
    let accessedSubstate :=
      (EvmYul.State.addAccessedAccount charged.toState target).substate
    let childEnv :=
      EvmYul.EVM.thetaCallExecutionEnv blobVersionedHashes
        evm.executionEnv.codeOwner evm.executionEnv.sender target
        (.Precompiled precompiled)
        (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice)
        value
        (charged.memory.readWithPadding inOffset.toNat inSize.toNat)
        (evm.executionEnv.depth + 1) evm.executionEnv.header
        evm.executionEnv.perm
    let precompileResult :=
      runPrecompiledContract precompiled callMap
        (EvmYul.UInt256.ofNat callGas) accessedSubstate childEnv
    let targetGas :=
      (charged.toMachineState.finishExternalCall precompileResult.2.2.2.2
        inOffset inSize outOffset outSize).gasAvailable +
        precompileResult.2.2.1
    EvmYul.EVM.call fuel.succ.succ gasCost blobVersionedHashes gas
        (EvmYul.UInt256.ofNat evm.executionEnv.codeOwner) address address
        value value inOffset inSize outOffset outSize evm.executionEnv.perm
        evm =
      .ok (⟨0⟩,
        { charged with
          toMachineState :=
            { charged.toMachineState.finishExternalCall
                precompileResult.2.2.2.2 inOffset inSize outOffset outSize with
              gasAvailable := targetGas }
          accountMap :=
            if precompileResult.2.1.isEmpty then evm.accountMap
            else precompileResult.2.1
          substate :=
            if precompileResult.2.1.isEmpty then accessedSubstate
            else precompileResult.2.2.2.1 }) := by
  dsimp at hFailure ⊢
  have hSource :
      EvmYul.AccountAddress.ofUInt256
          (EvmYul.UInt256.ofNat evm.executionEnv.codeOwner) =
        evm.executionEnv.codeOwner :=
    AccountAddress_ofUInt256_ofNat evm.executionEnv.codeOwner
  simp [EvmYul.EVM.call, EvmYul.toExecute, hEnough, hDepth,
    hPrecompile, hSource, evmCallTransfer_eq_thetaCallTransfer] at hFailure ⊢
  have hNotLt :
      ¬ ((evm.accountMap.find? evm.executionEnv.codeOwner).elim
          ⟨0⟩ fun account => account.balance) < value := by
    intro hLt
    cases hFind : evm.accountMap.find? evm.executionEnv.codeOwner with
    | none =>
        simp [hFind, Option.option] at hEnough hLt
        change value.val ≤ 0 at hEnough
        change 0 < value.val at hLt
        omega
    | some account =>
        simp [hFind, Option.option] at hEnough hLt
        change value.val ≤ account.balance.val at hEnough
        change account.balance.val < value.val at hLt
        omega
  have hNotDepthEq : ¬ evm.executionEnv.depth = 1024 := by
    omega
  simpa [EvmYul.EVM.Θ, hNotLt, hNotDepthEq] using hFailure

theorem EVM_call_ordinaryCode_of_theta_eq
    {fuel gasCost : Nat}
    {blobVersionedHashes : List ByteArray}
    {evm : EvmYul.EVM.State}
    {gas address value inOffset inSize outOffset outSize : EvmYul.UInt256}
    {calleeAccount : EvmYul.Account .EVM}
    {target : Assembly.TargetProgram}
    {createdAccounts' : Batteries.RBSet EvmYul.AccountAddress compare}
    {accountMap' : EvmYul.AccountMap .EVM}
    {returnedGas : EvmYul.UInt256}
    {substate' : EvmYul.Substate}
    {z : Bool}
    {output : ByteArray}
    (hEnough :
      value ≤
        (evm.accountMap.find? evm.executionEnv.codeOwner |>.option ⟨0⟩
          (·.balance)))
    (hDepth : evm.executionEnv.depth < 1024)
    (hNotPrecompile :
      EvmYul.PrecompiledContract.ofAddress?
        (EvmYul.AccountAddress.ofUInt256 address) = none)
    (hFind :
      evm.accountMap.find?
        (EvmYul.AccountAddress.ofUInt256 address) = some calleeAccount)
    (hCode : calleeAccount.code = Assembly.Bytecode.encodeTarget target)
    (hTheta :
      let callee := EvmYul.AccountAddress.ofUInt256 address
      let callGas :=
        EvmYul.EVM.Ccallgas callee callee value gas evm.accountMap
          evm.toMachineState evm.substate
      let accessedSubstate :=
        (EvmYul.State.addAccessedAccount evm.toState callee).substate
      EvmYul.EVM.Θ fuel blobVersionedHashes evm.createdAccounts
          evm.genesisBlockHeader evm.blocks evm.accountMap evm.σ₀
          { totalGasUsedInBlock := evm.totalGasUsedInBlock
            transactionReceipts := evm.transactionReceipts }
          accessedSubstate evm.executionEnv.codeOwner
          evm.executionEnv.sender callee
          (.Code (Assembly.Bytecode.encodeTarget target))
          (EvmYul.UInt256.ofNat callGas)
          (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice)
          value value
          (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
          (evm.executionEnv.depth + 1) evm.executionEnv.header
          evm.executionEnv.perm =
        .ok (createdAccounts', accountMap', returnedGas, substate', z,
          output)) :
    let charged : EvmYul.EVM.State :=
      { evm with gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
    let targetGas :=
      (charged.toMachineState.finishExternalCall output
        inOffset inSize outOffset outSize).gasAvailable + returnedGas
    EvmYul.EVM.call fuel.succ gasCost blobVersionedHashes gas
        (EvmYul.UInt256.ofNat evm.executionEnv.codeOwner) address address
        value value inOffset inSize outOffset outSize evm.executionEnv.perm
        evm =
      .ok (if z then ⟨1⟩ else ⟨0⟩,
        { charged with
          toMachineState :=
            { charged.toMachineState.finishExternalCall output
                inOffset inSize outOffset outSize with
              gasAvailable := targetGas }
          accountMap := accountMap'
          substate := substate'
          createdAccounts := createdAccounts' }) := by
  dsimp at hTheta ⊢
  have hSource :
      EvmYul.AccountAddress.ofUInt256
          (EvmYul.UInt256.ofNat evm.executionEnv.codeOwner) =
        evm.executionEnv.codeOwner :=
    AccountAddress_ofUInt256_ofNat evm.executionEnv.codeOwner
  have hNotLt :
      ¬ ((evm.accountMap.find? evm.executionEnv.codeOwner).elim
          ⟨0⟩ fun account => account.balance) < value := by
    intro hLt
    cases hOwner : evm.accountMap.find? evm.executionEnv.codeOwner with
    | none =>
        simp [hOwner, Option.option] at hEnough hLt
        change value.val ≤ 0 at hEnough
        change 0 < value.val at hLt
        omega
    | some account =>
        simp [hOwner, Option.option] at hEnough hLt
        change value.val ≤ account.balance.val at hEnough
        change account.balance.val < value.val at hLt
        omega
  have hNotDepthEq : ¬ evm.executionEnv.depth = 1024 := by
    omega
  have hThetaRun :
      EvmYul.EVM.Θ fuel blobVersionedHashes evm.createdAccounts
          evm.genesisBlockHeader evm.blocks evm.accountMap evm.σ₀
          { totalGasUsedInBlock := evm.totalGasUsedInBlock
            transactionReceipts := evm.transactionReceipts }
          (EvmYul.State.addAccessedAccount evm.toState
            (EvmYul.AccountAddress.ofUInt256 address)).substate
          evm.executionEnv.codeOwner evm.executionEnv.sender
          (EvmYul.AccountAddress.ofUInt256 address)
          (Id.run
            (EvmYul.ToExecute.Code (Assembly.Bytecode.encodeTarget target)))
          (EvmYul.UInt256.ofNat
            (EvmYul.EVM.Ccallgas
              (EvmYul.AccountAddress.ofUInt256 address)
              (EvmYul.AccountAddress.ofUInt256 address)
              value gas evm.accountMap evm.toMachineState evm.substate))
          (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice)
          value value
          (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
          (evm.executionEnv.depth + 1) evm.executionEnv.header
          evm.executionEnv.perm =
        .ok (createdAccounts', accountMap', returnedGas, substate', z,
          output) := by
    simpa using hTheta
  cases z <;>
    simp [EvmYul.EVM.call, EvmYul.toExecute, hEnough, hDepth,
      hNotPrecompile, hFind, hCode, hSource,
      hThetaRun, hNotLt, hNotDepthEq]

def thetaCodeRawInitialState
    (_target : Assembly.TargetProgram) (gasNat : Nat)
    (blobVersionedHashes : List ByteArray)
    (createdAccounts : Batteries.RBSet EvmYul.AccountAddress compare)
    (genesisBlockHeader : EvmYul.BlockHeader)
    (blocks : EvmYul.ProcessedBlocks)
    (accountMap sigma0 : EvmYul.AccountMap .EVM)
    (chainContext : EvmYul.EVM.ChildFrameChainContext)
    (substate : EvmYul.Substate)
    (source origin recipient : EvmYul.AccountAddress)
    (gasPrice value weiValue : EvmYul.UInt256)
    (calldata : ByteArray)
    (depth : Nat)
    (header : EvmYul.BlockHeader)
    (perm : Bool) : EVMState :=
  { xiInitialState createdAccounts genesisBlockHeader blocks
      (EvmYul.EVM.thetaCallTransfer accountMap source recipient value)
      sigma0 chainContext (EvmYul.UInt256.ofNat gasNat) substate
      (EvmYul.EVM.thetaCallExecutionEnv blobVersionedHashes source origin
        recipient (.Code default) gasPrice weiValue calldata depth header
        perm) with
    pc := Assembly.Program.pcAfter []
    stack := [] }

def thetaCodeXInitialState
    (target : Assembly.TargetProgram) (gasNat : Nat)
    (blobVersionedHashes : List ByteArray)
    (createdAccounts : Batteries.RBSet EvmYul.AccountAddress compare)
    (genesisBlockHeader : EvmYul.BlockHeader)
    (blocks : EvmYul.ProcessedBlocks)
    (accountMap sigma0 : EvmYul.AccountMap .EVM)
    (chainContext : EvmYul.EVM.ChildFrameChainContext)
    (substate : EvmYul.Substate)
    (source origin recipient : EvmYul.AccountAddress)
    (gasPrice value weiValue : EvmYul.UInt256)
    (calldata : ByteArray)
    (depth : Nat)
    (header : EvmYul.BlockHeader)
    (perm : Bool) : EVMState :=
  Assembly.GasAware.installCodeAndGas target gasNat
    (thetaCodeRawInitialState target gasNat blobVersionedHashes
      createdAccounts genesisBlockHeader blocks accountMap sigma0
      chainContext substate source origin recipient gasPrice value weiValue
      calldata depth header perm)

theorem sharedStateRel_callFrameFromThetaCodeXInitialState
    {cfg : Reference.StateRelConfig}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.SharedState .EVM}
    (hShared : Reference.SharedStateRel cfg yul evm)
    {yulAccountMap : EvmYul.AccountMap .Yul}
    {evmSubstate : EvmYul.Substate}
    {yulCreated : Batteries.RBSet EvmYul.AccountAddress compare}
    {yulGas : EvmYul.UInt256}
    {yulCode : AstContract}
    {yulSubstate : EvmYul.Substate}
    (source origin recipient : EvmYul.AccountAddress)
    (gasPrice value weiValue : EvmYul.UInt256)
    (calldata : ByteArray)
    (depth : Nat)
    (header : EvmYul.BlockHeader)
    (perm : Bool)
    (blobVersionedHashes : List ByteArray)
    (yulCodeBytes : ByteArray)
    (target : Assembly.TargetProgram) (gasNat : Nat)
    (hAccountMap :
      cfg.accountMapRel yulAccountMap
        (EvmYul.EVM.thetaCallTransfer evm.accountMap source recipient value))
    (hSubstate : yulSubstate = evmSubstate)
      (hCode :
        cfg.codeRel yulCode (Assembly.Bytecode.encodeTarget target))
      (hCodeBytes : yulCodeBytes = Assembly.Bytecode.encodeTarget target)
      (hCreated : yulCreated = evm.createdAccounts)
    (hGas :
      cfg.gasAvailableRel yulGas (EvmYul.UInt256.ofNat gasNat)) :
    Reference.SharedStateRel cfg
      { yul with
        toMachineState := EvmYul.MachineState.freshExternalCall yulGas
        accountMap := yulAccountMap
        substate := yulSubstate
        executionEnv :=
          { codeOwner := recipient
            sender := origin
            source := source
            weiValue := weiValue
            calldata := calldata
            code := yulCode
            gasPrice := gasPrice.toNat
            header := header
            depth := depth
            perm := perm
            blobVersionedHashes := blobVersionedHashes
            codeBytes := yulCodeBytes }
        createdAccounts := yulCreated }
      (thetaCodeXInitialState target gasNat blobVersionedHashes
        evm.createdAccounts evm.genesisBlockHeader evm.blocks
        evm.accountMap evm.σ₀
        { totalGasUsedInBlock := evm.totalGasUsedInBlock
          transactionReceipts := evm.transactionReceipts }
        evmSubstate source origin recipient gasPrice value weiValue
        calldata depth header perm).toSharedState := by
  simpa [thetaCodeXInitialState, Assembly.GasAware.installCodeAndGas,
    xiInitialState, EvmYul.EVM.thetaCallExecutionEnv,
    EvmYul.MachineState.freshExternalCall, Assembly.Program.pcAfter] using
    sharedStateRel_callFrameFromFreshEvmFrame
      (cfg := cfg)
      (yul := yul)
      (evm := evm)
      hShared
      (yulAccountMap := yulAccountMap)
      (evmAccountMap :=
        EvmYul.EVM.thetaCallTransfer evm.accountMap source recipient value)
      (yulSubstate := yulSubstate)
      (evmSubstate := evmSubstate)
      (yulCreated := yulCreated)
      (evmCreated := evm.createdAccounts)
      (yulGas := yulGas)
      (evmGas := EvmYul.UInt256.ofNat gasNat)
      (yulCode := yulCode)
      (evmCode := Assembly.Bytecode.encodeTarget target)
        hAccountMap hSubstate hCode hCreated hGas
        recipient origin source weiValue calldata gasPrice.toNat depth header
        perm blobVersionedHashes yulCodeBytes default hCodeBytes

theorem ordinaryCall_nondefault_initialChildFrame_rel
    {cfg : Reference.StateRelConfig}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.EVM.State}
    (hShared : Reference.SharedStateRel cfg yul evm.toSharedState)
    (hParentWorld : CompiledAccountMapRel yul.accountMap evm.accountMap)
    (hCfgAccountMap :
      ∀ {yulMap : EvmYul.AccountMap .Yul}
        {evmMap : EvmYul.AccountMap .EVM},
        CompiledAccountMapRel yulMap evmMap →
          cfg.accountMapRel yulMap evmMap)
    (hCfgCode :
      ∀ {yulCode : AstContract} {evmCode : ByteArray},
        CompiledCodeRel yulCode evmCode →
          cfg.codeRel yulCode evmCode)
    {gas address value inOffset inSize : EvmYul.UInt256}
    {yulRecipient : EvmYul.Account .Yul}
    (hEnough :
      value ≤
        (evm.accountMap.find? evm.executionEnv.codeOwner |>.option ⟨0⟩
          (·.balance)))
    (hFindRecipient :
      yul.accountMap.find? (EvmYul.AccountAddress.ofUInt256 address) =
        some yulRecipient)
    (hCodeNondefault : yulRecipient.code ≠ default)
    (hCallGas :
      cfg.gasAvailableRel
        (EvmYul.UInt256.ofNat
          (EvmYul.EVM.Ccallgas
            (EvmYul.AccountAddress.ofUInt256 address)
            (EvmYul.AccountAddress.ofUInt256 address)
            value gas yul.accountMap yul.toMachineState yul.substate))
        (EvmYul.UInt256.ofNat
          (EvmYul.EVM.Ccallgas
            (EvmYul.AccountAddress.ofUInt256 address)
            (EvmYul.AccountAddress.ofUInt256 address)
            value gas evm.accountMap evm.toMachineState evm.substate)))
    (hGasPriceFits :
      (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice).toNat =
        evm.executionEnv.gasPrice) :
    ∃ (yulCallMap : EvmYul.AccountMap .Yul)
      (evmRecipient : EvmYul.Account .EVM)
      (program : Program) (asm : Assembly.Program)
      (target : Assembly.TargetProgram),
      let callee := EvmYul.AccountAddress.ofUInt256 address
      let calldata :=
        yul.toMachineState.memory.readWithPadding
          inOffset.toNat inSize.toNat
      let yulAccessed : EvmYul.SharedState .Yul :=
        { yul with
          toState := EvmYul.State.addAccessedAccount yul.toState callee }
      let initialShared : EvmYul.SharedState .Yul :=
        { yulAccessed with
          executionEnv :=
            { yulAccessed.executionEnv with
              calldata := calldata
              code := yulRecipient.code
              codeBytes := yulRecipient.codeBytes
              codeOwner := callee
              source := yul.executionEnv.codeOwner
              weiValue := value
              depth := yul.executionEnv.depth + 1 }
          toMachineState :=
            EvmYul.MachineState.freshExternalCall
              (EvmYul.UInt256.ofNat
                (EvmYul.EVM.Ccallgas callee callee value gas
                  yul.accountMap yul.toMachineState yul.substate))
          accountMap := yulCallMap }
      EvmYul.Yul.callTransferAccountMap? yul.accountMap
          yul.executionEnv.codeOwner callee value =
        some yulCallMap ∧
      yulCallMap.isEmpty = false ∧
      (evmCallTransfer evm.accountMap evm.executionEnv.codeOwner
          callee value).isEmpty = false ∧
      CompiledAccountMapRel yulCallMap
        (evmCallTransfer evm.accountMap evm.executionEnv.codeOwner
          callee value) ∧
      evm.accountMap.find? callee = some evmRecipient ∧
      CompiledAccountRel yulRecipient evmRecipient ∧
      program.contract = yulRecipient.code ∧
      compileCheckedAssemblyTargetBytecodeResourcesSourceStatic? program =
        some (asm, target) ∧
      initialShared.executionEnv.code = program.contract ∧
      Reference.SharedStateRel cfg initialShared
        (thetaCodeXInitialState target
          (EvmYul.EVM.Ccallgas callee callee value gas
            evm.accountMap evm.toMachineState evm.substate)
          yul.executionEnv.blobVersionedHashes evm.createdAccounts
          evm.genesisBlockHeader evm.blocks evm.accountMap evm.σ₀
          { totalGasUsedInBlock := evm.totalGasUsedInBlock
            transactionReceipts := evm.transactionReceipts }
          (EvmYul.State.addAccessedAccount evm.toState callee).substate
          evm.executionEnv.codeOwner evm.executionEnv.sender callee
          (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice) value value
          calldata (evm.executionEnv.depth + 1) evm.executionEnv.header
          evm.executionEnv.perm).toSharedState := by
  dsimp
  let callee := EvmYul.AccountAddress.ofUInt256 address
  let calldata :=
    yul.toMachineState.memory.readWithPadding inOffset.toNat inSize.toNat
  let yulAccessed : EvmYul.SharedState .Yul :=
    { yul with
      toState := EvmYul.State.addAccessedAccount yul.toState callee }
  let evmAccessed : EvmYul.SharedState .EVM :=
    { evm.toSharedState with
      toState := EvmYul.State.addAccessedAccount evm.toState callee }
  have hOwner :
      yul.executionEnv.codeOwner = evm.executionEnv.codeOwner := by
    rcases hShared with ⟨hChain, _hMachine⟩
    simpa using hChain.executionEnv.codeOwner
  have hSender :
      yul.executionEnv.sender = evm.executionEnv.sender := by
    rcases hShared with ⟨hChain, _hMachine⟩
    simpa using hChain.executionEnv.sender
  have hGasPrice :
      yul.executionEnv.gasPrice = evm.executionEnv.gasPrice := by
    rcases hShared with ⟨hChain, _hMachine⟩
    simpa using hChain.executionEnv.gasPrice
  have hHeader :
      yul.executionEnv.header = evm.executionEnv.header := by
    rcases hShared with ⟨hChain, _hMachine⟩
    simpa using hChain.executionEnv.header
  have hDepth :
      yul.executionEnv.depth = evm.executionEnv.depth := by
    rcases hShared with ⟨hChain, _hMachine⟩
    simpa using hChain.executionEnv.depth
  have hPerm :
      yul.executionEnv.perm = evm.executionEnv.perm := by
    rcases hShared with ⟨hChain, _hMachine⟩
    simpa using hChain.executionEnv.perm
  rcases
      hParentWorld.ordinaryCall_nondefault_transferCheckedFacts
        (source := yul.executionEnv.codeOwner)
        (recipient := callee)
        (value := value)
        hFindRecipient hCodeNondefault
        (by simpa [hOwner] using hEnough) with
    ⟨yulCallMap, evmRecipient, program, asm, target, hTransfer,
      hYulCallMapNonempty, hEvmCallMapNonempty, hTransferRel,
      hFindEvm, hRecipientRel, hContract, hCompile, _hStatic,
      _hSourceAccepted, _hSourceCompileAccepted, _hCompileChecked,
      _hBytecode, _hResources, _hDecode, _hJumpdest, hBytes⟩
  refine
    ⟨yulCallMap, evmRecipient, program, asm, target, ?_, ?_, ?_,
      ?_, ?_, hRecipientRel, hContract, hCompile, ?_, ?_⟩
  · simpa [callee] using hTransfer
  · exact hYulCallMapNonempty
  · simpa [hOwner] using hEvmCallMapNonempty
  · simpa [hOwner] using hTransferRel
  · simpa [callee] using hFindEvm
  · simp [hContract]
  · have hSharedAccessed :
        Reference.SharedStateRel cfg yulAccessed evmAccessed := by
      simpa [yulAccessed, evmAccessed, callee] using
        sharedStateRel_addAccessedAccount hShared callee
    have hCalldata :
        calldata =
          evm.toMachineState.memory.readWithPadding
            inOffset.toNat inSize.toNat := by
      rcases hShared with ⟨_hChain, hMachine⟩
      simpa [calldata] using
        congrArg
          (fun memory =>
            memory.readWithPadding inOffset.toNat inSize.toNat)
          hMachine.memory
    have hCode :
        cfg.codeRel yulRecipient.code
          (Assembly.Bytecode.encodeTarget target) := by
      simpa [hBytes] using hCfgCode hRecipientRel.code
    have hAccountMap :
        cfg.accountMapRel yulCallMap
          (EvmYul.EVM.thetaCallTransfer evm.accountMap
            evm.executionEnv.codeOwner callee value) := by
      simpa [hOwner, evmCallTransfer_eq_thetaCallTransfer] using
        hCfgAccountMap hTransferRel
    simpa [callee, calldata, yulAccessed, evmAccessed, hOwner, hSender,
      hGasPrice, hGasPriceFits, hHeader, hDepth, hPerm, hCalldata,
      EvmYul.State.addAccessedAccount]
      using
        sharedStateRel_callFrameFromThetaCodeXInitialState
          (cfg := cfg)
          (yul := yulAccessed)
          (evm := evmAccessed)
          hSharedAccessed
          (yulAccountMap := yulCallMap)
          (evmSubstate := evmAccessed.substate)
          (yulCreated := yulAccessed.createdAccounts)
          (yulGas :=
            EvmYul.UInt256.ofNat
              (EvmYul.EVM.Ccallgas callee callee value gas
                yul.accountMap yul.toMachineState yul.substate))
          (yulCode := yulRecipient.code)
          (yulSubstate := yulAccessed.substate)
          evm.executionEnv.codeOwner evm.executionEnv.sender callee
          (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice) value value
          (evm.toMachineState.memory.readWithPadding
            inOffset.toNat inSize.toNat)
            (evm.executionEnv.depth + 1) evm.executionEnv.header
            evm.executionEnv.perm yul.executionEnv.blobVersionedHashes
            yulRecipient.codeBytes
            target
            (EvmYul.EVM.Ccallgas callee callee value gas evm.accountMap
              evm.toMachineState evm.substate)
            hAccountMap hSharedAccessed.chain.substate hCode
            (hRecipientRel.codeBytes.trans hBytes)
            hSharedAccessed.chain.createdAccounts hCallGas

theorem Theta_code_succ_succ_eq_X_installedCode
    (fuel gasNat : Nat)
    (blobVersionedHashes : List ByteArray)
    (createdAccounts : Batteries.RBSet EvmYul.AccountAddress compare)
    (genesisBlockHeader : EvmYul.BlockHeader)
    (blocks : EvmYul.ProcessedBlocks)
    (accountMap sigma0 : EvmYul.AccountMap .EVM)
    (chainContext : EvmYul.EVM.ChildFrameChainContext)
    (substate : EvmYul.Substate)
    (source origin recipient : EvmYul.AccountAddress)
    (target : Assembly.TargetProgram)
    (gasPrice value weiValue : EvmYul.UInt256)
    (calldata : ByteArray)
    (depth : Nat)
    (header : EvmYul.BlockHeader)
    (perm : Bool) :
    EvmYul.EVM.Θ fuel.succ.succ blobVersionedHashes createdAccounts
        genesisBlockHeader blocks accountMap sigma0 chainContext substate
        source origin recipient (.Code (Assembly.Bytecode.encodeTarget target))
        (EvmYul.UInt256.ofNat gasNat) gasPrice value weiValue calldata depth
        header perm =
      match EvmYul.EVM.X fuel (Assembly.GasAware.validJumps target)
          (thetaCodeXInitialState target gasNat blobVersionedHashes
            createdAccounts genesisBlockHeader blocks accountMap sigma0
            chainContext substate source origin recipient gasPrice value
            weiValue calldata depth header perm) with
      | .error err =>
          if err == EvmYul.EVM.ExecutionException.OutOfFuel then
            .error EvmYul.EVM.ExecutionException.OutOfFuel
          else
            .ok (createdAccounts, accountMap, ⟨0⟩, substate, false,
              ByteArray.empty)
      | .ok (.revert returnedGas output) =>
          .ok (createdAccounts, accountMap, returnedGas, substate, false,
            output)
      | .ok (.success evmState' output) =>
          .ok (evmState'.createdAccounts,
            if evmState'.accountMap.isEmpty then accountMap
            else evmState'.accountMap,
            evmState'.gasAvailable,
            if evmState'.accountMap.isEmpty then substate
            else evmState'.substate,
            true, output) := by
  rw [Theta_code_succ_eq_Xi (fuel := fuel.succ)]
  have hEnv :
      EvmYul.EVM.thetaCallExecutionEnv blobVersionedHashes source origin
          recipient (.Code (Assembly.Bytecode.encodeTarget target)) gasPrice
          weiValue calldata depth header perm =
        { EvmYul.EVM.thetaCallExecutionEnv blobVersionedHashes source origin
            recipient (.Code default) gasPrice weiValue calldata depth header
            perm with
          code := Assembly.Bytecode.encodeTarget target } := by
    simp [EvmYul.EVM.thetaCallExecutionEnv]
  rw [hEnv]
  rw [Xi_succ_eq_X_installedCode
    (fuel := fuel)
    (gasNat := gasNat)
    (createdAccounts := createdAccounts)
    (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks)
    (accountMap :=
      EvmYul.EVM.thetaCallTransfer accountMap source recipient value)
    (sigma0 := sigma0)
    (chainContext := chainContext)
    (initialGas := EvmYul.UInt256.ofNat gasNat)
    (substate := substate)
    (env :=
      EvmYul.EVM.thetaCallExecutionEnv blobVersionedHashes source origin
        recipient (.Code default) gasPrice weiValue calldata depth header perm)
    (target := target)]
  unfold thetaCodeXInitialState thetaCodeRawInitialState
  cases hX :
      EvmYul.EVM.X fuel (Assembly.GasAware.validJumps target)
        (Assembly.GasAware.installCodeAndGas target gasNat
          { xiInitialState createdAccounts genesisBlockHeader blocks
              (EvmYul.EVM.thetaCallTransfer accountMap source recipient value)
              sigma0 chainContext (EvmYul.UInt256.ofNat gasNat) substate
              (EvmYul.EVM.thetaCallExecutionEnv blobVersionedHashes source
                origin recipient (.Code default) gasPrice weiValue calldata
                depth header perm) with
            pc := Assembly.Program.pcAfter []
            stack := [] }) with
  | error err =>
      simp
  | ok result =>
      cases result with
      | success evmState output =>
          simp
      | revert returnedGas output =>
          simp

theorem Theta_code_success_of_X_installedCode
    {fuel gasNat : Nat}
    {blobVersionedHashes : List ByteArray}
    {createdAccounts : Batteries.RBSet EvmYul.AccountAddress compare}
    {genesisBlockHeader : EvmYul.BlockHeader}
    {blocks : EvmYul.ProcessedBlocks}
    {accountMap sigma0 : EvmYul.AccountMap .EVM}
    {chainContext : EvmYul.EVM.ChildFrameChainContext}
    {substate : EvmYul.Substate}
    {source origin recipient : EvmYul.AccountAddress}
    {target : Assembly.TargetProgram}
    {gasPrice value weiValue : EvmYul.UInt256}
    {calldata : ByteArray}
    {depth : Nat}
    {header : EvmYul.BlockHeader}
    {perm : Bool}
    {evmChild : EVMState} {output : ByteArray}
    (hX :
      EvmYul.EVM.X fuel (Assembly.GasAware.validJumps target)
          (thetaCodeXInitialState target gasNat blobVersionedHashes
            createdAccounts genesisBlockHeader blocks accountMap sigma0
            chainContext substate source origin recipient gasPrice value
            weiValue calldata depth header perm) =
        .ok (.success evmChild output)) :
    EvmYul.EVM.Θ fuel.succ.succ blobVersionedHashes createdAccounts
        genesisBlockHeader blocks accountMap sigma0 chainContext substate
        source origin recipient (.Code (Assembly.Bytecode.encodeTarget target))
        (EvmYul.UInt256.ofNat gasNat) gasPrice value weiValue calldata depth
        header perm =
      .ok (evmChild.createdAccounts,
        if evmChild.accountMap.isEmpty then accountMap else evmChild.accountMap,
        evmChild.gasAvailable,
        if evmChild.accountMap.isEmpty then substate else evmChild.substate,
        true, output) := by
  rw [Theta_code_succ_succ_eq_X_installedCode]
  simp [hX]

theorem ordinaryCodeCall_runningSuccessBranch_rel
    {cfg : Reference.StateRelConfig}
    {yulParent : EvmYul.SharedState .Yul}
    {evmParent : EvmYul.SharedState .EVM}
    (hParent : Reference.SharedStateRel cfg yulParent evmParent)
    (hParentWorld :
      CompiledAccountMapRel yulParent.accountMap evmParent.accountMap)
    (hCfgAccountMap :
      ∀ {yulMap : EvmYul.AccountMap .Yul}
        {evmMap : EvmYul.AccountMap .EVM},
        CompiledAccountMapRel yulMap evmMap →
          cfg.accountMapRel yulMap evmMap)
    (parentStore childStore restoreStore : EvmYul.Yul.VarStore)
    {yulChild : EvmYul.SharedState .Yul}
    {targetChild evmChild : EVMState}
    {fuel gasNat : Nat}
    {blobVersionedHashes : List ByteArray}
    {source origin recipient : EvmYul.AccountAddress}
    {target : Assembly.TargetProgram}
    {gasPrice value weiValue : EvmYul.UInt256}
    {calldata output : ByteArray}
    {depth : Nat}
    {header : EvmYul.BlockHeader}
    {perm : Bool}
    (hTargetChild :
      Reference.SharedStateRel cfg yulChild targetChild.toSharedState)
    (hTargetChildWorld :
      CompiledAccountMapRel yulChild.accountMap targetChild.accountMap)
    (hX :
      EvmYul.EVM.X fuel (Assembly.GasAware.validJumps target)
          (thetaCodeXInitialState target gasNat blobVersionedHashes
            evmParent.createdAccounts evmParent.genesisBlockHeader
            evmParent.blocks evmParent.accountMap evmParent.σ₀
            { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
              transactionReceipts := evmParent.transactionReceipts }
            evmParent.substate source origin recipient gasPrice value
            weiValue calldata depth header perm) =
        .ok (.success evmChild output))
    (hAgree :
      Assembly.GasAware.XResultAgrees (.running targetChild)
        (.success evmChild output))
    (hChildGas :
      cfg.gasAvailableRel yulChild.toMachineState.gasAvailable
        evmChild.gasAvailable)
    (inOffset inSize outOffset outSize : EvmYul.UInt256)
    {targetGas : EvmYul.UInt256}
    (hGas :
      cfg.gasAvailableRel
        (yulParent.toMachineState.finishExternalCall ByteArray.empty
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    EvmYul.EVM.Θ fuel.succ.succ blobVersionedHashes
        evmParent.createdAccounts evmParent.genesisBlockHeader
        evmParent.blocks evmParent.accountMap evmParent.σ₀
        { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
          transactionReceipts := evmParent.transactionReceipts }
        evmParent.substate source origin recipient
        (.Code (Assembly.Bytecode.encodeTarget target))
        (EvmYul.UInt256.ofNat gasNat) gasPrice value weiValue calldata depth
        header perm =
      .ok (evmChild.createdAccounts,
        if evmChild.accountMap.isEmpty then evmParent.accountMap
        else evmChild.accountMap,
        evmChild.gasAvailable,
        if evmChild.accountMap.isEmpty then evmParent.substate
        else evmChild.substate,
        true, output) ∧
      ∃ yulAfter,
        EvmYul.Yul.restoreSuccessfulContractCallState
            (.Ok yulParent parentStore)
            (.Ok yulChild childStore)
            restoreStore ByteArray.empty inOffset inSize outOffset outSize =
          .ok (.Ok yulAfter restoreStore, [⟨1⟩]) ∧
        Reference.SharedStateRel cfg yulAfter
          { evmParent with
            toMachineState :=
              { evmParent.toMachineState.finishExternalCall output
                  inOffset inSize outOffset outSize with
                gasAvailable := targetGas }
            accountMap :=
              if evmChild.accountMap.isEmpty then
                evmParent.accountMap
              else
                evmChild.accountMap
            substate :=
              if evmChild.accountMap.isEmpty then
                evmParent.substate
              else
                evmChild.substate
            createdAccounts := evmChild.createdAccounts } := by
  exact
    ⟨Theta_code_success_of_X_installedCode hX,
      restoreSuccessfulContractCallState_of_XResultAgrees_running_success_empty_output
        hParent hParentWorld hCfgAccountMap
        parentStore childStore restoreStore
        hTargetChild hTargetChildWorld hAgree hChildGas
        inOffset inSize outOffset outSize hGas⟩

theorem ordinaryCodeCall_runningSuccessBranch_rel_afterAccess
    {cfg : Reference.StateRelConfig}
    {yulParent : EvmYul.SharedState .Yul}
    {evmParent : EvmYul.SharedState .EVM}
    (hParent : Reference.SharedStateRel cfg yulParent evmParent)
    (hParentWorld :
      CompiledAccountMapRel yulParent.accountMap evmParent.accountMap)
    (hCfgAccountMap :
      ∀ {yulMap : EvmYul.AccountMap .Yul}
        {evmMap : EvmYul.AccountMap .EVM},
        CompiledAccountMapRel yulMap evmMap →
          cfg.accountMapRel yulMap evmMap)
    (parentStore childStore restoreStore : EvmYul.Yul.VarStore)
    (addr : EvmYul.AccountAddress)
    {yulChild : EvmYul.SharedState .Yul}
    {targetChild evmChild : EVMState}
    {fuel gasNat : Nat}
    {blobVersionedHashes : List ByteArray}
    {source origin recipient : EvmYul.AccountAddress}
    {target : Assembly.TargetProgram}
    {gasPrice value weiValue : EvmYul.UInt256}
    {calldata output : ByteArray}
    {depth : Nat}
    {header : EvmYul.BlockHeader}
    {perm : Bool}
    (hTargetChild :
      Reference.SharedStateRel cfg yulChild targetChild.toSharedState)
    (hTargetChildWorld :
      CompiledAccountMapRel yulChild.accountMap targetChild.accountMap)
    (hX :
      EvmYul.EVM.X fuel (Assembly.GasAware.validJumps target)
          (thetaCodeXInitialState target gasNat blobVersionedHashes
            evmParent.createdAccounts evmParent.genesisBlockHeader
            evmParent.blocks evmParent.accountMap evmParent.σ₀
            { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
              transactionReceipts := evmParent.transactionReceipts }
            (EvmYul.State.addAccessedAccount evmParent.toState addr).substate
            source origin recipient gasPrice value weiValue calldata depth
            header perm) =
        .ok (.success evmChild output))
    (hAgree :
      Assembly.GasAware.XResultAgrees (.running targetChild)
        (.success evmChild output))
    (hChildGas :
      cfg.gasAvailableRel yulChild.toMachineState.gasAvailable
        evmChild.gasAvailable)
    (inOffset inSize outOffset outSize : EvmYul.UInt256)
    {targetGas : EvmYul.UInt256}
    (hGas :
      cfg.gasAvailableRel
        (yulParent.toMachineState.finishExternalCall ByteArray.empty
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    EvmYul.EVM.Θ fuel.succ.succ blobVersionedHashes
        evmParent.createdAccounts evmParent.genesisBlockHeader
        evmParent.blocks evmParent.accountMap evmParent.σ₀
        { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
          transactionReceipts := evmParent.transactionReceipts }
        (EvmYul.State.addAccessedAccount evmParent.toState addr).substate
        source origin recipient (.Code (Assembly.Bytecode.encodeTarget target))
        (EvmYul.UInt256.ofNat gasNat) gasPrice value weiValue calldata depth
        header perm =
      .ok (evmChild.createdAccounts,
        if evmChild.accountMap.isEmpty then evmParent.accountMap
        else evmChild.accountMap,
        evmChild.gasAvailable,
        if evmChild.accountMap.isEmpty then
          (EvmYul.State.addAccessedAccount evmParent.toState addr).substate
        else evmChild.substate,
        true, output) ∧
      ∃ yulAfter,
        EvmYul.Yul.restoreSuccessfulContractCallState
            (EvmYul.Yul.addAccessedAccount (.Ok yulParent parentStore) addr)
            (.Ok yulChild childStore)
            restoreStore ByteArray.empty inOffset inSize outOffset outSize =
          .ok (.Ok yulAfter restoreStore, [⟨1⟩]) ∧
        Reference.SharedStateRel cfg yulAfter
          { evmParent with
            toMachineState :=
              { evmParent.toMachineState.finishExternalCall output
                  inOffset inSize outOffset outSize with
                gasAvailable := targetGas }
            accountMap :=
              if evmChild.accountMap.isEmpty then
                evmParent.accountMap
              else
                evmChild.accountMap
            substate :=
              if evmChild.accountMap.isEmpty then
                (EvmYul.State.addAccessedAccount evmParent.toState addr).substate
              else
                evmChild.substate
            createdAccounts := evmChild.createdAccounts } := by
  let yulAccessed : EvmYul.SharedState .Yul :=
    { yulParent with
      toState := EvmYul.State.addAccessedAccount yulParent.toState addr }
  let evmAccessed : EvmYul.SharedState .EVM :=
    { evmParent with
      toState := EvmYul.State.addAccessedAccount evmParent.toState addr }
  have hParentAccessed :
      Reference.SharedStateRel cfg yulAccessed evmAccessed := by
    simpa [yulAccessed, evmAccessed] using
      sharedStateRel_addAccessedAccount hParent addr
  have hParentWorldAccessed :
      CompiledAccountMapRel yulAccessed.accountMap evmAccessed.accountMap := by
    simpa [yulAccessed, evmAccessed] using hParentWorld
  have hXAccessed :
      EvmYul.EVM.X fuel (Assembly.GasAware.validJumps target)
          (thetaCodeXInitialState target gasNat blobVersionedHashes
            evmAccessed.createdAccounts evmAccessed.genesisBlockHeader
            evmAccessed.blocks evmAccessed.accountMap evmAccessed.σ₀
            { totalGasUsedInBlock := evmAccessed.totalGasUsedInBlock
              transactionReceipts := evmAccessed.transactionReceipts }
            evmAccessed.substate source origin recipient gasPrice value
            weiValue calldata depth header perm) =
        .ok (.success evmChild output) := by
    simpa [evmAccessed] using hX
  have hGasAccessed :
      cfg.gasAvailableRel
        (yulAccessed.toMachineState.finishExternalCall ByteArray.empty
          inOffset inSize outOffset outSize).gasAvailable
        targetGas := by
    simpa [yulAccessed] using hGas
  simpa [yulAccessed, evmAccessed, EvmYul.Yul.addAccessedAccount,
    EvmYul.Yul.State.setState, EvmYul.Yul.State.toState,
    EvmYul.State.addAccessedAccount]
    using
      ordinaryCodeCall_runningSuccessBranch_rel
        hParentAccessed hParentWorldAccessed hCfgAccountMap
        parentStore childStore restoreStore
        hTargetChild hTargetChildWorld hXAccessed hAgree hChildGas
        inOffset inSize outOffset outSize hGasAccessed

theorem ordinaryCodeCall_runningSuccessBranch_rel_of_childOutcome
    {varStackRel : Reference.VarStackRel}
    {terminalCfgRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop}
    {revertCfgRel : Reference.State → EVMState → Prop}
    {gasAvailableRel : Word → Word → Prop}
    {gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm}
    {totalGasRel : Nat → Nat → Prop}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {program : Program}
    {initialShared yulParent yulChild : EvmYul.SharedState .Yul}
    {evmParent : EvmYul.SharedState .EVM}
    {initialStore parentStore childStore restoreStore :
      EvmYul.Yul.VarStore}
    {sourceOutcome : Objects.Source.Outcome}
    {targetOutcome : Assembly.StepResult}
    {evmResult : EvmYul.EVM.ExecutionResult EVMState}
    (hParent :
      Reference.SharedStateRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        yulParent evmParent)
    (hOutcomeRel :
      Program.RecursiveBridgeSemanticContracts.dispatcherOutcomeRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        terminalRel revertRel program (.Ok initialShared initialStore)
        (.regular (.Ok yulChild childStore)) sourceOutcome)
    (hWhole :
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome)
    {fuel gasNat : Nat}
    {blobVersionedHashes : List ByteArray}
    {source origin recipient : EvmYul.AccountAddress}
    {target : Assembly.TargetProgram}
    {gasPrice value weiValue : EvmYul.UInt256}
    {calldata : ByteArray}
    {depth : Nat}
    {header : EvmYul.BlockHeader}
    {perm : Bool}
    (hX :
      EvmYul.EVM.X fuel (Assembly.GasAware.validJumps target)
          (thetaCodeXInitialState target gasNat blobVersionedHashes
            evmParent.createdAccounts evmParent.genesisBlockHeader
            evmParent.blocks evmParent.accountMap evmParent.σ₀
            { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
              transactionReceipts := evmParent.transactionReceipts }
            evmParent.substate source origin recipient gasPrice value
            weiValue calldata depth header perm) =
        .ok evmResult)
    (hAgree :
      Assembly.GasAware.XResultAgrees targetOutcome evmResult)
    (hTargetChildGas :
      ∀ {targetChild}, targetOutcome = .running targetChild →
        gasAvailableRel yulChild.toMachineState.gasAvailable
          targetChild.gasAvailable)
    (hEvmChildGas :
      ∀ {evmChild output}, evmResult = .success evmChild output →
        gasAvailableRel yulChild.toMachineState.gasAvailable
          evmChild.gasAvailable)
    (inOffset inSize outOffset outSize : EvmYul.UInt256)
    {targetGas : EvmYul.UInt256}
    (hGas :
      gasAvailableRel
        (yulParent.toMachineState.finishExternalCall ByteArray.empty
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    ∃ targetChild evmChild output,
      targetOutcome = .running targetChild ∧
        evmResult = .success evmChild output ∧
        EvmYul.EVM.Θ fuel.succ.succ blobVersionedHashes
          evmParent.createdAccounts evmParent.genesisBlockHeader
          evmParent.blocks evmParent.accountMap evmParent.σ₀
          { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
            transactionReceipts := evmParent.transactionReceipts }
          evmParent.substate source origin recipient
          (.Code (Assembly.Bytecode.encodeTarget target))
          (EvmYul.UInt256.ofNat gasNat) gasPrice value weiValue calldata depth
          header perm =
            .ok (evmChild.createdAccounts,
              if evmChild.accountMap.isEmpty then evmParent.accountMap
              else evmChild.accountMap,
              evmChild.gasAvailable,
              if evmChild.accountMap.isEmpty then evmParent.substate
              else evmChild.substate,
              true, output) ∧
        ∃ yulAfter,
          EvmYul.Yul.restoreSuccessfulContractCallState
              (.Ok yulParent parentStore)
              (.Ok yulChild childStore)
              restoreStore ByteArray.empty inOffset inSize outOffset outSize =
            .ok (.Ok yulAfter restoreStore, [⟨1⟩]) ∧
          Reference.SharedStateRel
            (stateRelConfig varStackRel terminalCfgRel revertCfgRel
              gasAvailableRel gasValueRel totalGasRel)
            yulAfter
            { evmParent with
              toMachineState :=
                { evmParent.toMachineState.finishExternalCall output
                    inOffset inSize outOffset outSize with
                  gasAvailable := targetGas }
              accountMap :=
                if evmChild.accountMap.isEmpty then
                  evmParent.accountMap
                else
                  evmChild.accountMap
              substate :=
                if evmChild.accountMap.isEmpty then
                  evmParent.substate
                else
                  evmChild.substate
              createdAccounts := evmChild.createdAccounts } := by
  rcases
      dispatcherOutcomeRel_regular_ok_whole_childRelations
        (varStackRel := varStackRel)
        (terminalCfgRel := terminalCfgRel)
        (revertCfgRel := revertCfgRel)
        (gasAvailableRel := gasAvailableRel)
        (gasValueRel := gasValueRel)
        (totalGasRel := totalGasRel)
        hOutcomeRel hWhole hTargetChildGas with
    ⟨targetChild, hTargetOutcome, hTargetChild, hTargetChildWorld⟩
  have hAgreeRunning :
      Assembly.GasAware.XResultAgrees (.running targetChild) evmResult := by
    simpa [hTargetOutcome] using hAgree
  rcases XResultAgrees_running_success_shape hAgreeRunning with
    ⟨evmChild, output, hResult, hAgreeSuccess⟩
  have hXSuccess :
      EvmYul.EVM.X fuel (Assembly.GasAware.validJumps target)
          (thetaCodeXInitialState target gasNat blobVersionedHashes
            evmParent.createdAccounts evmParent.genesisBlockHeader
            evmParent.blocks evmParent.accountMap evmParent.σ₀
            { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
              transactionReceipts := evmParent.transactionReceipts }
            evmParent.substate source origin recipient gasPrice value
            weiValue calldata depth header perm) =
        .ok (.success evmChild output) := by
    simpa [hResult] using hX
  have hParentWorld :
      CompiledAccountMapRel yulParent.accountMap evmParent.accountMap :=
    compiledAccountMapRel_of_sharedStateRel_stateRelConfig hParent
  have hCfgAccountMap :
      ∀ {yulMap : EvmYul.AccountMap .Yul}
        {evmMap : EvmYul.AccountMap .EVM},
        CompiledAccountMapRel yulMap evmMap →
          (stateRelConfig varStackRel terminalCfgRel revertCfgRel
            gasAvailableRel gasValueRel totalGasRel).accountMapRel
            yulMap evmMap := by
    intro yulMap evmMap hRel
    exact stateRelConfig_accountMapRel_of_compiledAccountMapRel hRel
  rcases
      ordinaryCodeCall_runningSuccessBranch_rel
        (cfg :=
          stateRelConfig varStackRel terminalCfgRel revertCfgRel
            gasAvailableRel gasValueRel totalGasRel)
        hParent hParentWorld hCfgAccountMap
        parentStore childStore restoreStore
        hTargetChild hTargetChildWorld hXSuccess hAgreeSuccess
        (hEvmChildGas hResult)
        inOffset inSize outOffset outSize hGas with
    ⟨hTheta, hRestore⟩
  exact ⟨targetChild, evmChild, output, hTargetOutcome, hResult,
    hTheta, hRestore⟩

theorem ordinaryCodeCall_runningSuccessBranch_rel_of_childOutcome_afterAccess
    {varStackRel : Reference.VarStackRel}
    {terminalCfgRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop}
    {revertCfgRel : Reference.State → EVMState → Prop}
    {gasAvailableRel : Word → Word → Prop}
    {gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm}
    {totalGasRel : Nat → Nat → Prop}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {program : Program}
    {initialShared yulParent yulChild : EvmYul.SharedState .Yul}
    {evmParent : EvmYul.SharedState .EVM}
    {initialStore parentStore childStore restoreStore :
      EvmYul.Yul.VarStore}
    {sourceOutcome : Objects.Source.Outcome}
    {targetOutcome : Assembly.StepResult}
    {evmResult : EvmYul.EVM.ExecutionResult EVMState}
    (hParent :
      Reference.SharedStateRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        yulParent evmParent)
    (hOutcomeRel :
      Program.RecursiveBridgeSemanticContracts.dispatcherOutcomeRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        terminalRel revertRel program (.Ok initialShared initialStore)
        (.regular (.Ok yulChild childStore)) sourceOutcome)
    (hWhole :
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome)
    {fuel gasNat : Nat}
    {blobVersionedHashes : List ByteArray}
    {source origin recipient addr : EvmYul.AccountAddress}
    {target : Assembly.TargetProgram}
    {gasPrice value weiValue : EvmYul.UInt256}
    {calldata : ByteArray}
    {depth : Nat}
    {header : EvmYul.BlockHeader}
    {perm : Bool}
    (hX :
      EvmYul.EVM.X fuel (Assembly.GasAware.validJumps target)
          (thetaCodeXInitialState target gasNat blobVersionedHashes
            evmParent.createdAccounts evmParent.genesisBlockHeader
            evmParent.blocks evmParent.accountMap evmParent.σ₀
            { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
              transactionReceipts := evmParent.transactionReceipts }
            (EvmYul.State.addAccessedAccount evmParent.toState addr).substate
            source origin recipient gasPrice value weiValue calldata depth
            header perm) =
        .ok evmResult)
    (hAgree :
      Assembly.GasAware.XResultAgrees targetOutcome evmResult)
    (hTargetChildGas :
      ∀ {targetChild}, targetOutcome = .running targetChild →
        gasAvailableRel yulChild.toMachineState.gasAvailable
          targetChild.gasAvailable)
    (hEvmChildGas :
      ∀ {evmChild output}, evmResult = .success evmChild output →
        gasAvailableRel yulChild.toMachineState.gasAvailable
          evmChild.gasAvailable)
    (inOffset inSize outOffset outSize : EvmYul.UInt256)
    {targetGas : EvmYul.UInt256}
    (hGas :
      gasAvailableRel
        (yulParent.toMachineState.finishExternalCall ByteArray.empty
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    ∃ targetChild evmChild output,
      targetOutcome = .running targetChild ∧
        evmResult = .success evmChild output ∧
        EvmYul.EVM.Θ fuel.succ.succ blobVersionedHashes
          evmParent.createdAccounts evmParent.genesisBlockHeader
          evmParent.blocks evmParent.accountMap evmParent.σ₀
          { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
            transactionReceipts := evmParent.transactionReceipts }
          (EvmYul.State.addAccessedAccount evmParent.toState addr).substate
          source origin recipient (.Code (Assembly.Bytecode.encodeTarget target))
          (EvmYul.UInt256.ofNat gasNat) gasPrice value weiValue calldata depth
          header perm =
            .ok (evmChild.createdAccounts,
              if evmChild.accountMap.isEmpty then evmParent.accountMap
              else evmChild.accountMap,
              evmChild.gasAvailable,
              if evmChild.accountMap.isEmpty then
                (EvmYul.State.addAccessedAccount
                  evmParent.toState addr).substate
              else evmChild.substate,
              true, output) ∧
        ∃ yulAfter,
          EvmYul.Yul.restoreSuccessfulContractCallState
              (EvmYul.Yul.addAccessedAccount
                (.Ok yulParent parentStore) addr)
              (.Ok yulChild childStore)
              restoreStore ByteArray.empty inOffset inSize outOffset outSize =
            .ok (.Ok yulAfter restoreStore, [⟨1⟩]) ∧
          Reference.SharedStateRel
            (stateRelConfig varStackRel terminalCfgRel revertCfgRel
              gasAvailableRel gasValueRel totalGasRel)
            yulAfter
            { evmParent with
              toMachineState :=
                { evmParent.toMachineState.finishExternalCall output
                    inOffset inSize outOffset outSize with
                  gasAvailable := targetGas }
              accountMap :=
                if evmChild.accountMap.isEmpty then
                  evmParent.accountMap
                else
                  evmChild.accountMap
              substate :=
                if evmChild.accountMap.isEmpty then
                  (EvmYul.State.addAccessedAccount
                    evmParent.toState addr).substate
                else
                  evmChild.substate
              createdAccounts := evmChild.createdAccounts } := by
  let yulAccessed : EvmYul.SharedState .Yul :=
    { yulParent with
      toState := EvmYul.State.addAccessedAccount yulParent.toState addr }
  let evmAccessed : EvmYul.SharedState .EVM :=
    { evmParent with
      toState := EvmYul.State.addAccessedAccount evmParent.toState addr }
  have hParentAccessed :
      Reference.SharedStateRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        yulAccessed evmAccessed := by
    simpa [yulAccessed, evmAccessed] using
      sharedStateRel_addAccessedAccount hParent addr
  have hXAccessed :
      EvmYul.EVM.X fuel (Assembly.GasAware.validJumps target)
          (thetaCodeXInitialState target gasNat blobVersionedHashes
            evmAccessed.createdAccounts evmAccessed.genesisBlockHeader
            evmAccessed.blocks evmAccessed.accountMap evmAccessed.σ₀
            { totalGasUsedInBlock := evmAccessed.totalGasUsedInBlock
              transactionReceipts := evmAccessed.transactionReceipts }
            evmAccessed.substate source origin recipient gasPrice value
            weiValue calldata depth header perm) =
        .ok evmResult := by
    simpa [evmAccessed] using hX
  have hGasAccessed :
      gasAvailableRel
        (yulAccessed.toMachineState.finishExternalCall ByteArray.empty
          inOffset inSize outOffset outSize).gasAvailable
        targetGas := by
    simpa [yulAccessed] using hGas
  simpa [yulAccessed, evmAccessed, EvmYul.Yul.addAccessedAccount,
    EvmYul.Yul.State.setState, EvmYul.Yul.State.toState,
    EvmYul.State.addAccessedAccount]
    using
      ordinaryCodeCall_runningSuccessBranch_rel_of_childOutcome
        (varStackRel := varStackRel)
        (terminalCfgRel := terminalCfgRel)
        (revertCfgRel := revertCfgRel)
        (gasAvailableRel := gasAvailableRel)
        (gasValueRel := gasValueRel)
        (totalGasRel := totalGasRel)
        hParentAccessed hOutcomeRel hWhole hXAccessed hAgree
        hTargetChildGas hEvmChildGas inOffset inSize outOffset outSize
        hGasAccessed

theorem ordinaryCodeCall_runningSuccessBranch_rel_of_childOutcome_afterAccess_withTargetGas
    {varStackRel : Reference.VarStackRel}
    {terminalCfgRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop}
    {revertCfgRel : Reference.State → EVMState → Prop}
    {gasAvailableRel : Word → Word → Prop}
    {gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm}
    {totalGasRel : Nat → Nat → Prop}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {program : Program}
    {initialShared yulParent yulChild : EvmYul.SharedState .Yul}
    {evmParent : EvmYul.SharedState .EVM}
    {initialStore parentStore childStore restoreStore :
      EvmYul.Yul.VarStore}
    {sourceOutcome : Objects.Source.Outcome}
    {targetOutcome : Assembly.StepResult}
    {evmResult : EvmYul.EVM.ExecutionResult EVMState}
    (hParent :
      Reference.SharedStateRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        yulParent evmParent)
    (hOutcomeRel :
      Program.RecursiveBridgeSemanticContracts.dispatcherOutcomeRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        terminalRel revertRel program (.Ok initialShared initialStore)
        (.regular (.Ok yulChild childStore)) sourceOutcome)
    (hWhole :
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome)
    {fuel gasNat : Nat}
    {blobVersionedHashes : List ByteArray}
    {source origin recipient addr : EvmYul.AccountAddress}
    {target : Assembly.TargetProgram}
    {gasPrice value weiValue : EvmYul.UInt256}
    {calldata : ByteArray}
    {depth : Nat}
    {header : EvmYul.BlockHeader}
    {perm : Bool}
    (hX :
      EvmYul.EVM.X fuel (Assembly.GasAware.validJumps target)
          (thetaCodeXInitialState target gasNat blobVersionedHashes
            evmParent.createdAccounts evmParent.genesisBlockHeader
            evmParent.blocks evmParent.accountMap evmParent.σ₀
            { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
              transactionReceipts := evmParent.transactionReceipts }
            (EvmYul.State.addAccessedAccount evmParent.toState addr).substate
            source origin recipient gasPrice value weiValue calldata depth
            header perm) =
        .ok evmResult)
    (hAgree :
      Assembly.GasAware.XResultAgrees targetOutcome evmResult)
    (hTargetChildGas :
      ∀ {targetChild}, targetOutcome = .running targetChild →
        gasAvailableRel yulChild.toMachineState.gasAvailable
          targetChild.gasAvailable)
    (hEvmChildGas :
      ∀ {evmChild output}, evmResult = .success evmChild output →
        gasAvailableRel yulChild.toMachineState.gasAvailable
          evmChild.gasAvailable)
    (inOffset inSize outOffset outSize : EvmYul.UInt256)
    (targetGasOf : EVMState → ByteArray → EvmYul.UInt256)
    (hReturnedGas :
      ∀ {targetOutcome evmChild output},
        SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome →
          Assembly.GasAware.XResultAgrees targetOutcome
            (.success evmChild output) →
          gasAvailableRel
            (yulParent.toMachineState.finishExternalCall ByteArray.empty
              inOffset inSize outOffset outSize).gasAvailable
            (targetGasOf evmChild output)) :
    ∃ targetChild evmChild output,
      targetOutcome = .running targetChild ∧
        evmResult = .success evmChild output ∧
        EvmYul.EVM.Θ fuel.succ.succ blobVersionedHashes
          evmParent.createdAccounts evmParent.genesisBlockHeader
          evmParent.blocks evmParent.accountMap evmParent.σ₀
          { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
            transactionReceipts := evmParent.transactionReceipts }
          (EvmYul.State.addAccessedAccount evmParent.toState addr).substate
          source origin recipient (.Code (Assembly.Bytecode.encodeTarget target))
          (EvmYul.UInt256.ofNat gasNat) gasPrice value weiValue calldata depth
          header perm =
            .ok (evmChild.createdAccounts,
              if evmChild.accountMap.isEmpty then evmParent.accountMap
              else evmChild.accountMap,
              evmChild.gasAvailable,
              if evmChild.accountMap.isEmpty then
                (EvmYul.State.addAccessedAccount
                  evmParent.toState addr).substate
              else evmChild.substate,
              true, output) ∧
        ∃ yulAfter,
          EvmYul.Yul.restoreSuccessfulContractCallState
              (EvmYul.Yul.addAccessedAccount
                (.Ok yulParent parentStore) addr)
              (.Ok yulChild childStore)
              restoreStore ByteArray.empty inOffset inSize outOffset outSize =
            .ok (.Ok yulAfter restoreStore, [⟨1⟩]) ∧
          Reference.SharedStateRel
            (stateRelConfig varStackRel terminalCfgRel revertCfgRel
              gasAvailableRel gasValueRel totalGasRel)
            yulAfter
            { evmParent with
              toMachineState :=
                { evmParent.toMachineState.finishExternalCall output
                    inOffset inSize outOffset outSize with
                  gasAvailable := targetGasOf evmChild output }
              accountMap :=
                if evmChild.accountMap.isEmpty then
                  evmParent.accountMap
                else
                  evmChild.accountMap
              substate :=
                if evmChild.accountMap.isEmpty then
                  (EvmYul.State.addAccessedAccount
                    evmParent.toState addr).substate
                else
                  evmChild.substate
              createdAccounts := evmChild.createdAccounts } := by
  rcases
      dispatcherOutcomeRel_regular_ok_whole_childRelations
        (varStackRel := varStackRel)
        (terminalCfgRel := terminalCfgRel)
        (revertCfgRel := revertCfgRel)
        (gasAvailableRel := gasAvailableRel)
        (gasValueRel := gasValueRel)
        (totalGasRel := totalGasRel)
        hOutcomeRel hWhole hTargetChildGas with
    ⟨targetChild, hTargetOutcome, hTargetChild, hTargetChildWorld⟩
  have hAgreeRunning :
      Assembly.GasAware.XResultAgrees (.running targetChild) evmResult := by
    simpa [hTargetOutcome] using hAgree
  rcases XResultAgrees_running_success_shape hAgreeRunning with
    ⟨evmChild, output, hResult, hAgreeSuccess⟩
  have hXSuccess :
      EvmYul.EVM.X fuel (Assembly.GasAware.validJumps target)
          (thetaCodeXInitialState target gasNat blobVersionedHashes
            evmParent.createdAccounts evmParent.genesisBlockHeader
            evmParent.blocks evmParent.accountMap evmParent.σ₀
            { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
              transactionReceipts := evmParent.transactionReceipts }
            (EvmYul.State.addAccessedAccount evmParent.toState addr).substate
            source origin recipient gasPrice value weiValue calldata depth
            header perm) =
        .ok (.success evmChild output) := by
    simpa [hResult] using hX
  have hParentWorld :
      CompiledAccountMapRel yulParent.accountMap evmParent.accountMap :=
    compiledAccountMapRel_of_sharedStateRel_stateRelConfig hParent
  have hCfgAccountMap :
      ∀ {yulMap : EvmYul.AccountMap .Yul}
        {evmMap : EvmYul.AccountMap .EVM},
        CompiledAccountMapRel yulMap evmMap →
          (stateRelConfig varStackRel terminalCfgRel revertCfgRel
            gasAvailableRel gasValueRel totalGasRel).accountMapRel
            yulMap evmMap := by
    intro yulMap evmMap hRel
    exact stateRelConfig_accountMapRel_of_compiledAccountMapRel hRel
  have hGasSuccess :
      gasAvailableRel
        (yulParent.toMachineState.finishExternalCall ByteArray.empty
          inOffset inSize outOffset outSize).gasAvailable
        (targetGasOf evmChild output) :=
    hReturnedGas hWhole (by simpa [hTargetOutcome] using hAgreeSuccess)
  rcases
      ordinaryCodeCall_runningSuccessBranch_rel_afterAccess
        (cfg :=
          stateRelConfig varStackRel terminalCfgRel revertCfgRel
            gasAvailableRel gasValueRel totalGasRel)
        hParent hParentWorld hCfgAccountMap
        parentStore childStore restoreStore addr
        hTargetChild hTargetChildWorld hXSuccess hAgreeSuccess
        (hEvmChildGas hResult)
        inOffset inSize outOffset outSize hGasSuccess with
    ⟨hTheta, hRestore⟩
  exact ⟨targetChild, evmChild, output, hTargetOutcome, hResult,
    hTheta, hRestore⟩

theorem ordinaryCodeCall_runningSuccessBranch_rel_of_installed_childDispatcher
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {varStackRel : Reference.VarStackRel}
    {terminalCfgRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop}
    {revertCfgRel : Reference.State → EVMState → Prop}
    {gasAvailableRel : Word → Word → Prop}
    {gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm}
    {totalGasRel : Nat → Nat → Prop}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    {referenceFuel sourceFuel gasNat : Nat}
    {initialShared yulParent yulChild : EvmYul.SharedState .Yul}
    {evmParent : EvmYul.SharedState .EVM}
    {initialStore parentStore childStore restoreStore :
      EvmYul.Yul.VarStore}
    {rets : List EvmYul.UInt256}
    {sourceOutcome : Objects.Source.Outcome}
    (hParent :
      Reference.SharedStateRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        yulParent evmParent)
    (hInstalled : initialShared.executionEnv.code = program.contract)
    (hCall :
      EvmYul.Yul.callDispatcher referenceFuel (some program.contract)
          (.Ok initialShared initialStore) =
        .ok (.Ok yulChild childStore, rets))
    {blobVersionedHashes : List ByteArray}
    {source origin recipient : EvmYul.AccountAddress}
    {gasPrice value weiValue : EvmYul.UInt256}
    {calldata : ByteArray}
    {depth : Nat}
    {header : EvmYul.BlockHeader}
    {perm : Bool}
    (hSourceRun :
      SourceLowered.run prim sourceFuel program
          (Assembly.GasAware.installCodeAndGas target gasNat
            (thetaCodeRawInitialState target gasNat blobVersionedHashes
              evmParent.createdAccounts evmParent.genesisBlockHeader
              evmParent.blocks evmParent.accountMap evmParent.σ₀
              { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
                transactionReceipts := evmParent.transactionReceipts }
              evmParent.substate source origin recipient gasPrice value
              weiValue calldata depth header perm)) =
        .ok sourceOutcome)
    (hOutcomeRel :
      Program.RecursiveBridgeSemanticContracts.dispatcherOutcomeRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        terminalRel revertRel program (.Ok initialShared initialStore)
        (.regular (.Ok yulChild childStore)) sourceOutcome)
    (hCompileBoundary :
      compileCheckedAssemblyTargetBytecodeResourcesSourceStatic? program =
        some (asm, target))
    (hTargetGasForX :
      ∀ {targetFuel targetOutcome},
        Assembly.Preservation.BlockTraceResult asm target targetFuel
          (Assembly.GasAware.installCodeAndGas target gasNat
            (thetaCodeRawInitialState target gasNat blobVersionedHashes
              evmParent.createdAccounts evmParent.genesisBlockHeader
              evmParent.blocks evmParent.accountMap evmParent.σ₀
              { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
                transactionReceipts := evmParent.transactionReceipts }
              evmParent.substate source origin recipient gasPrice value
              weiValue calldata depth header perm))
          targetOutcome →
        Assembly.GasAware.XResultPreconditionAssumptions target
          (Assembly.GasAware.installCodeAndGas target gasNat
            (thetaCodeRawInitialState target gasNat blobVersionedHashes
              evmParent.createdAccounts evmParent.genesisBlockHeader
              evmParent.blocks evmParent.accountMap evmParent.σ₀
              { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
                transactionReceipts := evmParent.transactionReceipts }
              evmParent.substate source origin recipient gasPrice value
              weiValue calldata depth header perm))
          targetOutcome)
    (hGasBound :
      ∀ {targetFuel targetOutcome}
        (hTrace :
          Assembly.Preservation.BlockTraceResult asm target targetFuel
            (Assembly.GasAware.installCodeAndGas target gasNat
              (thetaCodeRawInitialState target gasNat blobVersionedHashes
                evmParent.createdAccounts evmParent.genesisBlockHeader
                evmParent.blocks evmParent.accountMap evmParent.σ₀
                { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
                  transactionReceipts := evmParent.transactionReceipts }
                evmParent.substate source origin recipient gasPrice value
                weiValue calldata depth header perm))
            targetOutcome),
        (hTargetGasForX hTrace).gasBound ≤ gasNat)
    (hUInt256 : gasNat < EvmYul.UInt256.size)
    (hTargetChildGas :
      ∀ {targetChild}, SourceLowered.WholeProgramOutcomeRel sourceOutcome
          (.running targetChild) →
        gasAvailableRel yulChild.toMachineState.gasAvailable
          targetChild.gasAvailable)
    (hEvmChildGas :
      ∀ {targetOutcome evmChild output},
        SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome →
          Assembly.GasAware.XResultAgrees targetOutcome
            (.success evmChild output) →
          gasAvailableRel yulChild.toMachineState.gasAvailable
            evmChild.gasAvailable)
    (inOffset inSize outOffset outSize : EvmYul.UInt256)
    {targetGas : EvmYul.UInt256}
    (hGas :
      gasAvailableRel
        (yulParent.toMachineState.finishExternalCall ByteArray.empty
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    ∃ (evmFuel : Nat) (targetChild evmChild : EVMState) (output : ByteArray),
      EvmYul.Yul.callDispatcher referenceFuel (some program.contract)
          (.Ok initialShared initialStore) =
        .ok (.Ok yulChild childStore, rets) ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome
        (.running targetChild) ∧
        EvmYul.EVM.Θ evmFuel.succ.succ blobVersionedHashes
          evmParent.createdAccounts evmParent.genesisBlockHeader
          evmParent.blocks evmParent.accountMap evmParent.σ₀
          { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
            transactionReceipts := evmParent.transactionReceipts }
          evmParent.substate source origin recipient
          (.Code (Assembly.Bytecode.encodeTarget target))
          (EvmYul.UInt256.ofNat gasNat) gasPrice value weiValue calldata depth
          header perm =
            .ok (evmChild.createdAccounts,
              if evmChild.accountMap.isEmpty then evmParent.accountMap
              else evmChild.accountMap,
              evmChild.gasAvailable,
              if evmChild.accountMap.isEmpty then evmParent.substate
              else evmChild.substate,
              true, output) ∧
        ∃ yulAfter,
          EvmYul.Yul.restoreSuccessfulContractCallState
              (.Ok yulParent parentStore)
              (.Ok yulChild childStore)
              restoreStore ByteArray.empty inOffset inSize outOffset outSize =
            .ok (.Ok yulAfter restoreStore, [⟨1⟩]) ∧
          Reference.SharedStateRel
            (stateRelConfig varStackRel terminalCfgRel revertCfgRel
              gasAvailableRel gasValueRel totalGasRel)
            yulAfter
            { evmParent with
              toMachineState :=
                { evmParent.toMachineState.finishExternalCall output
                    inOffset inSize outOffset outSize with
                  gasAvailable := targetGas }
              accountMap :=
                if evmChild.accountMap.isEmpty then
                  evmParent.accountMap
                else
                  evmChild.accountMap
              substate :=
                if evmChild.accountMap.isEmpty then
                  evmParent.substate
                else
                  evmChild.substate
              createdAccounts := evmChild.createdAccounts } := by
  rcases
      compile_preserves_of_installed_callDispatcher_regular_sourceStaticBoundary_installedGas_XResult
        (prim := prim) hPrim
        (outcomeRel :=
          Program.RecursiveBridgeSemanticContracts.dispatcherOutcomeRel
            (stateRelConfig varStackRel terminalCfgRel revertCfgRel
              gasAvailableRel gasValueRel totalGasRel)
            terminalRel revertRel program (.Ok initialShared initialStore))
        (program := program) (asm := asm) (target := target)
        (referenceFuel := referenceFuel) (sourceFuel := sourceFuel)
        (gas := gasNat) (shared := initialShared)
        (store := initialStore) (state' := .Ok yulChild childStore)
        (rets := rets)
        (rawInitial :=
          thetaCodeRawInitialState target gasNat blobVersionedHashes
            evmParent.createdAccounts evmParent.genesisBlockHeader
            evmParent.blocks evmParent.accountMap evmParent.σ₀
            { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
              transactionReceipts := evmParent.transactionReceipts }
            evmParent.substate source origin recipient gasPrice value
            weiValue calldata depth header perm)
        (sourceOutcome := sourceOutcome)
        hInstalled hCall hSourceRun hOutcomeRel hCompileBoundary
        (by
          simp [thetaCodeRawInitialState, Assembly.GasAware.installCodeAndGas])
        (by
          simp [thetaCodeRawInitialState, Assembly.GasAware.installCodeAndGas])
        hTargetGasForX hGasBound hUInt256 with
    ⟨_targetFuel, targetOutcome, evmFuel, _gasBound, evmResult,
      _hReferenceRun, _hTargetRun, _hOutcomeRel, hWhole, _hTrace,
      _hGasBound, hX, hAgree, _hDecode, _hJumpdest⟩
  have hXTheta :
      EvmYul.EVM.X evmFuel (Assembly.GasAware.validJumps target)
          (thetaCodeXInitialState target gasNat blobVersionedHashes
            evmParent.createdAccounts evmParent.genesisBlockHeader
            evmParent.blocks evmParent.accountMap evmParent.σ₀
            { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
              transactionReceipts := evmParent.transactionReceipts }
            evmParent.substate source origin recipient gasPrice value
            weiValue calldata depth header perm) =
        .ok evmResult := by
    simpa [thetaCodeXInitialState] using hX
  rcases
      ordinaryCodeCall_runningSuccessBranch_rel_of_childOutcome
        (varStackRel := varStackRel)
        (terminalCfgRel := terminalCfgRel)
        (revertCfgRel := revertCfgRel)
        (gasAvailableRel := gasAvailableRel)
        (gasValueRel := gasValueRel)
        (totalGasRel := totalGasRel)
        hParent hOutcomeRel hWhole hXTheta hAgree
        (by
          intro targetChild hTarget
          exact hTargetChildGas (by simpa [hTarget] using hWhole))
        (by
          intro evmChild output hResult
          exact hEvmChildGas hWhole (by simpa [hResult] using hAgree))
        inOffset inSize outOffset outSize hGas with
    ⟨targetChild, evmChild, output, hTargetOutcome, _hResult,
      hTheta, hRestore⟩
  exact
    ⟨evmFuel, targetChild, evmChild, output, hCall,
      by simpa [hTargetOutcome] using hWhole, hTheta, hRestore⟩

theorem ordinaryCodeCall_runningSuccessBranch_rel_of_installed_childDispatcher_afterAccess
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {varStackRel : Reference.VarStackRel}
    {terminalCfgRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop}
    {revertCfgRel : Reference.State → EVMState → Prop}
    {gasAvailableRel : Word → Word → Prop}
    {gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm}
    {totalGasRel : Nat → Nat → Prop}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    {referenceFuel sourceFuel gasNat : Nat}
    {initialShared yulParent yulChild : EvmYul.SharedState .Yul}
    {evmParent : EvmYul.SharedState .EVM}
    {initialStore parentStore childStore restoreStore :
      EvmYul.Yul.VarStore}
    {rets : List EvmYul.UInt256}
    {sourceOutcome : Objects.Source.Outcome}
    (hParent :
      Reference.SharedStateRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        yulParent evmParent)
    (hInstalled : initialShared.executionEnv.code = program.contract)
    (hCall :
      EvmYul.Yul.callDispatcher referenceFuel (some program.contract)
          (.Ok initialShared initialStore) =
        .ok (.Ok yulChild childStore, rets))
    {blobVersionedHashes : List ByteArray}
    {source origin recipient addr : EvmYul.AccountAddress}
    {gasPrice value weiValue : EvmYul.UInt256}
    {calldata : ByteArray}
    {depth : Nat}
    {header : EvmYul.BlockHeader}
    {perm : Bool}
    (hSourceRun :
      SourceLowered.run prim sourceFuel program
          (Assembly.GasAware.installCodeAndGas target gasNat
            (thetaCodeRawInitialState target gasNat blobVersionedHashes
              evmParent.createdAccounts evmParent.genesisBlockHeader
              evmParent.blocks evmParent.accountMap evmParent.σ₀
              { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
                transactionReceipts := evmParent.transactionReceipts }
              (EvmYul.State.addAccessedAccount evmParent.toState addr).substate
              source origin recipient gasPrice value weiValue calldata depth
              header perm)) =
        .ok sourceOutcome)
    (hOutcomeRel :
      Program.RecursiveBridgeSemanticContracts.dispatcherOutcomeRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        terminalRel revertRel program (.Ok initialShared initialStore)
        (.regular (.Ok yulChild childStore)) sourceOutcome)
    (hCompileBoundary :
      compileCheckedAssemblyTargetBytecodeResourcesSourceStatic? program =
        some (asm, target))
    (hTargetGasForX :
      ∀ {targetFuel targetOutcome},
        Assembly.Preservation.BlockTraceResult asm target targetFuel
          (Assembly.GasAware.installCodeAndGas target gasNat
            (thetaCodeRawInitialState target gasNat blobVersionedHashes
              evmParent.createdAccounts evmParent.genesisBlockHeader
              evmParent.blocks evmParent.accountMap evmParent.σ₀
              { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
                transactionReceipts := evmParent.transactionReceipts }
              (EvmYul.State.addAccessedAccount evmParent.toState addr).substate
              source origin recipient gasPrice value weiValue calldata depth
              header perm))
          targetOutcome →
        Assembly.GasAware.XResultPreconditionAssumptions target
          (Assembly.GasAware.installCodeAndGas target gasNat
            (thetaCodeRawInitialState target gasNat blobVersionedHashes
              evmParent.createdAccounts evmParent.genesisBlockHeader
              evmParent.blocks evmParent.accountMap evmParent.σ₀
              { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
                transactionReceipts := evmParent.transactionReceipts }
              (EvmYul.State.addAccessedAccount evmParent.toState addr).substate
              source origin recipient gasPrice value weiValue calldata depth
              header perm))
          targetOutcome)
    (hGasBound :
      ∀ {targetFuel targetOutcome}
        (hTrace :
          Assembly.Preservation.BlockTraceResult asm target targetFuel
            (Assembly.GasAware.installCodeAndGas target gasNat
              (thetaCodeRawInitialState target gasNat blobVersionedHashes
                evmParent.createdAccounts evmParent.genesisBlockHeader
                evmParent.blocks evmParent.accountMap evmParent.σ₀
                { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
                  transactionReceipts := evmParent.transactionReceipts }
                (EvmYul.State.addAccessedAccount
                  evmParent.toState addr).substate
                source origin recipient gasPrice value weiValue calldata depth
                header perm))
            targetOutcome),
        (hTargetGasForX hTrace).gasBound ≤ gasNat)
    (hUInt256 : gasNat < EvmYul.UInt256.size)
    (hTargetChildGas :
      ∀ {targetChild}, SourceLowered.WholeProgramOutcomeRel sourceOutcome
          (.running targetChild) →
        gasAvailableRel yulChild.toMachineState.gasAvailable
          targetChild.gasAvailable)
    (hEvmChildGas :
      ∀ {targetOutcome evmChild output},
        SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome →
          Assembly.GasAware.XResultAgrees targetOutcome
            (.success evmChild output) →
          gasAvailableRel yulChild.toMachineState.gasAvailable
            evmChild.gasAvailable)
    (inOffset inSize outOffset outSize : EvmYul.UInt256)
    {targetGas : EvmYul.UInt256}
    (hGas :
      gasAvailableRel
        (yulParent.toMachineState.finishExternalCall ByteArray.empty
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    ∃ (evmFuel : Nat) (targetChild evmChild : EVMState) (output : ByteArray),
      EvmYul.Yul.callDispatcher referenceFuel (some program.contract)
          (.Ok initialShared initialStore) =
        .ok (.Ok yulChild childStore, rets) ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome
        (.running targetChild) ∧
        EvmYul.EVM.Θ evmFuel.succ.succ blobVersionedHashes
          evmParent.createdAccounts evmParent.genesisBlockHeader
          evmParent.blocks evmParent.accountMap evmParent.σ₀
          { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
            transactionReceipts := evmParent.transactionReceipts }
          (EvmYul.State.addAccessedAccount evmParent.toState addr).substate
          source origin recipient (.Code (Assembly.Bytecode.encodeTarget target))
          (EvmYul.UInt256.ofNat gasNat) gasPrice value weiValue calldata depth
          header perm =
            .ok (evmChild.createdAccounts,
              if evmChild.accountMap.isEmpty then evmParent.accountMap
              else evmChild.accountMap,
              evmChild.gasAvailable,
              if evmChild.accountMap.isEmpty then
                (EvmYul.State.addAccessedAccount
                  evmParent.toState addr).substate
              else evmChild.substate,
              true, output) ∧
        ∃ yulAfter,
          EvmYul.Yul.restoreSuccessfulContractCallState
              (EvmYul.Yul.addAccessedAccount
                (.Ok yulParent parentStore) addr)
              (.Ok yulChild childStore)
              restoreStore ByteArray.empty inOffset inSize outOffset outSize =
            .ok (.Ok yulAfter restoreStore, [⟨1⟩]) ∧
          Reference.SharedStateRel
            (stateRelConfig varStackRel terminalCfgRel revertCfgRel
              gasAvailableRel gasValueRel totalGasRel)
            yulAfter
            { evmParent with
              toMachineState :=
                { evmParent.toMachineState.finishExternalCall output
                    inOffset inSize outOffset outSize with
                  gasAvailable := targetGas }
              accountMap :=
                if evmChild.accountMap.isEmpty then
                  evmParent.accountMap
                else
                  evmChild.accountMap
              substate :=
                if evmChild.accountMap.isEmpty then
                  (EvmYul.State.addAccessedAccount
                    evmParent.toState addr).substate
                else
                  evmChild.substate
              createdAccounts := evmChild.createdAccounts } := by
  let yulAccessed : EvmYul.SharedState .Yul :=
    { yulParent with
      toState := EvmYul.State.addAccessedAccount yulParent.toState addr }
  let evmAccessed : EvmYul.SharedState .EVM :=
    { evmParent with
      toState := EvmYul.State.addAccessedAccount evmParent.toState addr }
  have hParentAccessed :
      Reference.SharedStateRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        yulAccessed evmAccessed := by
    simpa [yulAccessed, evmAccessed] using
      sharedStateRel_addAccessedAccount hParent addr
  have hSourceRunAccessed :
      SourceLowered.run prim sourceFuel program
          (Assembly.GasAware.installCodeAndGas target gasNat
            (thetaCodeRawInitialState target gasNat blobVersionedHashes
              evmAccessed.createdAccounts evmAccessed.genesisBlockHeader
              evmAccessed.blocks evmAccessed.accountMap evmAccessed.σ₀
              { totalGasUsedInBlock := evmAccessed.totalGasUsedInBlock
                transactionReceipts := evmAccessed.transactionReceipts }
              evmAccessed.substate source origin recipient gasPrice value
              weiValue calldata depth header perm)) =
        .ok sourceOutcome := by
    simpa [evmAccessed] using hSourceRun
  let hTargetGasForXAccessed :
      ∀ {targetFuel targetOutcome},
        Assembly.Preservation.BlockTraceResult asm target targetFuel
          (Assembly.GasAware.installCodeAndGas target gasNat
            (thetaCodeRawInitialState target gasNat blobVersionedHashes
              evmAccessed.createdAccounts evmAccessed.genesisBlockHeader
              evmAccessed.blocks evmAccessed.accountMap evmAccessed.σ₀
              { totalGasUsedInBlock := evmAccessed.totalGasUsedInBlock
                transactionReceipts := evmAccessed.transactionReceipts }
              evmAccessed.substate source origin recipient gasPrice value
              weiValue calldata depth header perm))
          targetOutcome →
        Assembly.GasAware.XResultPreconditionAssumptions target
          (Assembly.GasAware.installCodeAndGas target gasNat
            (thetaCodeRawInitialState target gasNat blobVersionedHashes
              evmAccessed.createdAccounts evmAccessed.genesisBlockHeader
              evmAccessed.blocks evmAccessed.accountMap evmAccessed.σ₀
              { totalGasUsedInBlock := evmAccessed.totalGasUsedInBlock
                transactionReceipts := evmAccessed.transactionReceipts }
              evmAccessed.substate source origin recipient gasPrice value
              weiValue calldata depth header perm))
          targetOutcome := by
    intro targetFuel targetOutcome hTrace
    exact hTargetGasForX (by simpa [evmAccessed] using hTrace)
  have hGasBoundAccessed :
      ∀ {targetFuel targetOutcome}
        (hTrace :
          Assembly.Preservation.BlockTraceResult asm target targetFuel
            (Assembly.GasAware.installCodeAndGas target gasNat
              (thetaCodeRawInitialState target gasNat blobVersionedHashes
                evmAccessed.createdAccounts evmAccessed.genesisBlockHeader
                evmAccessed.blocks evmAccessed.accountMap evmAccessed.σ₀
                { totalGasUsedInBlock := evmAccessed.totalGasUsedInBlock
                  transactionReceipts := evmAccessed.transactionReceipts }
                evmAccessed.substate source origin recipient gasPrice value
                weiValue calldata depth header perm))
            targetOutcome),
        (hTargetGasForXAccessed hTrace).gasBound ≤ gasNat := by
    intro targetFuel targetOutcome hTrace
    exact hGasBound (by simpa [evmAccessed] using hTrace)
  have hGasAccessed :
      gasAvailableRel
        (yulAccessed.toMachineState.finishExternalCall ByteArray.empty
          inOffset inSize outOffset outSize).gasAvailable
        targetGas := by
    simpa [yulAccessed] using hGas
  simpa [yulAccessed, evmAccessed, EvmYul.Yul.addAccessedAccount,
    EvmYul.Yul.State.setState, EvmYul.Yul.State.toState,
    EvmYul.State.addAccessedAccount]
    using
      ordinaryCodeCall_runningSuccessBranch_rel_of_installed_childDispatcher
        (prim := prim) hPrim
        (varStackRel := varStackRel)
        (terminalCfgRel := terminalCfgRel)
        (revertCfgRel := revertCfgRel)
        (gasAvailableRel := gasAvailableRel)
        (gasValueRel := gasValueRel)
        (totalGasRel := totalGasRel)
        hParentAccessed hInstalled hCall hSourceRunAccessed hOutcomeRel
        hCompileBoundary hTargetGasForXAccessed hGasBoundAccessed hUInt256
        hTargetChildGas hEvmChildGas inOffset inSize outOffset outSize
        hGasAccessed

theorem ordinaryCodeCall_runningSuccessBranch_rel_of_installed_childDispatcher_afterAccess_withTargetGas
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {varStackRel : Reference.VarStackRel}
    {terminalCfgRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop}
    {revertCfgRel : Reference.State → EVMState → Prop}
    {gasAvailableRel : Word → Word → Prop}
    {gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm}
    {totalGasRel : Nat → Nat → Prop}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    {referenceFuel sourceFuel gasNat : Nat}
    {initialShared yulParent yulChild : EvmYul.SharedState .Yul}
    {evmParent : EvmYul.SharedState .EVM}
    {initialStore parentStore childStore restoreStore :
      EvmYul.Yul.VarStore}
    {rets : List EvmYul.UInt256}
    {sourceOutcome : Objects.Source.Outcome}
    (hParent :
      Reference.SharedStateRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        yulParent evmParent)
    (hInstalled : initialShared.executionEnv.code = program.contract)
    (hCall :
      EvmYul.Yul.callDispatcher referenceFuel (some program.contract)
          (.Ok initialShared initialStore) =
        .ok (.Ok yulChild childStore, rets))
    {blobVersionedHashes : List ByteArray}
    {source origin recipient addr : EvmYul.AccountAddress}
    {gasPrice value weiValue : EvmYul.UInt256}
    {calldata : ByteArray}
    {depth : Nat}
    {header : EvmYul.BlockHeader}
    {perm : Bool}
    (hSourceRun :
      SourceLowered.run prim sourceFuel program
          (Assembly.GasAware.installCodeAndGas target gasNat
            (thetaCodeRawInitialState target gasNat blobVersionedHashes
              evmParent.createdAccounts evmParent.genesisBlockHeader
              evmParent.blocks evmParent.accountMap evmParent.σ₀
              { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
                transactionReceipts := evmParent.transactionReceipts }
              (EvmYul.State.addAccessedAccount evmParent.toState addr).substate
              source origin recipient gasPrice value weiValue calldata depth
              header perm)) =
        .ok sourceOutcome)
    (hOutcomeRel :
      Program.RecursiveBridgeSemanticContracts.dispatcherOutcomeRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        terminalRel revertRel program (.Ok initialShared initialStore)
        (.regular (.Ok yulChild childStore)) sourceOutcome)
    (hCompileBoundary :
      compileCheckedAssemblyTargetBytecodeResourcesSourceStatic? program =
        some (asm, target))
    (hTargetGasForX :
      ∀ {targetFuel targetOutcome},
        Assembly.Preservation.BlockTraceResult asm target targetFuel
          (Assembly.GasAware.installCodeAndGas target gasNat
            (thetaCodeRawInitialState target gasNat blobVersionedHashes
              evmParent.createdAccounts evmParent.genesisBlockHeader
              evmParent.blocks evmParent.accountMap evmParent.σ₀
              { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
                transactionReceipts := evmParent.transactionReceipts }
              (EvmYul.State.addAccessedAccount evmParent.toState addr).substate
              source origin recipient gasPrice value weiValue calldata depth
              header perm))
          targetOutcome →
        Assembly.GasAware.XResultPreconditionAssumptions target
          (Assembly.GasAware.installCodeAndGas target gasNat
            (thetaCodeRawInitialState target gasNat blobVersionedHashes
              evmParent.createdAccounts evmParent.genesisBlockHeader
              evmParent.blocks evmParent.accountMap evmParent.σ₀
              { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
                transactionReceipts := evmParent.transactionReceipts }
              (EvmYul.State.addAccessedAccount evmParent.toState addr).substate
              source origin recipient gasPrice value weiValue calldata depth
              header perm))
          targetOutcome)
    (hGasBound :
      ∀ {targetFuel targetOutcome}
        (hTrace :
          Assembly.Preservation.BlockTraceResult asm target targetFuel
            (Assembly.GasAware.installCodeAndGas target gasNat
              (thetaCodeRawInitialState target gasNat blobVersionedHashes
                evmParent.createdAccounts evmParent.genesisBlockHeader
                evmParent.blocks evmParent.accountMap evmParent.σ₀
                { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
                  transactionReceipts := evmParent.transactionReceipts }
                (EvmYul.State.addAccessedAccount
                  evmParent.toState addr).substate
                source origin recipient gasPrice value weiValue calldata depth
                header perm))
            targetOutcome),
        (hTargetGasForX hTrace).gasBound ≤ gasNat)
    (hUInt256 : gasNat < EvmYul.UInt256.size)
    (hTargetChildGas :
      ∀ {targetChild}, SourceLowered.WholeProgramOutcomeRel sourceOutcome
          (.running targetChild) →
        gasAvailableRel yulChild.toMachineState.gasAvailable
          targetChild.gasAvailable)
    (hEvmChildGas :
      ∀ {targetOutcome evmChild output},
        SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome →
          Assembly.GasAware.XResultAgrees targetOutcome
            (.success evmChild output) →
          gasAvailableRel yulChild.toMachineState.gasAvailable
            evmChild.gasAvailable)
    (inOffset inSize outOffset outSize : EvmYul.UInt256)
    (targetGasOf : EVMState → ByteArray → EvmYul.UInt256)
    (hReturnedGas :
      ∀ {targetOutcome evmChild output},
        SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome →
          Assembly.GasAware.XResultAgrees targetOutcome
            (.success evmChild output) →
          gasAvailableRel
            (yulParent.toMachineState.finishExternalCall ByteArray.empty
              inOffset inSize outOffset outSize).gasAvailable
            (targetGasOf evmChild output)) :
    ∃ (evmFuel : Nat) (targetChild evmChild : EVMState) (output : ByteArray),
      EvmYul.Yul.callDispatcher referenceFuel (some program.contract)
          (.Ok initialShared initialStore) =
        .ok (.Ok yulChild childStore, rets) ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome
        (.running targetChild) ∧
        EvmYul.EVM.Θ evmFuel.succ.succ blobVersionedHashes
          evmParent.createdAccounts evmParent.genesisBlockHeader
          evmParent.blocks evmParent.accountMap evmParent.σ₀
          { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
            transactionReceipts := evmParent.transactionReceipts }
          (EvmYul.State.addAccessedAccount evmParent.toState addr).substate
          source origin recipient (.Code (Assembly.Bytecode.encodeTarget target))
          (EvmYul.UInt256.ofNat gasNat) gasPrice value weiValue calldata depth
          header perm =
            .ok (evmChild.createdAccounts,
              if evmChild.accountMap.isEmpty then evmParent.accountMap
              else evmChild.accountMap,
              evmChild.gasAvailable,
              if evmChild.accountMap.isEmpty then
                (EvmYul.State.addAccessedAccount
                  evmParent.toState addr).substate
              else evmChild.substate,
              true, output) ∧
        ∃ yulAfter,
          EvmYul.Yul.restoreSuccessfulContractCallState
              (EvmYul.Yul.addAccessedAccount
                (.Ok yulParent parentStore) addr)
              (.Ok yulChild childStore)
              restoreStore ByteArray.empty inOffset inSize outOffset outSize =
            .ok (.Ok yulAfter restoreStore, [⟨1⟩]) ∧
          Reference.SharedStateRel
            (stateRelConfig varStackRel terminalCfgRel revertCfgRel
              gasAvailableRel gasValueRel totalGasRel)
            yulAfter
            { evmParent with
              toMachineState :=
                { evmParent.toMachineState.finishExternalCall output
                    inOffset inSize outOffset outSize with
                  gasAvailable := targetGasOf evmChild output }
              accountMap :=
                if evmChild.accountMap.isEmpty then
                  evmParent.accountMap
                else
                  evmChild.accountMap
              substate :=
                if evmChild.accountMap.isEmpty then
                  (EvmYul.State.addAccessedAccount
                    evmParent.toState addr).substate
                else
                  evmChild.substate
              createdAccounts := evmChild.createdAccounts } := by
  rcases
      compile_preserves_of_installed_callDispatcher_regular_sourceStaticBoundary_installedGas_XResult
        (prim := prim) hPrim
        (outcomeRel :=
          Program.RecursiveBridgeSemanticContracts.dispatcherOutcomeRel
            (stateRelConfig varStackRel terminalCfgRel revertCfgRel
              gasAvailableRel gasValueRel totalGasRel)
            terminalRel revertRel program (.Ok initialShared initialStore))
        (program := program) (asm := asm) (target := target)
        (referenceFuel := referenceFuel) (sourceFuel := sourceFuel)
        (gas := gasNat) (shared := initialShared)
        (store := initialStore) (state' := .Ok yulChild childStore)
        (rets := rets)
        (rawInitial :=
          thetaCodeRawInitialState target gasNat blobVersionedHashes
            evmParent.createdAccounts evmParent.genesisBlockHeader
            evmParent.blocks evmParent.accountMap evmParent.σ₀
            { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
              transactionReceipts := evmParent.transactionReceipts }
            (EvmYul.State.addAccessedAccount evmParent.toState addr).substate
            source origin recipient gasPrice value weiValue calldata depth
            header perm)
        (sourceOutcome := sourceOutcome)
        hInstalled hCall hSourceRun hOutcomeRel hCompileBoundary
        (by
          simp [thetaCodeRawInitialState, Assembly.GasAware.installCodeAndGas])
        (by
          simp [thetaCodeRawInitialState, Assembly.GasAware.installCodeAndGas])
        hTargetGasForX hGasBound hUInt256 with
    ⟨_targetFuel, targetOutcome, evmFuel, _gasBound, evmResult,
      _hReferenceRun, _hTargetRun, _hOutcomeRel, hWhole, _hTrace,
      _hGasBound, hX, hAgree, _hDecode, _hJumpdest⟩
  have hXTheta :
      EvmYul.EVM.X evmFuel (Assembly.GasAware.validJumps target)
          (thetaCodeXInitialState target gasNat blobVersionedHashes
            evmParent.createdAccounts evmParent.genesisBlockHeader
            evmParent.blocks evmParent.accountMap evmParent.σ₀
            { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
              transactionReceipts := evmParent.transactionReceipts }
            (EvmYul.State.addAccessedAccount evmParent.toState addr).substate
            source origin recipient gasPrice value weiValue calldata depth
            header perm) =
        .ok evmResult := by
    simpa [thetaCodeXInitialState] using hX
  rcases
      ordinaryCodeCall_runningSuccessBranch_rel_of_childOutcome_afterAccess_withTargetGas
        (varStackRel := varStackRel)
        (terminalCfgRel := terminalCfgRel)
        (revertCfgRel := revertCfgRel)
        (gasAvailableRel := gasAvailableRel)
        (gasValueRel := gasValueRel)
        (totalGasRel := totalGasRel)
        hParent hOutcomeRel hWhole hXTheta hAgree
        (by
          intro targetChild hTarget
          exact hTargetChildGas (by simpa [hTarget] using hWhole))
        (by
          intro evmChild output hResult
          exact hEvmChildGas hWhole (by simpa [hResult] using hAgree))
        inOffset inSize outOffset outSize targetGasOf hReturnedGas with
    ⟨targetChild, evmChild, output, hTargetOutcome, _hResult,
      hTheta, hRestore⟩
  exact
    ⟨evmFuel, targetChild, evmChild, output, hCall,
      by simpa [hTargetOutcome] using hWhole, hTheta, hRestore⟩

theorem ordinaryCodeCall_haltedSuccessBranch_rel
    {cfg : Reference.StateRelConfig}
    {yulParent : EvmYul.SharedState .Yul}
    {evmParent : EvmYul.SharedState .EVM}
    (hParent : Reference.SharedStateRel cfg yulParent evmParent)
    (hParentWorld :
      CompiledAccountMapRel yulParent.accountMap evmParent.accountMap)
    (hCfgAccountMap :
      ∀ {yulMap : EvmYul.AccountMap .Yul}
        {evmMap : EvmYul.AccountMap .EVM},
        CompiledAccountMapRel yulMap evmMap →
          cfg.accountMapRel yulMap evmMap)
    (parentStore childStore restoreStore : EvmYul.Yul.VarStore)
    {yulChild : EvmYul.SharedState .Yul}
    {halt : Assembly.Halt}
    {evmChild : EVMState}
    {fuel gasNat : Nat}
    {blobVersionedHashes : List ByteArray}
    {source origin recipient : EvmYul.AccountAddress}
    {target : Assembly.TargetProgram}
    {gasPrice value weiValue : EvmYul.UInt256}
    {calldata output : ByteArray}
    {depth : Nat}
    {header : EvmYul.BlockHeader}
    {perm : Bool}
    (hTargetChild :
      ExternalChildMergeRel yulChild halt.state.toSharedState)
    (hX :
      EvmYul.EVM.X fuel (Assembly.GasAware.validJumps target)
          (thetaCodeXInitialState target gasNat blobVersionedHashes
            evmParent.createdAccounts evmParent.genesisBlockHeader
            evmParent.blocks evmParent.accountMap evmParent.σ₀
            { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
              transactionReceipts := evmParent.transactionReceipts }
            evmParent.substate source origin recipient gasPrice value
            weiValue calldata depth header perm) =
        .ok (.success evmChild output))
    (hAgree :
      Assembly.GasAware.XResultAgrees (.halted halt)
        (.success evmChild output))
    (inOffset inSize outOffset outSize : EvmYul.UInt256)
    {targetGas : EvmYul.UInt256}
    (hGas :
      cfg.gasAvailableRel
        (yulParent.toMachineState.finishExternalCall output
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    EvmYul.EVM.Θ fuel.succ.succ blobVersionedHashes
        evmParent.createdAccounts evmParent.genesisBlockHeader
        evmParent.blocks evmParent.accountMap evmParent.σ₀
        { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
          transactionReceipts := evmParent.transactionReceipts }
        evmParent.substate source origin recipient
        (.Code (Assembly.Bytecode.encodeTarget target))
        (EvmYul.UInt256.ofNat gasNat) gasPrice value weiValue calldata depth
        header perm =
      .ok (evmChild.createdAccounts,
        if evmChild.accountMap.isEmpty then evmParent.accountMap
        else evmChild.accountMap,
        evmChild.gasAvailable,
        if evmChild.accountMap.isEmpty then evmParent.substate
        else evmChild.substate,
        true, output) ∧
      halt.kind ≠ .revert ∧
        ∃ yulAfter,
          EvmYul.Yul.restoreSuccessfulContractCallState
              (.Ok yulParent parentStore)
              (.Ok yulChild childStore)
              restoreStore output inOffset inSize outOffset outSize =
            .ok (.Ok yulAfter restoreStore, [⟨1⟩]) ∧
          Reference.SharedStateRel cfg yulAfter
            { evmParent with
              toMachineState :=
                { evmParent.toMachineState.finishExternalCall output
                    inOffset inSize outOffset outSize with
                  gasAvailable := targetGas }
              accountMap :=
                if evmChild.accountMap.isEmpty then
                  evmParent.accountMap
                else
                  evmChild.accountMap
              substate :=
                if evmChild.accountMap.isEmpty then
                  evmParent.substate
                else
                  evmChild.substate
              createdAccounts := evmChild.createdAccounts } := by
  exact
    ⟨Theta_code_success_of_X_installedCode hX,
      restoreSuccessfulContractCallState_of_XResultAgrees_halted_success_merge
        hParent hParentWorld hCfgAccountMap
        parentStore childStore restoreStore
        hTargetChild hAgree
        inOffset inSize outOffset outSize hGas⟩

theorem ordinaryCodeCall_haltedSuccessBranch_rel_afterAccess
    {cfg : Reference.StateRelConfig}
    {yulParent : EvmYul.SharedState .Yul}
    {evmParent : EvmYul.SharedState .EVM}
    (hParent : Reference.SharedStateRel cfg yulParent evmParent)
    (hParentWorld :
      CompiledAccountMapRel yulParent.accountMap evmParent.accountMap)
    (hCfgAccountMap :
      ∀ {yulMap : EvmYul.AccountMap .Yul}
        {evmMap : EvmYul.AccountMap .EVM},
        CompiledAccountMapRel yulMap evmMap →
          cfg.accountMapRel yulMap evmMap)
    (parentStore childStore restoreStore : EvmYul.Yul.VarStore)
    (addr : EvmYul.AccountAddress)
    {yulChild : EvmYul.SharedState .Yul}
    {halt : Assembly.Halt}
    {evmChild : EVMState}
    {fuel gasNat : Nat}
    {blobVersionedHashes : List ByteArray}
    {source origin recipient : EvmYul.AccountAddress}
    {target : Assembly.TargetProgram}
    {gasPrice value weiValue : EvmYul.UInt256}
    {calldata output : ByteArray}
    {depth : Nat}
    {header : EvmYul.BlockHeader}
    {perm : Bool}
    (hTargetChild :
      ExternalChildMergeRel yulChild halt.state.toSharedState)
    (hX :
      EvmYul.EVM.X fuel (Assembly.GasAware.validJumps target)
          (thetaCodeXInitialState target gasNat blobVersionedHashes
            evmParent.createdAccounts evmParent.genesisBlockHeader
            evmParent.blocks evmParent.accountMap evmParent.σ₀
            { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
              transactionReceipts := evmParent.transactionReceipts }
            (EvmYul.State.addAccessedAccount evmParent.toState addr).substate
            source origin recipient gasPrice value weiValue calldata depth
            header perm) =
        .ok (.success evmChild output))
    (hAgree :
      Assembly.GasAware.XResultAgrees (.halted halt)
        (.success evmChild output))
    (inOffset inSize outOffset outSize : EvmYul.UInt256)
    {targetGas : EvmYul.UInt256}
    (hGas :
      cfg.gasAvailableRel
        (yulParent.toMachineState.finishExternalCall output
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    EvmYul.EVM.Θ fuel.succ.succ blobVersionedHashes
        evmParent.createdAccounts evmParent.genesisBlockHeader
        evmParent.blocks evmParent.accountMap evmParent.σ₀
        { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
          transactionReceipts := evmParent.transactionReceipts }
        (EvmYul.State.addAccessedAccount evmParent.toState addr).substate
        source origin recipient (.Code (Assembly.Bytecode.encodeTarget target))
        (EvmYul.UInt256.ofNat gasNat) gasPrice value weiValue calldata depth
        header perm =
      .ok (evmChild.createdAccounts,
        if evmChild.accountMap.isEmpty then evmParent.accountMap
        else evmChild.accountMap,
        evmChild.gasAvailable,
        if evmChild.accountMap.isEmpty then
          (EvmYul.State.addAccessedAccount evmParent.toState addr).substate
        else evmChild.substate,
        true, output) ∧
      halt.kind ≠ .revert ∧
        ∃ yulAfter,
          EvmYul.Yul.restoreSuccessfulContractCallState
              (EvmYul.Yul.addAccessedAccount
                (.Ok yulParent parentStore) addr)
              (.Ok yulChild childStore)
              restoreStore output inOffset inSize outOffset outSize =
            .ok (.Ok yulAfter restoreStore, [⟨1⟩]) ∧
          Reference.SharedStateRel cfg yulAfter
            { evmParent with
              toMachineState :=
                { evmParent.toMachineState.finishExternalCall output
                    inOffset inSize outOffset outSize with
                  gasAvailable := targetGas }
              accountMap :=
                if evmChild.accountMap.isEmpty then
                  evmParent.accountMap
                else
                  evmChild.accountMap
              substate :=
                if evmChild.accountMap.isEmpty then
                  (EvmYul.State.addAccessedAccount
                    evmParent.toState addr).substate
                else
                  evmChild.substate
              createdAccounts := evmChild.createdAccounts } := by
  let yulAccessed : EvmYul.SharedState .Yul :=
    { yulParent with
      toState := EvmYul.State.addAccessedAccount yulParent.toState addr }
  let evmAccessed : EvmYul.SharedState .EVM :=
    { evmParent with
      toState := EvmYul.State.addAccessedAccount evmParent.toState addr }
  have hParentAccessed :
      Reference.SharedStateRel cfg yulAccessed evmAccessed := by
    simpa [yulAccessed, evmAccessed] using
      sharedStateRel_addAccessedAccount hParent addr
  have hParentWorldAccessed :
      CompiledAccountMapRel yulAccessed.accountMap evmAccessed.accountMap := by
    simpa [yulAccessed, evmAccessed] using hParentWorld
  have hXAccessed :
      EvmYul.EVM.X fuel (Assembly.GasAware.validJumps target)
          (thetaCodeXInitialState target gasNat blobVersionedHashes
            evmAccessed.createdAccounts evmAccessed.genesisBlockHeader
            evmAccessed.blocks evmAccessed.accountMap evmAccessed.σ₀
            { totalGasUsedInBlock := evmAccessed.totalGasUsedInBlock
              transactionReceipts := evmAccessed.transactionReceipts }
            evmAccessed.substate source origin recipient gasPrice value
            weiValue calldata depth header perm) =
        .ok (.success evmChild output) := by
    simpa [evmAccessed] using hX
  have hGasAccessed :
      cfg.gasAvailableRel
        (yulAccessed.toMachineState.finishExternalCall output
          inOffset inSize outOffset outSize).gasAvailable
        targetGas := by
    simpa [yulAccessed] using hGas
  simpa [yulAccessed, evmAccessed, EvmYul.Yul.addAccessedAccount,
    EvmYul.Yul.State.setState, EvmYul.Yul.State.toState,
    EvmYul.State.addAccessedAccount]
    using
      ordinaryCodeCall_haltedSuccessBranch_rel
        hParentAccessed hParentWorldAccessed hCfgAccountMap
        parentStore childStore restoreStore
        hTargetChild hXAccessed hAgree
        inOffset inSize outOffset outSize hGasAccessed

theorem ordinaryCodeCall_haltedSuccessBranch_rel_of_childOutcome
    {varStackRel : Reference.VarStackRel}
    {terminalCfgRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop}
    {revertCfgRel : Reference.State → EVMState → Prop}
    {gasAvailableRel : Word → Word → Prop}
    {gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm}
    {totalGasRel : Nat → Nat → Prop}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {program : Program}
    {initialShared yulParent yulChild : EvmYul.SharedState .Yul}
    {evmParent : EvmYul.SharedState .EVM}
    {initialStore parentStore childStore restoreStore :
      EvmYul.Yul.VarStore}
    {value : Word}
    {sourceOutcome : Objects.Source.Outcome}
    {targetOutcome : Assembly.StepResult}
    {evmResult : EvmYul.EVM.ExecutionResult EVMState}
    (hParent :
      Reference.SharedStateRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        yulParent evmParent)
    (hOutcomeRel :
      Program.RecursiveBridgeSemanticContracts.dispatcherOutcomeRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        terminalRel revertRel program (.Ok initialShared initialStore)
        (.yulHalt (.Ok yulChild childStore) value) sourceOutcome)
    (hWhole :
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome)
    (hTerminalChild :
      ∀ {kind compiler},
        terminalRel kind value (.Ok yulChild childStore) compiler →
          ExternalChildMergeRel yulChild compiler.shared)
    (hTerminalNonRevert :
      ∀ {kind compiler},
        terminalRel kind value (.Ok yulChild childStore) compiler →
          kind ≠ .revert)
    {fuel gasNat : Nat}
    {blobVersionedHashes : List ByteArray}
    {source origin recipient : EvmYul.AccountAddress}
    {target : Assembly.TargetProgram}
    {gasPrice valueWei weiValue : EvmYul.UInt256}
    {calldata : ByteArray}
    {depth : Nat}
    {header : EvmYul.BlockHeader}
    {perm : Bool}
    (hX :
      EvmYul.EVM.X fuel (Assembly.GasAware.validJumps target)
          (thetaCodeXInitialState target gasNat blobVersionedHashes
            evmParent.createdAccounts evmParent.genesisBlockHeader
            evmParent.blocks evmParent.accountMap evmParent.σ₀
            { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
              transactionReceipts := evmParent.transactionReceipts }
            evmParent.substate source origin recipient gasPrice valueWei
            weiValue calldata depth header perm) =
        .ok evmResult)
    (hAgree :
      Assembly.GasAware.XResultAgrees targetOutcome evmResult)
    (inOffset inSize outOffset outSize : EvmYul.UInt256)
    {targetGas : EvmYul.UInt256}
    (hReturnedGas :
      ∀ {evmChild output}, evmResult = .success evmChild output →
        gasAvailableRel
          (yulParent.toMachineState.finishExternalCall output
            inOffset inSize outOffset outSize).gasAvailable
          targetGas) :
    ∃ kind compiler halt evmChild output,
      terminalRel kind value (.Ok yulChild childStore) compiler ∧
        targetOutcome = .halted halt ∧
        halt.kind = kind ∧
        evmResult = .success evmChild output ∧
        EvmYul.EVM.Θ fuel.succ.succ blobVersionedHashes
          evmParent.createdAccounts evmParent.genesisBlockHeader
          evmParent.blocks evmParent.accountMap evmParent.σ₀
          { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
            transactionReceipts := evmParent.transactionReceipts }
          evmParent.substate source origin recipient
          (.Code (Assembly.Bytecode.encodeTarget target))
          (EvmYul.UInt256.ofNat gasNat) gasPrice valueWei weiValue calldata
          depth header perm =
            .ok (evmChild.createdAccounts,
              if evmChild.accountMap.isEmpty then evmParent.accountMap
              else evmChild.accountMap,
              evmChild.gasAvailable,
              if evmChild.accountMap.isEmpty then evmParent.substate
              else evmChild.substate,
              true, output) ∧
        halt.kind ≠ .revert ∧
          ∃ yulAfter,
            EvmYul.Yul.restoreSuccessfulContractCallState
                (.Ok yulParent parentStore)
                (.Ok yulChild childStore)
                restoreStore output inOffset inSize outOffset outSize =
              .ok (.Ok yulAfter restoreStore, [⟨1⟩]) ∧
            Reference.SharedStateRel
              (stateRelConfig varStackRel terminalCfgRel revertCfgRel
                gasAvailableRel gasValueRel totalGasRel)
              yulAfter
              { evmParent with
                toMachineState :=
                  { evmParent.toMachineState.finishExternalCall output
                      inOffset inSize outOffset outSize with
                    gasAvailable := targetGas }
                accountMap :=
                  if evmChild.accountMap.isEmpty then
                    evmParent.accountMap
                  else
                    evmChild.accountMap
                substate :=
                  if evmChild.accountMap.isEmpty then
                    evmParent.substate
                  else
                    evmChild.substate
                createdAccounts := evmChild.createdAccounts } := by
  rcases
      dispatcherOutcomeRel_yulHalt_ok_whole_childMergeRelations
        (varStackRel := varStackRel)
        (terminalCfgRel := terminalCfgRel)
        (revertCfgRel := revertCfgRel)
        (gasAvailableRel := gasAvailableRel)
        (gasValueRel := gasValueRel)
        (totalGasRel := totalGasRel)
        hOutcomeRel hWhole hTerminalChild with
    ⟨kind, compiler, halt, hTerminal, _hSource, hTarget, hKind,
      hTargetChild⟩
  have hNotRevert : halt.kind ≠ .revert := by
    intro hRevert
    exact hTerminalNonRevert hTerminal (hKind.symm.trans hRevert)
  have hAgreeHalted :
      Assembly.GasAware.XResultAgrees (.halted halt) evmResult := by
    simpa [hTarget] using hAgree
  rcases
      XResultAgrees_halted_nonrevert_success_shape hAgreeHalted
        hNotRevert with
    ⟨evmChild, output, hResult, hAgreeSuccess⟩
  have hXSuccess :
      EvmYul.EVM.X fuel (Assembly.GasAware.validJumps target)
          (thetaCodeXInitialState target gasNat blobVersionedHashes
            evmParent.createdAccounts evmParent.genesisBlockHeader
            evmParent.blocks evmParent.accountMap evmParent.σ₀
            { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
              transactionReceipts := evmParent.transactionReceipts }
            evmParent.substate source origin recipient gasPrice valueWei
            weiValue calldata depth header perm) =
        .ok (.success evmChild output) := by
    simpa [hResult] using hX
  have hParentWorld :
      CompiledAccountMapRel yulParent.accountMap evmParent.accountMap :=
    compiledAccountMapRel_of_sharedStateRel_stateRelConfig hParent
  have hCfgAccountMap :
      ∀ {yulMap : EvmYul.AccountMap .Yul}
        {evmMap : EvmYul.AccountMap .EVM},
        CompiledAccountMapRel yulMap evmMap →
          (stateRelConfig varStackRel terminalCfgRel revertCfgRel
            gasAvailableRel gasValueRel totalGasRel).accountMapRel
            yulMap evmMap := by
    intro yulMap evmMap hRel
    exact stateRelConfig_accountMapRel_of_compiledAccountMapRel hRel
  have hGasSuccess :
      gasAvailableRel
        (yulParent.toMachineState.finishExternalCall output
          inOffset inSize outOffset outSize).gasAvailable
        targetGas :=
    hReturnedGas hResult
  rcases
      ordinaryCodeCall_haltedSuccessBranch_rel
        (cfg :=
          stateRelConfig varStackRel terminalCfgRel revertCfgRel
            gasAvailableRel gasValueRel totalGasRel)
        hParent hParentWorld hCfgAccountMap
        parentStore childStore restoreStore
        hTargetChild
        hXSuccess hAgreeSuccess
        inOffset inSize outOffset outSize hGasSuccess with
    ⟨hTheta, hSuccess⟩
  exact
    ⟨kind, compiler, halt, evmChild, output, hTerminal, hTarget, hKind,
      hResult, hTheta, hSuccess⟩

theorem ordinaryCodeCall_haltedSuccessBranch_rel_of_childOutcome_afterAccess
    {varStackRel : Reference.VarStackRel}
    {terminalCfgRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop}
    {revertCfgRel : Reference.State → EVMState → Prop}
    {gasAvailableRel : Word → Word → Prop}
    {gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm}
    {totalGasRel : Nat → Nat → Prop}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {program : Program}
    {initialShared yulParent yulChild : EvmYul.SharedState .Yul}
    {evmParent : EvmYul.SharedState .EVM}
    {initialStore parentStore childStore restoreStore :
      EvmYul.Yul.VarStore}
    {value : Word}
    {sourceOutcome : Objects.Source.Outcome}
    {targetOutcome : Assembly.StepResult}
    {evmResult : EvmYul.EVM.ExecutionResult EVMState}
    (hParent :
      Reference.SharedStateRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        yulParent evmParent)
    (hOutcomeRel :
      Program.RecursiveBridgeSemanticContracts.dispatcherOutcomeRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        terminalRel revertRel program (.Ok initialShared initialStore)
        (.yulHalt (.Ok yulChild childStore) value) sourceOutcome)
    (hWhole :
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome)
    (hTerminalChild :
      ∀ {kind compiler},
        terminalRel kind value (.Ok yulChild childStore) compiler →
          ExternalChildMergeRel yulChild compiler.shared)
    (hTerminalNonRevert :
      ∀ {kind compiler},
        terminalRel kind value (.Ok yulChild childStore) compiler →
          kind ≠ .revert)
    {fuel gasNat : Nat}
    {blobVersionedHashes : List ByteArray}
    {source origin recipient addr : EvmYul.AccountAddress}
    {target : Assembly.TargetProgram}
    {gasPrice valueWei weiValue : EvmYul.UInt256}
    {calldata : ByteArray}
    {depth : Nat}
    {header : EvmYul.BlockHeader}
    {perm : Bool}
    (hX :
      EvmYul.EVM.X fuel (Assembly.GasAware.validJumps target)
          (thetaCodeXInitialState target gasNat blobVersionedHashes
            evmParent.createdAccounts evmParent.genesisBlockHeader
            evmParent.blocks evmParent.accountMap evmParent.σ₀
            { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
              transactionReceipts := evmParent.transactionReceipts }
            (EvmYul.State.addAccessedAccount evmParent.toState addr).substate
            source origin recipient gasPrice valueWei weiValue calldata depth
            header perm) =
        .ok evmResult)
    (hAgree :
      Assembly.GasAware.XResultAgrees targetOutcome evmResult)
    (inOffset inSize outOffset outSize : EvmYul.UInt256)
    {targetGas : EvmYul.UInt256}
    (hReturnedGas :
      ∀ {evmChild output}, evmResult = .success evmChild output →
        gasAvailableRel
          (yulParent.toMachineState.finishExternalCall output
            inOffset inSize outOffset outSize).gasAvailable
          targetGas) :
    ∃ kind compiler halt evmChild output,
      terminalRel kind value (.Ok yulChild childStore) compiler ∧
        targetOutcome = .halted halt ∧
        halt.kind = kind ∧
        evmResult = .success evmChild output ∧
        EvmYul.EVM.Θ fuel.succ.succ blobVersionedHashes
          evmParent.createdAccounts evmParent.genesisBlockHeader
          evmParent.blocks evmParent.accountMap evmParent.σ₀
          { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
            transactionReceipts := evmParent.transactionReceipts }
          (EvmYul.State.addAccessedAccount evmParent.toState addr).substate
          source origin recipient (.Code (Assembly.Bytecode.encodeTarget target))
          (EvmYul.UInt256.ofNat gasNat) gasPrice valueWei weiValue calldata
          depth header perm =
            .ok (evmChild.createdAccounts,
              if evmChild.accountMap.isEmpty then evmParent.accountMap
              else evmChild.accountMap,
              evmChild.gasAvailable,
              if evmChild.accountMap.isEmpty then
                (EvmYul.State.addAccessedAccount
                  evmParent.toState addr).substate
              else evmChild.substate,
              true, output) ∧
        halt.kind ≠ .revert ∧
          ∃ yulAfter,
            EvmYul.Yul.restoreSuccessfulContractCallState
                (EvmYul.Yul.addAccessedAccount
                  (.Ok yulParent parentStore) addr)
                (.Ok yulChild childStore)
                restoreStore output inOffset inSize outOffset outSize =
              .ok (.Ok yulAfter restoreStore, [⟨1⟩]) ∧
            Reference.SharedStateRel
              (stateRelConfig varStackRel terminalCfgRel revertCfgRel
                gasAvailableRel gasValueRel totalGasRel)
              yulAfter
              { evmParent with
                toMachineState :=
                  { evmParent.toMachineState.finishExternalCall output
                      inOffset inSize outOffset outSize with
                    gasAvailable := targetGas }
                accountMap :=
                  if evmChild.accountMap.isEmpty then
                    evmParent.accountMap
                  else
                    evmChild.accountMap
                substate :=
                  if evmChild.accountMap.isEmpty then
                    (EvmYul.State.addAccessedAccount
                      evmParent.toState addr).substate
                  else
                    evmChild.substate
                createdAccounts := evmChild.createdAccounts } := by
  let yulAccessed : EvmYul.SharedState .Yul :=
    { yulParent with
      toState := EvmYul.State.addAccessedAccount yulParent.toState addr }
  let evmAccessed : EvmYul.SharedState .EVM :=
    { evmParent with
      toState := EvmYul.State.addAccessedAccount evmParent.toState addr }
  have hParentAccessed :
      Reference.SharedStateRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        yulAccessed evmAccessed := by
    simpa [yulAccessed, evmAccessed] using
      sharedStateRel_addAccessedAccount hParent addr
  have hXAccessed :
      EvmYul.EVM.X fuel (Assembly.GasAware.validJumps target)
          (thetaCodeXInitialState target gasNat blobVersionedHashes
            evmAccessed.createdAccounts evmAccessed.genesisBlockHeader
            evmAccessed.blocks evmAccessed.accountMap evmAccessed.σ₀
            { totalGasUsedInBlock := evmAccessed.totalGasUsedInBlock
              transactionReceipts := evmAccessed.transactionReceipts }
            evmAccessed.substate source origin recipient gasPrice valueWei
            weiValue calldata depth header perm) =
        .ok evmResult := by
    simpa [evmAccessed] using hX
  have hReturnedGasAccessed :
      ∀ {evmChild output}, evmResult = .success evmChild output →
        gasAvailableRel
          (yulAccessed.toMachineState.finishExternalCall output
            inOffset inSize outOffset outSize).gasAvailable
          targetGas := by
    intro evmChild output hResult
    simpa [yulAccessed] using hReturnedGas hResult
  simpa [yulAccessed, evmAccessed, EvmYul.Yul.addAccessedAccount,
    EvmYul.Yul.State.setState, EvmYul.Yul.State.toState,
    EvmYul.State.addAccessedAccount]
    using
      ordinaryCodeCall_haltedSuccessBranch_rel_of_childOutcome
        (varStackRel := varStackRel)
        (terminalCfgRel := terminalCfgRel)
        (revertCfgRel := revertCfgRel)
        (gasAvailableRel := gasAvailableRel)
        (gasValueRel := gasValueRel)
        (totalGasRel := totalGasRel)
        hParentAccessed hOutcomeRel hWhole hTerminalChild
        hTerminalNonRevert hXAccessed hAgree
        inOffset inSize outOffset outSize hReturnedGasAccessed

theorem ordinaryCodeCall_haltedSuccessBranch_rel_of_installed_childDispatcher
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {varStackRel : Reference.VarStackRel}
    {terminalCfgRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop}
    {revertCfgRel : Reference.State → EVMState → Prop}
    {gasAvailableRel : Word → Word → Prop}
    {gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm}
    {totalGasRel : Nat → Nat → Prop}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    {referenceFuel sourceFuel gasNat : Nat}
    {initialShared yulParent yulChild : EvmYul.SharedState .Yul}
    {evmParent : EvmYul.SharedState .EVM}
    {initialStore parentStore childStore restoreStore :
      EvmYul.Yul.VarStore}
    {value : Word}
    {sourceOutcome : Objects.Source.Outcome}
    (hParent :
      Reference.SharedStateRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        yulParent evmParent)
    (hInstalled : initialShared.executionEnv.code = program.contract)
    (hCall :
      EvmYul.Yul.callDispatcher referenceFuel (some program.contract)
          (.Ok initialShared initialStore) =
        .error (.YulHalt (.Ok yulChild childStore) value))
    {blobVersionedHashes : List ByteArray}
    {source origin recipient : EvmYul.AccountAddress}
    {gasPrice valueWei weiValue : EvmYul.UInt256}
    {calldata : ByteArray}
    {depth : Nat}
    {header : EvmYul.BlockHeader}
    {perm : Bool}
    (hSourceRun :
      SourceLowered.run prim sourceFuel program
          (Assembly.GasAware.installCodeAndGas target gasNat
            (thetaCodeRawInitialState target gasNat blobVersionedHashes
              evmParent.createdAccounts evmParent.genesisBlockHeader
              evmParent.blocks evmParent.accountMap evmParent.σ₀
              { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
                transactionReceipts := evmParent.transactionReceipts }
              evmParent.substate source origin recipient gasPrice valueWei
              weiValue calldata depth header perm)) =
        .ok sourceOutcome)
    (hOutcomeRel :
      Program.RecursiveBridgeSemanticContracts.dispatcherOutcomeRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        terminalRel revertRel program (.Ok initialShared initialStore)
        (.yulHalt (.Ok yulChild childStore) value) sourceOutcome)
    (hTerminalChild :
      ∀ {kind compiler},
        terminalRel kind value (.Ok yulChild childStore) compiler →
          ExternalChildMergeRel yulChild compiler.shared)
    (hTerminalNonRevert :
      ∀ {kind compiler},
        terminalRel kind value (.Ok yulChild childStore) compiler →
          kind ≠ .revert)
    (hCompileBoundary :
      compileCheckedAssemblyTargetBytecodeResourcesSourceStatic? program =
        some (asm, target))
    (hTargetGasForX :
      ∀ {targetFuel targetOutcome},
        Assembly.Preservation.BlockTraceResult asm target targetFuel
          (Assembly.GasAware.installCodeAndGas target gasNat
            (thetaCodeRawInitialState target gasNat blobVersionedHashes
              evmParent.createdAccounts evmParent.genesisBlockHeader
              evmParent.blocks evmParent.accountMap evmParent.σ₀
              { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
                transactionReceipts := evmParent.transactionReceipts }
              evmParent.substate source origin recipient gasPrice valueWei
              weiValue calldata depth header perm))
          targetOutcome →
        Assembly.GasAware.XResultPreconditionAssumptions target
          (Assembly.GasAware.installCodeAndGas target gasNat
            (thetaCodeRawInitialState target gasNat blobVersionedHashes
              evmParent.createdAccounts evmParent.genesisBlockHeader
              evmParent.blocks evmParent.accountMap evmParent.σ₀
              { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
                transactionReceipts := evmParent.transactionReceipts }
              evmParent.substate source origin recipient gasPrice valueWei
              weiValue calldata depth header perm))
          targetOutcome)
    (hGasBound :
      ∀ {targetFuel targetOutcome}
        (hTrace :
          Assembly.Preservation.BlockTraceResult asm target targetFuel
            (Assembly.GasAware.installCodeAndGas target gasNat
              (thetaCodeRawInitialState target gasNat blobVersionedHashes
                evmParent.createdAccounts evmParent.genesisBlockHeader
                evmParent.blocks evmParent.accountMap evmParent.σ₀
                { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
                  transactionReceipts := evmParent.transactionReceipts }
                evmParent.substate source origin recipient gasPrice valueWei
                weiValue calldata depth header perm))
            targetOutcome),
        (hTargetGasForX hTrace).gasBound ≤ gasNat)
    (hUInt256 : gasNat < EvmYul.UInt256.size)
    (inOffset inSize outOffset outSize : EvmYul.UInt256)
    {targetGas : EvmYul.UInt256}
    (hReturnedGas :
      ∀ {targetOutcome evmChild output},
        SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome →
          Assembly.GasAware.XResultAgrees targetOutcome
            (.success evmChild output) →
          gasAvailableRel
            (yulParent.toMachineState.finishExternalCall output
              inOffset inSize outOffset outSize).gasAvailable
            targetGas) :
    ∃ (evmFuel : Nat) (kind : Assembly.HaltKind)
      (compiler : Objects.Source.State) (halt : Assembly.Halt)
      (evmChild : EVMState) (output : ByteArray),
      EvmYul.Yul.callDispatcher referenceFuel (some program.contract)
          (.Ok initialShared initialStore) =
        .error (.YulHalt (.Ok yulChild childStore) value) ∧
        terminalRel kind value (.Ok yulChild childStore) compiler ∧
        SourceLowered.WholeProgramOutcomeRel sourceOutcome (.halted halt) ∧
        halt.kind = kind ∧
        EvmYul.EVM.Θ evmFuel.succ.succ blobVersionedHashes
          evmParent.createdAccounts evmParent.genesisBlockHeader
          evmParent.blocks evmParent.accountMap evmParent.σ₀
          { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
            transactionReceipts := evmParent.transactionReceipts }
          evmParent.substate source origin recipient
          (.Code (Assembly.Bytecode.encodeTarget target))
          (EvmYul.UInt256.ofNat gasNat) gasPrice valueWei weiValue calldata
          depth header perm =
            .ok (evmChild.createdAccounts,
              if evmChild.accountMap.isEmpty then evmParent.accountMap
              else evmChild.accountMap,
              evmChild.gasAvailable,
              if evmChild.accountMap.isEmpty then evmParent.substate
              else evmChild.substate,
              true, output) ∧
        halt.kind ≠ .revert ∧
          ∃ yulAfter,
            EvmYul.Yul.restoreSuccessfulContractCallState
                (.Ok yulParent parentStore)
                (.Ok yulChild childStore)
                restoreStore output inOffset inSize outOffset outSize =
              .ok (.Ok yulAfter restoreStore, [⟨1⟩]) ∧
            Reference.SharedStateRel
              (stateRelConfig varStackRel terminalCfgRel revertCfgRel
                gasAvailableRel gasValueRel totalGasRel)
              yulAfter
              { evmParent with
                toMachineState :=
                  { evmParent.toMachineState.finishExternalCall output
                      inOffset inSize outOffset outSize with
                    gasAvailable := targetGas }
                accountMap :=
                  if evmChild.accountMap.isEmpty then
                    evmParent.accountMap
                  else
                    evmChild.accountMap
                substate :=
                  if evmChild.accountMap.isEmpty then
                    evmParent.substate
                  else
                    evmChild.substate
                createdAccounts := evmChild.createdAccounts } := by
  rcases
      compile_preserves_of_installed_callDispatcher_yulHalt_sourceStaticBoundary_installedGas_XResult
        (prim := prim) hPrim
        (outcomeRel :=
          Program.RecursiveBridgeSemanticContracts.dispatcherOutcomeRel
            (stateRelConfig varStackRel terminalCfgRel revertCfgRel
              gasAvailableRel gasValueRel totalGasRel)
            terminalRel revertRel program (.Ok initialShared initialStore))
        (program := program) (asm := asm) (target := target)
        (referenceFuel := referenceFuel) (sourceFuel := sourceFuel)
        (gas := gasNat) (shared := initialShared)
        (store := initialStore) (haltState := .Ok yulChild childStore)
        (value := value)
        (rawInitial :=
          thetaCodeRawInitialState target gasNat blobVersionedHashes
            evmParent.createdAccounts evmParent.genesisBlockHeader
            evmParent.blocks evmParent.accountMap evmParent.σ₀
            { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
              transactionReceipts := evmParent.transactionReceipts }
            evmParent.substate source origin recipient gasPrice valueWei
            weiValue calldata depth header perm)
        (sourceOutcome := sourceOutcome)
        hInstalled hCall hSourceRun hOutcomeRel hCompileBoundary
        (by
          simp [thetaCodeRawInitialState, Assembly.GasAware.installCodeAndGas])
        (by
          simp [thetaCodeRawInitialState, Assembly.GasAware.installCodeAndGas])
        hTargetGasForX hGasBound hUInt256 with
    ⟨_targetFuel, targetOutcome, evmFuel, _gasBound, evmResult,
      _hReferenceRun, _hTargetRun, _hOutcomeRel, hWhole, _hTrace,
      _hGasBound, hX, hAgree, _hDecode, _hJumpdest⟩
  have hXTheta :
      EvmYul.EVM.X evmFuel (Assembly.GasAware.validJumps target)
          (thetaCodeXInitialState target gasNat blobVersionedHashes
            evmParent.createdAccounts evmParent.genesisBlockHeader
            evmParent.blocks evmParent.accountMap evmParent.σ₀
            { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
              transactionReceipts := evmParent.transactionReceipts }
            evmParent.substate source origin recipient gasPrice valueWei
            weiValue calldata depth header perm) =
        .ok evmResult := by
    simpa [thetaCodeXInitialState] using hX
  rcases
      ordinaryCodeCall_haltedSuccessBranch_rel_of_childOutcome
        (varStackRel := varStackRel)
        (terminalCfgRel := terminalCfgRel)
        (revertCfgRel := revertCfgRel)
        (gasAvailableRel := gasAvailableRel)
        (gasValueRel := gasValueRel)
        (totalGasRel := totalGasRel)
        hParent hOutcomeRel hWhole hTerminalChild
        hTerminalNonRevert hXTheta hAgree
        inOffset inSize outOffset outSize
        (by
          intro evmChild output hResult
          exact hReturnedGas hWhole (by simpa [hResult] using hAgree)) with
    ⟨kind, compiler, halt, evmChild, output, hTerminal, hTargetOutcome,
      hKind, _hResult, hTheta, hRestore⟩
  exact
    ⟨evmFuel, kind, compiler, halt, evmChild, output, hCall,
      hTerminal, by simpa [hTargetOutcome] using hWhole, hKind,
      hTheta, hRestore⟩

theorem ordinaryCodeCall_haltedSuccessBranch_rel_of_installed_childDispatcher_afterAccess
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {varStackRel : Reference.VarStackRel}
    {terminalCfgRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop}
    {revertCfgRel : Reference.State → EVMState → Prop}
    {gasAvailableRel : Word → Word → Prop}
    {gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm}
    {totalGasRel : Nat → Nat → Prop}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    {referenceFuel sourceFuel gasNat : Nat}
    {initialShared yulParent yulChild : EvmYul.SharedState .Yul}
    {evmParent : EvmYul.SharedState .EVM}
    {initialStore parentStore childStore restoreStore :
      EvmYul.Yul.VarStore}
    {value : Word}
    {sourceOutcome : Objects.Source.Outcome}
    (hParent :
      Reference.SharedStateRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        yulParent evmParent)
    (hInstalled : initialShared.executionEnv.code = program.contract)
    (hCall :
      EvmYul.Yul.callDispatcher referenceFuel (some program.contract)
          (.Ok initialShared initialStore) =
        .error (.YulHalt (.Ok yulChild childStore) value))
    {blobVersionedHashes : List ByteArray}
    {source origin recipient addr : EvmYul.AccountAddress}
    {gasPrice valueWei weiValue : EvmYul.UInt256}
    {calldata : ByteArray}
    {depth : Nat}
    {header : EvmYul.BlockHeader}
    {perm : Bool}
    (hSourceRun :
      SourceLowered.run prim sourceFuel program
          (Assembly.GasAware.installCodeAndGas target gasNat
            (thetaCodeRawInitialState target gasNat blobVersionedHashes
              evmParent.createdAccounts evmParent.genesisBlockHeader
              evmParent.blocks evmParent.accountMap evmParent.σ₀
              { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
                transactionReceipts := evmParent.transactionReceipts }
              (EvmYul.State.addAccessedAccount evmParent.toState addr).substate
              source origin recipient gasPrice valueWei weiValue calldata depth
              header perm)) =
        .ok sourceOutcome)
    (hOutcomeRel :
      Program.RecursiveBridgeSemanticContracts.dispatcherOutcomeRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        terminalRel revertRel program (.Ok initialShared initialStore)
        (.yulHalt (.Ok yulChild childStore) value) sourceOutcome)
    (hTerminalChild :
      ∀ {kind compiler},
        terminalRel kind value (.Ok yulChild childStore) compiler →
          ExternalChildMergeRel yulChild compiler.shared)
    (hTerminalNonRevert :
      ∀ {kind compiler},
        terminalRel kind value (.Ok yulChild childStore) compiler →
          kind ≠ .revert)
    (hCompileBoundary :
      compileCheckedAssemblyTargetBytecodeResourcesSourceStatic? program =
        some (asm, target))
    (hTargetGasForX :
      ∀ {targetFuel targetOutcome},
        Assembly.Preservation.BlockTraceResult asm target targetFuel
          (Assembly.GasAware.installCodeAndGas target gasNat
            (thetaCodeRawInitialState target gasNat blobVersionedHashes
              evmParent.createdAccounts evmParent.genesisBlockHeader
              evmParent.blocks evmParent.accountMap evmParent.σ₀
              { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
                transactionReceipts := evmParent.transactionReceipts }
              (EvmYul.State.addAccessedAccount evmParent.toState addr).substate
              source origin recipient gasPrice valueWei weiValue calldata depth
              header perm))
          targetOutcome →
        Assembly.GasAware.XResultPreconditionAssumptions target
          (Assembly.GasAware.installCodeAndGas target gasNat
            (thetaCodeRawInitialState target gasNat blobVersionedHashes
              evmParent.createdAccounts evmParent.genesisBlockHeader
              evmParent.blocks evmParent.accountMap evmParent.σ₀
              { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
                transactionReceipts := evmParent.transactionReceipts }
              (EvmYul.State.addAccessedAccount evmParent.toState addr).substate
              source origin recipient gasPrice valueWei weiValue calldata depth
              header perm))
          targetOutcome)
    (hGasBound :
      ∀ {targetFuel targetOutcome}
        (hTrace :
          Assembly.Preservation.BlockTraceResult asm target targetFuel
            (Assembly.GasAware.installCodeAndGas target gasNat
              (thetaCodeRawInitialState target gasNat blobVersionedHashes
                evmParent.createdAccounts evmParent.genesisBlockHeader
                evmParent.blocks evmParent.accountMap evmParent.σ₀
                { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
                  transactionReceipts := evmParent.transactionReceipts }
                (EvmYul.State.addAccessedAccount
                  evmParent.toState addr).substate
                source origin recipient gasPrice valueWei weiValue calldata depth
                header perm))
            targetOutcome),
        (hTargetGasForX hTrace).gasBound ≤ gasNat)
    (hUInt256 : gasNat < EvmYul.UInt256.size)
    (inOffset inSize outOffset outSize : EvmYul.UInt256)
    {targetGas : EvmYul.UInt256}
    (hReturnedGas :
      ∀ {targetOutcome evmChild output},
        SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome →
          Assembly.GasAware.XResultAgrees targetOutcome
            (.success evmChild output) →
          gasAvailableRel
            (yulParent.toMachineState.finishExternalCall output
              inOffset inSize outOffset outSize).gasAvailable
            targetGas) :
    ∃ (evmFuel : Nat) (kind : Assembly.HaltKind)
      (compiler : Objects.Source.State) (halt : Assembly.Halt)
      (evmChild : EVMState) (output : ByteArray),
      EvmYul.Yul.callDispatcher referenceFuel (some program.contract)
          (.Ok initialShared initialStore) =
        .error (.YulHalt (.Ok yulChild childStore) value) ∧
        terminalRel kind value (.Ok yulChild childStore) compiler ∧
        SourceLowered.WholeProgramOutcomeRel sourceOutcome (.halted halt) ∧
        halt.kind = kind ∧
        EvmYul.EVM.Θ evmFuel.succ.succ blobVersionedHashes
          evmParent.createdAccounts evmParent.genesisBlockHeader
          evmParent.blocks evmParent.accountMap evmParent.σ₀
          { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
            transactionReceipts := evmParent.transactionReceipts }
          (EvmYul.State.addAccessedAccount evmParent.toState addr).substate
          source origin recipient (.Code (Assembly.Bytecode.encodeTarget target))
          (EvmYul.UInt256.ofNat gasNat) gasPrice valueWei weiValue calldata
          depth header perm =
            .ok (evmChild.createdAccounts,
              if evmChild.accountMap.isEmpty then evmParent.accountMap
              else evmChild.accountMap,
              evmChild.gasAvailable,
              if evmChild.accountMap.isEmpty then
                (EvmYul.State.addAccessedAccount
                  evmParent.toState addr).substate
              else evmChild.substate,
              true, output) ∧
        halt.kind ≠ .revert ∧
          ∃ yulAfter,
            EvmYul.Yul.restoreSuccessfulContractCallState
                (EvmYul.Yul.addAccessedAccount
                  (.Ok yulParent parentStore) addr)
                (.Ok yulChild childStore)
                restoreStore output inOffset inSize outOffset outSize =
              .ok (.Ok yulAfter restoreStore, [⟨1⟩]) ∧
            Reference.SharedStateRel
              (stateRelConfig varStackRel terminalCfgRel revertCfgRel
                gasAvailableRel gasValueRel totalGasRel)
              yulAfter
              { evmParent with
                toMachineState :=
                  { evmParent.toMachineState.finishExternalCall output
                      inOffset inSize outOffset outSize with
                    gasAvailable := targetGas }
                accountMap :=
                  if evmChild.accountMap.isEmpty then
                    evmParent.accountMap
                  else
                    evmChild.accountMap
                substate :=
                  if evmChild.accountMap.isEmpty then
                    (EvmYul.State.addAccessedAccount
                      evmParent.toState addr).substate
                  else
                    evmChild.substate
                createdAccounts := evmChild.createdAccounts } := by
  let yulAccessed : EvmYul.SharedState .Yul :=
    { yulParent with
      toState := EvmYul.State.addAccessedAccount yulParent.toState addr }
  let evmAccessed : EvmYul.SharedState .EVM :=
    { evmParent with
      toState := EvmYul.State.addAccessedAccount evmParent.toState addr }
  have hParentAccessed :
      Reference.SharedStateRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        yulAccessed evmAccessed := by
    simpa [yulAccessed, evmAccessed] using
      sharedStateRel_addAccessedAccount hParent addr
  have hSourceRunAccessed :
      SourceLowered.run prim sourceFuel program
          (Assembly.GasAware.installCodeAndGas target gasNat
            (thetaCodeRawInitialState target gasNat blobVersionedHashes
              evmAccessed.createdAccounts evmAccessed.genesisBlockHeader
              evmAccessed.blocks evmAccessed.accountMap evmAccessed.σ₀
              { totalGasUsedInBlock := evmAccessed.totalGasUsedInBlock
                transactionReceipts := evmAccessed.transactionReceipts }
              evmAccessed.substate source origin recipient gasPrice valueWei
              weiValue calldata depth header perm)) =
        .ok sourceOutcome := by
    simpa [evmAccessed] using hSourceRun
  let hTargetGasForXAccessed :
      ∀ {targetFuel targetOutcome},
        Assembly.Preservation.BlockTraceResult asm target targetFuel
          (Assembly.GasAware.installCodeAndGas target gasNat
            (thetaCodeRawInitialState target gasNat blobVersionedHashes
              evmAccessed.createdAccounts evmAccessed.genesisBlockHeader
              evmAccessed.blocks evmAccessed.accountMap evmAccessed.σ₀
              { totalGasUsedInBlock := evmAccessed.totalGasUsedInBlock
                transactionReceipts := evmAccessed.transactionReceipts }
              evmAccessed.substate source origin recipient gasPrice valueWei
              weiValue calldata depth header perm))
          targetOutcome →
        Assembly.GasAware.XResultPreconditionAssumptions target
          (Assembly.GasAware.installCodeAndGas target gasNat
            (thetaCodeRawInitialState target gasNat blobVersionedHashes
              evmAccessed.createdAccounts evmAccessed.genesisBlockHeader
              evmAccessed.blocks evmAccessed.accountMap evmAccessed.σ₀
              { totalGasUsedInBlock := evmAccessed.totalGasUsedInBlock
                transactionReceipts := evmAccessed.transactionReceipts }
              evmAccessed.substate source origin recipient gasPrice valueWei
              weiValue calldata depth header perm))
          targetOutcome := by
    intro targetFuel targetOutcome hTrace
    exact hTargetGasForX (by simpa [evmAccessed] using hTrace)
  have hGasBoundAccessed :
      ∀ {targetFuel targetOutcome}
        (hTrace :
          Assembly.Preservation.BlockTraceResult asm target targetFuel
            (Assembly.GasAware.installCodeAndGas target gasNat
              (thetaCodeRawInitialState target gasNat blobVersionedHashes
                evmAccessed.createdAccounts evmAccessed.genesisBlockHeader
                evmAccessed.blocks evmAccessed.accountMap evmAccessed.σ₀
                { totalGasUsedInBlock := evmAccessed.totalGasUsedInBlock
                  transactionReceipts := evmAccessed.transactionReceipts }
                evmAccessed.substate source origin recipient gasPrice valueWei
                weiValue calldata depth header perm))
            targetOutcome),
        (hTargetGasForXAccessed hTrace).gasBound ≤ gasNat := by
    intro targetFuel targetOutcome hTrace
    exact hGasBound (by simpa [evmAccessed] using hTrace)
  have hReturnedGasAccessed :
      ∀ {targetOutcome evmChild output},
        SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome →
          Assembly.GasAware.XResultAgrees targetOutcome
            (.success evmChild output) →
          gasAvailableRel
            (yulAccessed.toMachineState.finishExternalCall output
              inOffset inSize outOffset outSize).gasAvailable
            targetGas := by
    intro targetOutcome evmChild output hWhole hAgree
    simpa [yulAccessed] using hReturnedGas hWhole hAgree
  simpa [yulAccessed, evmAccessed, EvmYul.Yul.addAccessedAccount,
    EvmYul.Yul.State.setState, EvmYul.Yul.State.toState,
    EvmYul.State.addAccessedAccount]
    using
      ordinaryCodeCall_haltedSuccessBranch_rel_of_installed_childDispatcher
        (prim := prim) hPrim
        (varStackRel := varStackRel)
        (terminalCfgRel := terminalCfgRel)
        (revertCfgRel := revertCfgRel)
        (gasAvailableRel := gasAvailableRel)
        (gasValueRel := gasValueRel)
        (totalGasRel := totalGasRel)
        hParentAccessed hInstalled hCall hSourceRunAccessed hOutcomeRel
        hTerminalChild hTerminalNonRevert hCompileBoundary
        hTargetGasForXAccessed hGasBoundAccessed hUInt256
        inOffset inSize outOffset outSize
        hReturnedGasAccessed

theorem Theta_code_revert_of_X_installedCode
    {fuel gasNat : Nat}
    {blobVersionedHashes : List ByteArray}
    {createdAccounts : Batteries.RBSet EvmYul.AccountAddress compare}
    {genesisBlockHeader : EvmYul.BlockHeader}
    {blocks : EvmYul.ProcessedBlocks}
    {accountMap sigma0 : EvmYul.AccountMap .EVM}
    {chainContext : EvmYul.EVM.ChildFrameChainContext}
    {substate : EvmYul.Substate}
    {source origin recipient : EvmYul.AccountAddress}
    {target : Assembly.TargetProgram}
    {gasPrice value weiValue : EvmYul.UInt256}
    {calldata output : ByteArray}
    {depth : Nat}
    {header : EvmYul.BlockHeader}
    {perm : Bool}
    {returnedGas : EvmYul.UInt256}
    (hX :
      EvmYul.EVM.X fuel (Assembly.GasAware.validJumps target)
          (thetaCodeXInitialState target gasNat blobVersionedHashes
            createdAccounts genesisBlockHeader blocks accountMap sigma0
            chainContext substate source origin recipient gasPrice value
            weiValue calldata depth header perm) =
        .ok (.revert returnedGas output)) :
    EvmYul.EVM.Θ fuel.succ.succ blobVersionedHashes createdAccounts
        genesisBlockHeader blocks accountMap sigma0 chainContext substate
        source origin recipient (.Code (Assembly.Bytecode.encodeTarget target))
        (EvmYul.UInt256.ofNat gasNat) gasPrice value weiValue calldata depth
        header perm =
      .ok (createdAccounts, accountMap, returnedGas, substate, false,
        output) := by
  rw [Theta_code_succ_succ_eq_X_installedCode]
  simp [hX]

theorem ordinaryCodeCall_revertBranch_rel
    {cfg : Reference.StateRelConfig}
    {yulParent : EvmYul.SharedState .Yul}
    {evmParent : EvmYul.SharedState .EVM}
    (hParent : Reference.SharedStateRel cfg yulParent evmParent)
    (parentStore childStore : EvmYul.Yul.VarStore)
    (addr : EvmYul.AccountAddress)
    {yulChild : EvmYul.SharedState .Yul}
    {halt : Assembly.Halt}
    {fuel gasNat : Nat}
    {blobVersionedHashes : List ByteArray}
    {source origin recipient : EvmYul.AccountAddress}
    {target : Assembly.TargetProgram}
    {gasPrice value weiValue : EvmYul.UInt256}
    {calldata output : ByteArray}
    {depth : Nat}
    {header : EvmYul.BlockHeader}
    {perm : Bool}
    {returnedGas : EvmYul.UInt256}
    {asm : Assembly.Program}
    {targetFuel : Nat} {initial : EVMState}
    (hTargetChild :
      Reference.SharedStateRel cfg yulChild halt.state.toSharedState)
    (hTrace :
      Assembly.Preservation.BlockTraceResult asm target targetFuel initial
        (.halted halt))
    (hX :
      EvmYul.EVM.X fuel (Assembly.GasAware.validJumps target)
          (thetaCodeXInitialState target gasNat blobVersionedHashes
            evmParent.createdAccounts evmParent.genesisBlockHeader
            evmParent.blocks evmParent.accountMap evmParent.σ₀
            { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
              transactionReceipts := evmParent.transactionReceipts }
            (EvmYul.State.addAccessedAccount evmParent.toState addr).substate
            source origin recipient gasPrice value weiValue calldata depth
            header perm) =
        .ok (.revert returnedGas output))
    (hAgree :
      Assembly.GasAware.XResultAgrees (.halted halt)
        (.revert returnedGas output))
    (inOffset inSize outOffset outSize : EvmYul.UInt256)
    (hGas :
      cfg.gasAvailableRel
        (yulParent.toMachineState.finishExternalCall output
          inOffset inSize outOffset outSize).gasAvailable
        returnedGas) :
    EvmYul.EVM.Θ fuel.succ.succ blobVersionedHashes
        evmParent.createdAccounts evmParent.genesisBlockHeader
        evmParent.blocks evmParent.accountMap evmParent.σ₀
        { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
          transactionReceipts := evmParent.transactionReceipts }
        (EvmYul.State.addAccessedAccount evmParent.toState addr).substate
        source origin recipient (.Code (Assembly.Bytecode.encodeTarget target))
        (EvmYul.UInt256.ofNat gasNat) gasPrice value weiValue calldata depth
        header perm =
      .ok (evmParent.createdAccounts, evmParent.accountMap, returnedGas,
        (EvmYul.State.addAccessedAccount evmParent.toState addr).substate,
        false, output) ∧
      halt.kind = .revert ∧
        ∃ yulAfter,
          EvmYul.Yul.restoreRevertedContractCallState
              (EvmYul.Yul.addAccessedAccount
                (.Ok yulParent parentStore) addr)
              (.Ok yulChild childStore)
              inOffset inSize outOffset outSize =
            .ok (.Ok yulAfter parentStore, [⟨0⟩]) ∧
          Reference.SharedStateRel cfg yulAfter
            { evmParent with
              toMachineState :=
                { evmParent.toMachineState.finishExternalCall output
                    inOffset inSize outOffset outSize with
                  gasAvailable := returnedGas }
              substate :=
                (EvmYul.State.addAccessedAccount
                  evmParent.toState addr).substate } := by
  exact
    ⟨Theta_code_revert_of_X_installedCode hX,
      restoreRevertedContractCallState_of_XResultAgrees_halted_revert_trace
        hParent parentStore childStore addr hTargetChild hTrace hAgree
        inOffset inSize outOffset outSize hGas⟩

theorem ordinaryCodeCall_revertBranch_rel_withTargetGas
    {cfg : Reference.StateRelConfig}
    {yulParent : EvmYul.SharedState .Yul}
    {evmParent : EvmYul.SharedState .EVM}
    (hParent : Reference.SharedStateRel cfg yulParent evmParent)
    (parentStore childStore : EvmYul.Yul.VarStore)
    (addr : EvmYul.AccountAddress)
    {yulChild : EvmYul.SharedState .Yul}
    {halt : Assembly.Halt}
    {fuel gasNat : Nat}
    {blobVersionedHashes : List ByteArray}
    {source origin recipient : EvmYul.AccountAddress}
    {target : Assembly.TargetProgram}
    {gasPrice value weiValue : EvmYul.UInt256}
    {calldata output : ByteArray}
    {depth : Nat}
    {header : EvmYul.BlockHeader}
    {perm : Bool}
    {returnedGas targetGas : EvmYul.UInt256}
    {asm : Assembly.Program}
    {targetFuel : Nat} {initial : EVMState}
    (hTargetChild :
      Reference.SharedStateRel cfg yulChild halt.state.toSharedState)
    (hTrace :
      Assembly.Preservation.BlockTraceResult asm target targetFuel initial
        (.halted halt))
    (hX :
      EvmYul.EVM.X fuel (Assembly.GasAware.validJumps target)
          (thetaCodeXInitialState target gasNat blobVersionedHashes
            evmParent.createdAccounts evmParent.genesisBlockHeader
            evmParent.blocks evmParent.accountMap evmParent.σ₀
            { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
              transactionReceipts := evmParent.transactionReceipts }
            (EvmYul.State.addAccessedAccount evmParent.toState addr).substate
            source origin recipient gasPrice value weiValue calldata depth
            header perm) =
        .ok (.revert returnedGas output))
    (hAgree :
      Assembly.GasAware.XResultAgrees (.halted halt)
        (.revert returnedGas output))
    (inOffset inSize outOffset outSize : EvmYul.UInt256)
    (hGas :
      cfg.gasAvailableRel
        (yulParent.toMachineState.finishExternalCall output
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    EvmYul.EVM.Θ fuel.succ.succ blobVersionedHashes
        evmParent.createdAccounts evmParent.genesisBlockHeader
        evmParent.blocks evmParent.accountMap evmParent.σ₀
        { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
          transactionReceipts := evmParent.transactionReceipts }
        (EvmYul.State.addAccessedAccount evmParent.toState addr).substate
        source origin recipient (.Code (Assembly.Bytecode.encodeTarget target))
        (EvmYul.UInt256.ofNat gasNat) gasPrice value weiValue calldata depth
        header perm =
      .ok (evmParent.createdAccounts, evmParent.accountMap, returnedGas,
        (EvmYul.State.addAccessedAccount evmParent.toState addr).substate,
        false, output) ∧
      halt.kind = .revert ∧
        ∃ yulAfter,
          EvmYul.Yul.restoreRevertedContractCallState
              (EvmYul.Yul.addAccessedAccount
                (.Ok yulParent parentStore) addr)
              (.Ok yulChild childStore)
              inOffset inSize outOffset outSize =
            .ok (.Ok yulAfter parentStore, [⟨0⟩]) ∧
          Reference.SharedStateRel cfg yulAfter
            { evmParent with
              toMachineState :=
                { evmParent.toMachineState.finishExternalCall output
                    inOffset inSize outOffset outSize with
                  gasAvailable := targetGas }
              substate :=
                (EvmYul.State.addAccessedAccount
                  evmParent.toState addr).substate } := by
  exact
    ⟨Theta_code_revert_of_X_installedCode hX,
      restoreRevertedContractCallState_of_XResultAgrees_halted_revert_trace_targetGas
        hParent parentStore childStore addr hTargetChild hTrace hAgree
        inOffset inSize outOffset outSize hGas⟩

theorem ordinaryCodeCall_revertBranch_rel_of_childOutcome
    {varStackRel : Reference.VarStackRel}
    {terminalCfgRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop}
    {revertCfgRel : Reference.State → EVMState → Prop}
    {gasAvailableRel : Word → Word → Prop}
    {gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm}
    {totalGasRel : Nat → Nat → Prop}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {program : Program}
    {initialShared yulParent yulChild : EvmYul.SharedState .Yul}
    {evmParent : EvmYul.SharedState .EVM}
    {initialStore parentStore childStore : EvmYul.Yul.VarStore}
    {sourceOutcome : Objects.Source.Outcome}
    {targetOutcome : Assembly.StepResult}
    {evmResult : EvmYul.EVM.ExecutionResult EVMState}
    (hParent :
      Reference.SharedStateRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        yulParent evmParent)
    (hOutcomeRel :
      Program.RecursiveBridgeSemanticContracts.dispatcherOutcomeRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        terminalRel revertRel program (.Ok initialShared initialStore)
        (.revert (.Ok yulChild childStore)) sourceOutcome)
    (hWhole :
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome)
    (hRevertShared :
      ∀ {compiler},
        revertRel (.Ok yulChild childStore) compiler →
          Reference.SharedStateRel
            (stateRelConfig varStackRel terminalCfgRel revertCfgRel
              gasAvailableRel gasValueRel totalGasRel)
            yulChild compiler.shared)
    {fuel gasNat : Nat}
    {blobVersionedHashes : List ByteArray}
    {source origin recipient addr : EvmYul.AccountAddress}
    {target : Assembly.TargetProgram}
    {gasPrice value weiValue : EvmYul.UInt256}
    {calldata : ByteArray}
    {depth : Nat}
    {header : EvmYul.BlockHeader}
    {perm : Bool}
    (hX :
      EvmYul.EVM.X fuel (Assembly.GasAware.validJumps target)
          (thetaCodeXInitialState target gasNat blobVersionedHashes
            evmParent.createdAccounts evmParent.genesisBlockHeader
            evmParent.blocks evmParent.accountMap evmParent.σ₀
            { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
              transactionReceipts := evmParent.transactionReceipts }
            (EvmYul.State.addAccessedAccount evmParent.toState addr).substate
            source origin recipient gasPrice value weiValue calldata depth
            header perm) =
        .ok evmResult)
    (hAgree :
      Assembly.GasAware.XResultAgrees targetOutcome evmResult)
    (hTargetChildGas :
      ∀ {halt}, targetOutcome = .halted halt →
        gasAvailableRel yulChild.toMachineState.gasAvailable
          halt.state.gasAvailable)
    {asm : Assembly.Program} {targetFuel : Nat} {initial : EVMState}
    (hTrace :
      Assembly.Preservation.BlockTraceResult asm target targetFuel initial
        targetOutcome)
    (inOffset inSize outOffset outSize : EvmYul.UInt256)
    (hReturnedGas :
      ∀ {returnedGas output}, evmResult = .revert returnedGas output →
        gasAvailableRel
          (yulParent.toMachineState.finishExternalCall output
            inOffset inSize outOffset outSize).gasAvailable
          returnedGas) :
    ∃ compiler halt returnedGas output,
      revertRel (.Ok yulChild childStore) compiler ∧
        targetOutcome = .halted halt ∧
        evmResult = .revert returnedGas output ∧
        EvmYul.EVM.Θ fuel.succ.succ blobVersionedHashes
          evmParent.createdAccounts evmParent.genesisBlockHeader
          evmParent.blocks evmParent.accountMap evmParent.σ₀
          { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
            transactionReceipts := evmParent.transactionReceipts }
          (EvmYul.State.addAccessedAccount evmParent.toState addr).substate
          source origin recipient (.Code (Assembly.Bytecode.encodeTarget target))
          (EvmYul.UInt256.ofNat gasNat) gasPrice value weiValue calldata depth
          header perm =
            .ok (evmParent.createdAccounts, evmParent.accountMap, returnedGas,
              (EvmYul.State.addAccessedAccount evmParent.toState addr).substate,
              false, output) ∧
        halt.kind = .revert ∧
          ∃ yulAfter,
            EvmYul.Yul.restoreRevertedContractCallState
                (EvmYul.Yul.addAccessedAccount
                  (.Ok yulParent parentStore) addr)
                (.Ok yulChild childStore)
                inOffset inSize outOffset outSize =
              .ok (.Ok yulAfter parentStore, [⟨0⟩]) ∧
            Reference.SharedStateRel
              (stateRelConfig varStackRel terminalCfgRel revertCfgRel
                gasAvailableRel gasValueRel totalGasRel)
              yulAfter
              { evmParent with
                toMachineState :=
                  { evmParent.toMachineState.finishExternalCall output
                      inOffset inSize outOffset outSize with
                    gasAvailable := returnedGas }
                substate :=
                  (EvmYul.State.addAccessedAccount
                    evmParent.toState addr).substate } := by
  rcases
      dispatcherOutcomeRel_revert_ok_whole_childRelations
        (varStackRel := varStackRel)
        (terminalCfgRel := terminalCfgRel)
        (revertCfgRel := revertCfgRel)
        (gasAvailableRel := gasAvailableRel)
        (gasValueRel := gasValueRel)
        (totalGasRel := totalGasRel)
        hOutcomeRel hWhole hRevertShared hTargetChildGas with
    ⟨compiler, halt, hRevert, _hSource, hTarget, hKind,
      hTargetChild, _hTargetChildWorld⟩
  have hAgreeHalted :
      Assembly.GasAware.XResultAgrees (.halted halt) evmResult := by
    simpa [hTarget] using hAgree
  rcases XResultAgrees_halted_revert_shape hAgreeHalted hKind with
    ⟨returnedGas, output, hResult, hAgreeRevert⟩
  have hXRevert :
      EvmYul.EVM.X fuel (Assembly.GasAware.validJumps target)
          (thetaCodeXInitialState target gasNat blobVersionedHashes
            evmParent.createdAccounts evmParent.genesisBlockHeader
            evmParent.blocks evmParent.accountMap evmParent.σ₀
            { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
              transactionReceipts := evmParent.transactionReceipts }
            (EvmYul.State.addAccessedAccount evmParent.toState addr).substate
            source origin recipient gasPrice value weiValue calldata depth
            header perm) =
        .ok (.revert returnedGas output) := by
    simpa [hResult] using hX
  have hTraceHalt :
      Assembly.Preservation.BlockTraceResult asm target targetFuel initial
        (.halted halt) := by
    simpa [hTarget] using hTrace
  rcases
      ordinaryCodeCall_revertBranch_rel
        (cfg :=
          stateRelConfig varStackRel terminalCfgRel revertCfgRel
            gasAvailableRel gasValueRel totalGasRel)
        hParent parentStore childStore addr
        hTargetChild hTraceHalt hXRevert hAgreeRevert
        inOffset inSize outOffset outSize (hReturnedGas hResult) with
    ⟨hTheta, hRestore⟩
  exact
    ⟨compiler, halt, returnedGas, output, hRevert, hTarget, hResult,
      hTheta, hRestore⟩

theorem ordinaryCodeCall_revertBranch_rel_of_childOutcome_withTargetGas
    {varStackRel : Reference.VarStackRel}
    {terminalCfgRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop}
    {revertCfgRel : Reference.State → EVMState → Prop}
    {gasAvailableRel : Word → Word → Prop}
    {gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm}
    {totalGasRel : Nat → Nat → Prop}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {program : Program}
    {initialShared yulParent yulChild : EvmYul.SharedState .Yul}
    {evmParent : EvmYul.SharedState .EVM}
    {initialStore parentStore childStore : EvmYul.Yul.VarStore}
    {sourceOutcome : Objects.Source.Outcome}
    {targetOutcome : Assembly.StepResult}
    {evmResult : EvmYul.EVM.ExecutionResult EVMState}
    (hParent :
      Reference.SharedStateRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        yulParent evmParent)
    (hOutcomeRel :
      Program.RecursiveBridgeSemanticContracts.dispatcherOutcomeRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        terminalRel revertRel program (.Ok initialShared initialStore)
        (.revert (.Ok yulChild childStore)) sourceOutcome)
    (hWhole :
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome)
    (hRevertShared :
      ∀ {compiler},
        revertRel (.Ok yulChild childStore) compiler →
          Reference.SharedStateRel
            (stateRelConfig varStackRel terminalCfgRel revertCfgRel
              gasAvailableRel gasValueRel totalGasRel)
            yulChild compiler.shared)
    {fuel gasNat : Nat}
    {blobVersionedHashes : List ByteArray}
    {source origin recipient addr : EvmYul.AccountAddress}
    {target : Assembly.TargetProgram}
    {gasPrice value weiValue : EvmYul.UInt256}
    {calldata : ByteArray}
    {depth : Nat}
    {header : EvmYul.BlockHeader}
    {perm : Bool}
    (hX :
      EvmYul.EVM.X fuel (Assembly.GasAware.validJumps target)
          (thetaCodeXInitialState target gasNat blobVersionedHashes
            evmParent.createdAccounts evmParent.genesisBlockHeader
            evmParent.blocks evmParent.accountMap evmParent.σ₀
            { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
              transactionReceipts := evmParent.transactionReceipts }
            (EvmYul.State.addAccessedAccount evmParent.toState addr).substate
            source origin recipient gasPrice value weiValue calldata depth
            header perm) =
        .ok evmResult)
    (hAgree :
      Assembly.GasAware.XResultAgrees targetOutcome evmResult)
    (hTargetChildGas :
      ∀ {halt}, targetOutcome = .halted halt →
        gasAvailableRel yulChild.toMachineState.gasAvailable
          halt.state.gasAvailable)
    {asm : Assembly.Program} {targetFuel : Nat} {initial : EVMState}
    (hTrace :
      Assembly.Preservation.BlockTraceResult asm target targetFuel initial
        targetOutcome)
    (inOffset inSize outOffset outSize : EvmYul.UInt256)
    {targetGas : EvmYul.UInt256}
    (hTargetGas :
      ∀ {returnedGas output}, evmResult = .revert returnedGas output →
        gasAvailableRel
          (yulParent.toMachineState.finishExternalCall output
            inOffset inSize outOffset outSize).gasAvailable
          targetGas) :
    ∃ compiler halt returnedGas output,
      revertRel (.Ok yulChild childStore) compiler ∧
        targetOutcome = .halted halt ∧
        evmResult = .revert returnedGas output ∧
        EvmYul.EVM.Θ fuel.succ.succ blobVersionedHashes
          evmParent.createdAccounts evmParent.genesisBlockHeader
          evmParent.blocks evmParent.accountMap evmParent.σ₀
          { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
            transactionReceipts := evmParent.transactionReceipts }
          (EvmYul.State.addAccessedAccount evmParent.toState addr).substate
          source origin recipient (.Code (Assembly.Bytecode.encodeTarget target))
          (EvmYul.UInt256.ofNat gasNat) gasPrice value weiValue calldata depth
          header perm =
            .ok (evmParent.createdAccounts, evmParent.accountMap, returnedGas,
              (EvmYul.State.addAccessedAccount evmParent.toState addr).substate,
              false, output) ∧
        halt.kind = .revert ∧
          ∃ yulAfter,
            EvmYul.Yul.restoreRevertedContractCallState
                (EvmYul.Yul.addAccessedAccount
                  (.Ok yulParent parentStore) addr)
                (.Ok yulChild childStore)
                inOffset inSize outOffset outSize =
              .ok (.Ok yulAfter parentStore, [⟨0⟩]) ∧
            Reference.SharedStateRel
              (stateRelConfig varStackRel terminalCfgRel revertCfgRel
                gasAvailableRel gasValueRel totalGasRel)
              yulAfter
              { evmParent with
                toMachineState :=
                  { evmParent.toMachineState.finishExternalCall output
                      inOffset inSize outOffset outSize with
                    gasAvailable := targetGas }
                substate :=
                  (EvmYul.State.addAccessedAccount
                    evmParent.toState addr).substate } := by
  rcases
      dispatcherOutcomeRel_revert_ok_whole_childRelations
        (varStackRel := varStackRel)
        (terminalCfgRel := terminalCfgRel)
        (revertCfgRel := revertCfgRel)
        (gasAvailableRel := gasAvailableRel)
        (gasValueRel := gasValueRel)
        (totalGasRel := totalGasRel)
        hOutcomeRel hWhole hRevertShared hTargetChildGas with
    ⟨compiler, halt, hRevert, _hSource, hTarget, hKind,
      hTargetChild, _hTargetChildWorld⟩
  have hAgreeHalted :
      Assembly.GasAware.XResultAgrees (.halted halt) evmResult := by
    simpa [hTarget] using hAgree
  rcases XResultAgrees_halted_revert_shape hAgreeHalted hKind with
    ⟨returnedGas, output, hResult, hAgreeRevert⟩
  have hXRevert :
      EvmYul.EVM.X fuel (Assembly.GasAware.validJumps target)
          (thetaCodeXInitialState target gasNat blobVersionedHashes
            evmParent.createdAccounts evmParent.genesisBlockHeader
            evmParent.blocks evmParent.accountMap evmParent.σ₀
            { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
              transactionReceipts := evmParent.transactionReceipts }
            (EvmYul.State.addAccessedAccount evmParent.toState addr).substate
            source origin recipient gasPrice value weiValue calldata depth
            header perm) =
        .ok (.revert returnedGas output) := by
    simpa [hResult] using hX
  have hTraceHalt :
      Assembly.Preservation.BlockTraceResult asm target targetFuel initial
        (.halted halt) := by
    simpa [hTarget] using hTrace
  rcases
      ordinaryCodeCall_revertBranch_rel_withTargetGas
        (cfg :=
          stateRelConfig varStackRel terminalCfgRel revertCfgRel
            gasAvailableRel gasValueRel totalGasRel)
        hParent parentStore childStore addr
        hTargetChild hTraceHalt hXRevert hAgreeRevert
        inOffset inSize outOffset outSize (hTargetGas hResult) with
    ⟨hTheta, hRestore⟩
  exact
    ⟨compiler, halt, returnedGas, output, hRevert, hTarget, hResult,
      hTheta, hRestore⟩

theorem ordinaryCodeCall_revertBranch_rel_of_installed_childDispatcher
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {varStackRel : Reference.VarStackRel}
    {terminalCfgRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop}
    {revertCfgRel : Reference.State → EVMState → Prop}
    {gasAvailableRel : Word → Word → Prop}
    {gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm}
    {totalGasRel : Nat → Nat → Prop}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    {referenceFuel sourceFuel gasNat : Nat}
    {initialShared yulParent yulChild : EvmYul.SharedState .Yul}
    {evmParent : EvmYul.SharedState .EVM}
    {initialStore parentStore childStore : EvmYul.Yul.VarStore}
    {sourceOutcome : Objects.Source.Outcome}
    (hParent :
      Reference.SharedStateRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        yulParent evmParent)
    (hInstalled : initialShared.executionEnv.code = program.contract)
    (hCall :
      EvmYul.Yul.callDispatcher referenceFuel (some program.contract)
          (.Ok initialShared initialStore) =
        .error (.Revert (.Ok yulChild childStore)))
    {blobVersionedHashes : List ByteArray}
    {source origin recipient addr : EvmYul.AccountAddress}
    {gasPrice value weiValue : EvmYul.UInt256}
    {calldata : ByteArray}
    {depth : Nat}
    {header : EvmYul.BlockHeader}
    {perm : Bool}
    (hSourceRun :
      SourceLowered.run prim sourceFuel program
          (Assembly.GasAware.installCodeAndGas target gasNat
            (thetaCodeRawInitialState target gasNat blobVersionedHashes
              evmParent.createdAccounts evmParent.genesisBlockHeader
              evmParent.blocks evmParent.accountMap evmParent.σ₀
              { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
                transactionReceipts := evmParent.transactionReceipts }
              (EvmYul.State.addAccessedAccount evmParent.toState addr).substate
              source origin recipient gasPrice value weiValue calldata depth
              header perm)) =
        .ok sourceOutcome)
    (hOutcomeRel :
      Program.RecursiveBridgeSemanticContracts.dispatcherOutcomeRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        terminalRel revertRel program (.Ok initialShared initialStore)
        (.revert (.Ok yulChild childStore)) sourceOutcome)
    (hRevertShared :
      ∀ {compiler},
        revertRel (.Ok yulChild childStore) compiler →
          Reference.SharedStateRel
            (stateRelConfig varStackRel terminalCfgRel revertCfgRel
              gasAvailableRel gasValueRel totalGasRel)
            yulChild compiler.shared)
    (hCompileBoundary :
      compileCheckedAssemblyTargetBytecodeResourcesSourceStatic? program =
        some (asm, target))
    (hTargetGasForX :
      ∀ {targetFuel targetOutcome},
        Assembly.Preservation.BlockTraceResult asm target targetFuel
          (Assembly.GasAware.installCodeAndGas target gasNat
            (thetaCodeRawInitialState target gasNat blobVersionedHashes
              evmParent.createdAccounts evmParent.genesisBlockHeader
              evmParent.blocks evmParent.accountMap evmParent.σ₀
              { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
                transactionReceipts := evmParent.transactionReceipts }
              (EvmYul.State.addAccessedAccount evmParent.toState addr).substate
              source origin recipient gasPrice value weiValue calldata depth
              header perm))
          targetOutcome →
        Assembly.GasAware.XResultPreconditionAssumptions target
          (Assembly.GasAware.installCodeAndGas target gasNat
            (thetaCodeRawInitialState target gasNat blobVersionedHashes
              evmParent.createdAccounts evmParent.genesisBlockHeader
              evmParent.blocks evmParent.accountMap evmParent.σ₀
              { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
                transactionReceipts := evmParent.transactionReceipts }
              (EvmYul.State.addAccessedAccount evmParent.toState addr).substate
              source origin recipient gasPrice value weiValue calldata depth
              header perm))
          targetOutcome)
    (hGasBound :
      ∀ {targetFuel targetOutcome}
        (hTrace :
          Assembly.Preservation.BlockTraceResult asm target targetFuel
            (Assembly.GasAware.installCodeAndGas target gasNat
              (thetaCodeRawInitialState target gasNat blobVersionedHashes
                evmParent.createdAccounts evmParent.genesisBlockHeader
                evmParent.blocks evmParent.accountMap evmParent.σ₀
                { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
                  transactionReceipts := evmParent.transactionReceipts }
                (EvmYul.State.addAccessedAccount
                  evmParent.toState addr).substate
                source origin recipient gasPrice value weiValue calldata depth
                header perm))
            targetOutcome),
        (hTargetGasForX hTrace).gasBound ≤ gasNat)
    (hUInt256 : gasNat < EvmYul.UInt256.size)
    (hTargetChildGas :
      ∀ {halt}, SourceLowered.WholeProgramOutcomeRel sourceOutcome
          (.halted halt) →
        gasAvailableRel yulChild.toMachineState.gasAvailable
          halt.state.gasAvailable)
    (inOffset inSize outOffset outSize : EvmYul.UInt256)
    (hReturnedGas :
      ∀ {targetOutcome returnedGas output},
        SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome →
          Assembly.GasAware.XResultAgrees targetOutcome
            (.revert returnedGas output) →
          gasAvailableRel
            (yulParent.toMachineState.finishExternalCall output
              inOffset inSize outOffset outSize).gasAvailable
            returnedGas) :
    ∃ (evmFuel : Nat) (compiler : Objects.Source.State)
      (halt : Assembly.Halt) (returnedGas : EvmYul.UInt256)
      (output : ByteArray),
      EvmYul.Yul.callDispatcher referenceFuel (some program.contract)
          (.Ok initialShared initialStore) =
        .error (.Revert (.Ok yulChild childStore)) ∧
        revertRel (.Ok yulChild childStore) compiler ∧
        SourceLowered.WholeProgramOutcomeRel sourceOutcome (.halted halt) ∧
        EvmYul.EVM.Θ evmFuel.succ.succ blobVersionedHashes
          evmParent.createdAccounts evmParent.genesisBlockHeader
          evmParent.blocks evmParent.accountMap evmParent.σ₀
          { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
            transactionReceipts := evmParent.transactionReceipts }
          (EvmYul.State.addAccessedAccount evmParent.toState addr).substate
          source origin recipient (.Code (Assembly.Bytecode.encodeTarget target))
          (EvmYul.UInt256.ofNat gasNat) gasPrice value weiValue calldata depth
          header perm =
            .ok (evmParent.createdAccounts, evmParent.accountMap, returnedGas,
              (EvmYul.State.addAccessedAccount evmParent.toState addr).substate,
              false, output) ∧
        halt.kind = .revert ∧
          ∃ yulAfter,
            EvmYul.Yul.restoreRevertedContractCallState
                (EvmYul.Yul.addAccessedAccount
                  (.Ok yulParent parentStore) addr)
                (.Ok yulChild childStore)
                inOffset inSize outOffset outSize =
              .ok (.Ok yulAfter parentStore, [⟨0⟩]) ∧
            Reference.SharedStateRel
              (stateRelConfig varStackRel terminalCfgRel revertCfgRel
                gasAvailableRel gasValueRel totalGasRel)
              yulAfter
              { evmParent with
                toMachineState :=
                  { evmParent.toMachineState.finishExternalCall output
                      inOffset inSize outOffset outSize with
                    gasAvailable := returnedGas }
                substate :=
                  (EvmYul.State.addAccessedAccount
                    evmParent.toState addr).substate } := by
  rcases
      compile_preserves_of_installed_callDispatcher_revert_sourceStaticBoundary_installedGas_XResult
        (prim := prim) hPrim
        (outcomeRel :=
          Program.RecursiveBridgeSemanticContracts.dispatcherOutcomeRel
            (stateRelConfig varStackRel terminalCfgRel revertCfgRel
              gasAvailableRel gasValueRel totalGasRel)
            terminalRel revertRel program (.Ok initialShared initialStore))
        (program := program) (asm := asm) (target := target)
        (referenceFuel := referenceFuel) (sourceFuel := sourceFuel)
        (gas := gasNat) (shared := initialShared)
        (store := initialStore) (revertState := .Ok yulChild childStore)
        (rawInitial :=
          thetaCodeRawInitialState target gasNat blobVersionedHashes
            evmParent.createdAccounts evmParent.genesisBlockHeader
            evmParent.blocks evmParent.accountMap evmParent.σ₀
            { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
              transactionReceipts := evmParent.transactionReceipts }
            (EvmYul.State.addAccessedAccount evmParent.toState addr).substate
            source origin recipient gasPrice value weiValue calldata depth
            header perm)
        (sourceOutcome := sourceOutcome)
        hInstalled hCall hSourceRun hOutcomeRel hCompileBoundary
        (by
          simp [thetaCodeRawInitialState, Assembly.GasAware.installCodeAndGas])
        (by
          simp [thetaCodeRawInitialState, Assembly.GasAware.installCodeAndGas])
        hTargetGasForX hGasBound hUInt256 with
    ⟨targetFuel, targetOutcome, evmFuel, _gasBound, evmResult,
      _hReferenceRun, _hTargetRun, _hOutcomeRel, hWhole, hTrace,
      _hGasBound, hX, hAgree, _hDecode, _hJumpdest⟩
  have hXTheta :
      EvmYul.EVM.X evmFuel (Assembly.GasAware.validJumps target)
          (thetaCodeXInitialState target gasNat blobVersionedHashes
            evmParent.createdAccounts evmParent.genesisBlockHeader
            evmParent.blocks evmParent.accountMap evmParent.σ₀
            { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
              transactionReceipts := evmParent.transactionReceipts }
            (EvmYul.State.addAccessedAccount evmParent.toState addr).substate
            source origin recipient gasPrice value weiValue calldata depth
            header perm) =
        .ok evmResult := by
    simpa [thetaCodeXInitialState] using hX
  rcases
      ordinaryCodeCall_revertBranch_rel_of_childOutcome
        (varStackRel := varStackRel)
        (terminalCfgRel := terminalCfgRel)
        (revertCfgRel := revertCfgRel)
        (gasAvailableRel := gasAvailableRel)
        (gasValueRel := gasValueRel)
        (totalGasRel := totalGasRel)
        hParent hOutcomeRel hWhole hRevertShared hXTheta hAgree
        (by
          intro halt hTarget
          exact hTargetChildGas (by simpa [hTarget] using hWhole))
        hTrace inOffset inSize outOffset outSize
        (by
          intro returnedGas output hResult
          exact hReturnedGas hWhole (by simpa [hResult] using hAgree)) with
    ⟨compiler, halt, returnedGas, output, hRevert, hTargetOutcome,
      _hResult, hTheta, hRestore⟩
  exact
    ⟨evmFuel, compiler, halt, returnedGas, output, hCall, hRevert,
      by simpa [hTargetOutcome] using hWhole, hTheta, hRestore⟩

theorem ordinaryCodeCall_revertBranch_rel_of_installed_childDispatcher_withTargetGas
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {varStackRel : Reference.VarStackRel}
    {terminalCfgRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop}
    {revertCfgRel : Reference.State → EVMState → Prop}
    {gasAvailableRel : Word → Word → Prop}
    {gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm}
    {totalGasRel : Nat → Nat → Prop}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    {referenceFuel sourceFuel gasNat : Nat}
    {initialShared yulParent yulChild : EvmYul.SharedState .Yul}
    {evmParent : EvmYul.SharedState .EVM}
    {initialStore parentStore childStore : EvmYul.Yul.VarStore}
    {sourceOutcome : Objects.Source.Outcome}
    (hParent :
      Reference.SharedStateRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        yulParent evmParent)
    (hInstalled : initialShared.executionEnv.code = program.contract)
    (hCall :
      EvmYul.Yul.callDispatcher referenceFuel (some program.contract)
          (.Ok initialShared initialStore) =
        .error (.Revert (.Ok yulChild childStore)))
    {blobVersionedHashes : List ByteArray}
    {source origin recipient addr : EvmYul.AccountAddress}
    {gasPrice value weiValue : EvmYul.UInt256}
    {calldata : ByteArray}
    {depth : Nat}
    {header : EvmYul.BlockHeader}
    {perm : Bool}
    (hSourceRun :
      SourceLowered.run prim sourceFuel program
          (Assembly.GasAware.installCodeAndGas target gasNat
            (thetaCodeRawInitialState target gasNat blobVersionedHashes
              evmParent.createdAccounts evmParent.genesisBlockHeader
              evmParent.blocks evmParent.accountMap evmParent.σ₀
              { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
                transactionReceipts := evmParent.transactionReceipts }
              (EvmYul.State.addAccessedAccount evmParent.toState addr).substate
              source origin recipient gasPrice value weiValue calldata depth
              header perm)) =
        .ok sourceOutcome)
    (hOutcomeRel :
      Program.RecursiveBridgeSemanticContracts.dispatcherOutcomeRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        terminalRel revertRel program (.Ok initialShared initialStore)
        (.revert (.Ok yulChild childStore)) sourceOutcome)
    (hRevertShared :
      ∀ {compiler},
        revertRel (.Ok yulChild childStore) compiler →
          Reference.SharedStateRel
            (stateRelConfig varStackRel terminalCfgRel revertCfgRel
              gasAvailableRel gasValueRel totalGasRel)
            yulChild compiler.shared)
    (hCompileBoundary :
      compileCheckedAssemblyTargetBytecodeResourcesSourceStatic? program =
        some (asm, target))
    (hTargetGasForX :
      ∀ {targetFuel targetOutcome},
        Assembly.Preservation.BlockTraceResult asm target targetFuel
          (Assembly.GasAware.installCodeAndGas target gasNat
            (thetaCodeRawInitialState target gasNat blobVersionedHashes
              evmParent.createdAccounts evmParent.genesisBlockHeader
              evmParent.blocks evmParent.accountMap evmParent.σ₀
              { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
                transactionReceipts := evmParent.transactionReceipts }
              (EvmYul.State.addAccessedAccount evmParent.toState addr).substate
              source origin recipient gasPrice value weiValue calldata depth
              header perm))
          targetOutcome →
        Assembly.GasAware.XResultPreconditionAssumptions target
          (Assembly.GasAware.installCodeAndGas target gasNat
            (thetaCodeRawInitialState target gasNat blobVersionedHashes
              evmParent.createdAccounts evmParent.genesisBlockHeader
              evmParent.blocks evmParent.accountMap evmParent.σ₀
              { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
                transactionReceipts := evmParent.transactionReceipts }
              (EvmYul.State.addAccessedAccount evmParent.toState addr).substate
              source origin recipient gasPrice value weiValue calldata depth
              header perm))
          targetOutcome)
    (hGasBound :
      ∀ {targetFuel targetOutcome}
        (hTrace :
          Assembly.Preservation.BlockTraceResult asm target targetFuel
            (Assembly.GasAware.installCodeAndGas target gasNat
              (thetaCodeRawInitialState target gasNat blobVersionedHashes
                evmParent.createdAccounts evmParent.genesisBlockHeader
                evmParent.blocks evmParent.accountMap evmParent.σ₀
                { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
                  transactionReceipts := evmParent.transactionReceipts }
                (EvmYul.State.addAccessedAccount
                  evmParent.toState addr).substate
                source origin recipient gasPrice value weiValue calldata depth
                header perm))
            targetOutcome),
        (hTargetGasForX hTrace).gasBound ≤ gasNat)
    (hUInt256 : gasNat < EvmYul.UInt256.size)
    (hTargetChildGas :
      ∀ {halt}, SourceLowered.WholeProgramOutcomeRel sourceOutcome
          (.halted halt) →
        gasAvailableRel yulChild.toMachineState.gasAvailable
          halt.state.gasAvailable)
    (inOffset inSize outOffset outSize : EvmYul.UInt256)
    {targetGas : EvmYul.UInt256}
    (hTargetGas :
      ∀ {targetOutcome returnedGas output},
        SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome →
          Assembly.GasAware.XResultAgrees targetOutcome
            (.revert returnedGas output) →
          gasAvailableRel
            (yulParent.toMachineState.finishExternalCall output
              inOffset inSize outOffset outSize).gasAvailable
            targetGas) :
    ∃ (evmFuel : Nat) (compiler : Objects.Source.State)
      (halt : Assembly.Halt) (returnedGas : EvmYul.UInt256)
      (output : ByteArray),
      EvmYul.Yul.callDispatcher referenceFuel (some program.contract)
          (.Ok initialShared initialStore) =
        .error (.Revert (.Ok yulChild childStore)) ∧
        revertRel (.Ok yulChild childStore) compiler ∧
        SourceLowered.WholeProgramOutcomeRel sourceOutcome (.halted halt) ∧
        EvmYul.EVM.Θ evmFuel.succ.succ blobVersionedHashes
          evmParent.createdAccounts evmParent.genesisBlockHeader
          evmParent.blocks evmParent.accountMap evmParent.σ₀
          { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
            transactionReceipts := evmParent.transactionReceipts }
          (EvmYul.State.addAccessedAccount evmParent.toState addr).substate
          source origin recipient (.Code (Assembly.Bytecode.encodeTarget target))
          (EvmYul.UInt256.ofNat gasNat) gasPrice value weiValue calldata depth
          header perm =
            .ok (evmParent.createdAccounts, evmParent.accountMap, returnedGas,
              (EvmYul.State.addAccessedAccount evmParent.toState addr).substate,
              false, output) ∧
        halt.kind = .revert ∧
          ∃ yulAfter,
            EvmYul.Yul.restoreRevertedContractCallState
                (EvmYul.Yul.addAccessedAccount
                  (.Ok yulParent parentStore) addr)
                (.Ok yulChild childStore)
                inOffset inSize outOffset outSize =
              .ok (.Ok yulAfter parentStore, [⟨0⟩]) ∧
            Reference.SharedStateRel
              (stateRelConfig varStackRel terminalCfgRel revertCfgRel
                gasAvailableRel gasValueRel totalGasRel)
              yulAfter
              { evmParent with
                toMachineState :=
                  { evmParent.toMachineState.finishExternalCall output
                      inOffset inSize outOffset outSize with
                    gasAvailable := targetGas }
                substate :=
                  (EvmYul.State.addAccessedAccount
                    evmParent.toState addr).substate } := by
  rcases
      compile_preserves_of_installed_callDispatcher_revert_sourceStaticBoundary_installedGas_XResult
        (prim := prim) hPrim
        (outcomeRel :=
          Program.RecursiveBridgeSemanticContracts.dispatcherOutcomeRel
            (stateRelConfig varStackRel terminalCfgRel revertCfgRel
              gasAvailableRel gasValueRel totalGasRel)
            terminalRel revertRel program (.Ok initialShared initialStore))
        (program := program) (asm := asm) (target := target)
        (referenceFuel := referenceFuel) (sourceFuel := sourceFuel)
        (gas := gasNat) (shared := initialShared)
        (store := initialStore) (revertState := .Ok yulChild childStore)
        (rawInitial :=
          thetaCodeRawInitialState target gasNat blobVersionedHashes
            evmParent.createdAccounts evmParent.genesisBlockHeader
            evmParent.blocks evmParent.accountMap evmParent.σ₀
            { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
              transactionReceipts := evmParent.transactionReceipts }
            (EvmYul.State.addAccessedAccount evmParent.toState addr).substate
            source origin recipient gasPrice value weiValue calldata depth
            header perm)
        (sourceOutcome := sourceOutcome)
        hInstalled hCall hSourceRun hOutcomeRel hCompileBoundary
        (by
          simp [thetaCodeRawInitialState, Assembly.GasAware.installCodeAndGas])
        (by
          simp [thetaCodeRawInitialState, Assembly.GasAware.installCodeAndGas])
        hTargetGasForX hGasBound hUInt256 with
    ⟨targetFuel, targetOutcome, evmFuel, _gasBound, evmResult,
      _hReferenceRun, _hTargetRun, _hOutcomeRel, hWhole, hTrace,
      _hGasBound, hX, hAgree, _hDecode, _hJumpdest⟩
  have hXTheta :
      EvmYul.EVM.X evmFuel (Assembly.GasAware.validJumps target)
          (thetaCodeXInitialState target gasNat blobVersionedHashes
            evmParent.createdAccounts evmParent.genesisBlockHeader
            evmParent.blocks evmParent.accountMap evmParent.σ₀
            { totalGasUsedInBlock := evmParent.totalGasUsedInBlock
              transactionReceipts := evmParent.transactionReceipts }
            (EvmYul.State.addAccessedAccount evmParent.toState addr).substate
            source origin recipient gasPrice value weiValue calldata depth
            header perm) =
        .ok evmResult := by
    simpa [thetaCodeXInitialState] using hX
  rcases
      ordinaryCodeCall_revertBranch_rel_of_childOutcome_withTargetGas
        (varStackRel := varStackRel)
        (terminalCfgRel := terminalCfgRel)
        (revertCfgRel := revertCfgRel)
        (gasAvailableRel := gasAvailableRel)
        (gasValueRel := gasValueRel)
        (totalGasRel := totalGasRel)
        hParent hOutcomeRel hWhole hRevertShared hXTheta hAgree
        (by
          intro halt hTarget
          exact hTargetChildGas (by simpa [hTarget] using hWhole))
        hTrace inOffset inSize outOffset outSize
        (by
          intro returnedGas output hResult
          exact hTargetGas hWhole (by simpa [hResult] using hAgree)) with
    ⟨compiler, halt, returnedGas, output, hRevert, hTargetOutcome,
      _hResult, hTheta, hRestore⟩
  exact
    ⟨evmFuel, compiler, halt, returnedGas, output, hCall, hRevert,
      by simpa [hTargetOutcome] using hWhole, hTheta, hRestore⟩

theorem Theta_code_non_oog_error_of_X_installedCode
    {fuel gasNat : Nat}
    {blobVersionedHashes : List ByteArray}
    {createdAccounts : Batteries.RBSet EvmYul.AccountAddress compare}
    {genesisBlockHeader : EvmYul.BlockHeader}
    {blocks : EvmYul.ProcessedBlocks}
    {accountMap sigma0 : EvmYul.AccountMap .EVM}
    {chainContext : EvmYul.EVM.ChildFrameChainContext}
    {substate : EvmYul.Substate}
    {source origin recipient : EvmYul.AccountAddress}
    {target : Assembly.TargetProgram}
    {gasPrice value weiValue : EvmYul.UInt256}
    {calldata : ByteArray}
    {depth : Nat}
    {header : EvmYul.BlockHeader}
    {perm : Bool}
    {err : EvmYul.EVM.ExecutionException}
    (hX :
      EvmYul.EVM.X fuel (Assembly.GasAware.validJumps target)
          (thetaCodeXInitialState target gasNat blobVersionedHashes
            createdAccounts genesisBlockHeader blocks accountMap sigma0
            chainContext substate source origin recipient gasPrice value
            weiValue calldata depth header perm) =
        .error err)
    (hErr : (err == EvmYul.EVM.ExecutionException.OutOfFuel) = false) :
    EvmYul.EVM.Θ fuel.succ.succ blobVersionedHashes createdAccounts
        genesisBlockHeader blocks accountMap sigma0 chainContext substate
        source origin recipient (.Code (Assembly.Bytecode.encodeTarget target))
        (EvmYul.UInt256.ofNat gasNat) gasPrice value weiValue calldata depth
        header perm =
      .ok (createdAccounts, accountMap, ⟨0⟩, substate, false,
        ByteArray.empty) := by
  rw [Theta_code_succ_succ_eq_X_installedCode]
  simp [hX, hErr]

theorem Theta_code_oog_error_of_X_installedCode
    {fuel gasNat : Nat}
    {blobVersionedHashes : List ByteArray}
    {createdAccounts : Batteries.RBSet EvmYul.AccountAddress compare}
    {genesisBlockHeader : EvmYul.BlockHeader}
    {blocks : EvmYul.ProcessedBlocks}
    {accountMap sigma0 : EvmYul.AccountMap .EVM}
    {chainContext : EvmYul.EVM.ChildFrameChainContext}
    {substate : EvmYul.Substate}
    {source origin recipient : EvmYul.AccountAddress}
    {target : Assembly.TargetProgram}
    {gasPrice value weiValue : EvmYul.UInt256}
    {calldata : ByteArray}
    {depth : Nat}
    {header : EvmYul.BlockHeader}
    {perm : Bool}
    {err : EvmYul.EVM.ExecutionException}
    (hX :
      EvmYul.EVM.X fuel (Assembly.GasAware.validJumps target)
          (thetaCodeXInitialState target gasNat blobVersionedHashes
            createdAccounts genesisBlockHeader blocks accountMap sigma0
            chainContext substate source origin recipient gasPrice value
            weiValue calldata depth header perm) =
        .error err)
    (hErr : (err == EvmYul.EVM.ExecutionException.OutOfFuel) = true) :
    EvmYul.EVM.Θ fuel.succ.succ blobVersionedHashes createdAccounts
        genesisBlockHeader blocks accountMap sigma0 chainContext substate
        source origin recipient (.Code (Assembly.Bytecode.encodeTarget target))
        (EvmYul.UInt256.ofNat gasNat) gasPrice value weiValue calldata depth
        header perm =
      .error EvmYul.EVM.ExecutionException.OutOfFuel := by
  rw [Theta_code_succ_succ_eq_X_installedCode]
  simp [hX, hErr]

theorem Ccallgas_eq_of_dead_eq
    {τ υ : EvmYul.OperationType}
    {yulAccountMap : EvmYul.AccountMap τ}
    {evmAccountMap : EvmYul.AccountMap υ}
    {yulMachine evmMachine : EvmYul.MachineState}
    {yulSubstate evmSubstate : EvmYul.Substate}
    {target recipient : EvmYul.AccountAddress}
    {value gas : EvmYul.UInt256}
    (hGas : yulMachine.gasAvailable = evmMachine.gasAvailable)
    (hSubstate : yulSubstate = evmSubstate)
    (hDead :
      EvmYul.State.dead yulAccountMap recipient =
        EvmYul.State.dead evmAccountMap recipient) :
    EvmYul.EVM.Ccallgas target recipient value gas
        yulAccountMap yulMachine yulSubstate =
      EvmYul.EVM.Ccallgas target recipient value gas
        evmAccountMap evmMachine evmSubstate := by
  subst evmSubstate
  cases value
  simp [EvmYul.EVM.Ccallgas, EvmYul.EVM.Cgascap,
    EvmYul.EVM.Cextra, EvmYul.EVM.Cnew, hGas, hDead]

theorem CompiledAccountMapRel.dead_eq_of_missing
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    {addr : EvmYul.AccountAddress}
    (hMissing : yul.find? addr = none) :
    EvmYul.State.dead yul addr = EvmYul.State.dead evm addr := by
  have hEvmMissing := hWorld.not_find_evm_of_not_find_yul hMissing
  unfold EvmYul.State.dead
  rw [hMissing, hEvmMissing]
  rfl

theorem CompiledAccountMapRel.dead_eq
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    (addr : EvmYul.AccountAddress) :
    EvmYul.State.dead yul addr = EvmYul.State.dead evm addr := by
  unfold EvmYul.State.dead
  cases hYul : yul.find? addr with
  | none =>
      have hEvm := hWorld.not_find_evm_of_not_find_yul hYul
      rw [hEvm]
      rfl
  | some yulAccount =>
      rcases hWorld.find_yul hYul with
        ⟨evmAccount, hEvm, hAccount⟩
      rw [hEvm]
      exact hAccount.emptyAccount

theorem CompiledAccountMapRel.Ccallgas_eq
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    {yulMachine evmMachine : EvmYul.MachineState}
    {yulSubstate evmSubstate : EvmYul.Substate}
    {target recipient : EvmYul.AccountAddress}
    {value gas : EvmYul.UInt256}
    (hGas : yulMachine.gasAvailable = evmMachine.gasAvailable)
    (hSubstate : yulSubstate = evmSubstate) :
    EvmYul.EVM.Ccallgas target recipient value gas
        yul yulMachine yulSubstate =
      EvmYul.EVM.Ccallgas target recipient value gas
        evm evmMachine evmSubstate := by
  exact
    Ccallgas_eq_of_dead_eq hGas hSubstate
      (hWorld.dead_eq recipient)

theorem CompiledAccountMapRel.Ccallgas_eq_of_missing_recipient
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    {yulMachine evmMachine : EvmYul.MachineState}
    {yulSubstate evmSubstate : EvmYul.Substate}
    {target recipient : EvmYul.AccountAddress}
    {value gas : EvmYul.UInt256}
    (hGas : yulMachine.gasAvailable = evmMachine.gasAvailable)
    (hSubstate : yulSubstate = evmSubstate)
    (hMissing : yul.find? recipient = none) :
    EvmYul.EVM.Ccallgas target recipient value gas
        yul yulMachine yulSubstate =
      EvmYul.EVM.Ccallgas target recipient value gas
        evm evmMachine evmSubstate := by
  exact
    Ccallgas_eq_of_dead_eq hGas hSubstate
      (hWorld.dead_eq_of_missing hMissing)

theorem CompiledAccountMapRel.toExecute_precompiled
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    {addr : EvmYul.AccountAddress}
    {precompiled : EvmYul.PrecompiledContract}
    (hPrecompile :
      EvmYul.PrecompiledContract.ofAddress? addr = some precompiled) :
    CompiledToExecuteRel
      (EvmYul.toExecute .Yul yul addr)
      (EvmYul.toExecute .EVM evm addr) := by
  simp [EvmYul.toExecute, hPrecompile,
    CompiledToExecuteRel.precompiled]

theorem CompiledAccountMapRel.toExecute_code_of_find_yul
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    {addr : EvmYul.AccountAddress} {yulAccount : EvmYul.Account .Yul}
    (hNotPrecompile :
      EvmYul.PrecompiledContract.ofAddress? addr = none)
    (hFind : yul.find? addr = some yulAccount) :
    ∃ evmAccount,
      evm.find? addr = some evmAccount ∧
        CompiledToExecuteRel
          (EvmYul.ToExecute.Code yulAccount.code)
          (EvmYul.toExecute .EVM evm addr) := by
  rcases hWorld.find_yul hFind with
    ⟨evmAccount, hEvmFind, hAccount⟩
  refine ⟨evmAccount, hEvmFind, ?_⟩
  simp [EvmYul.toExecute, hNotPrecompile, hEvmFind]
  exact CompiledToExecuteRel.code hAccount.code

theorem CompiledAccountMapRel.toExecute
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    (addr : EvmYul.AccountAddress) :
    CompiledToExecuteRel
      (EvmYul.toExecute .Yul yul addr)
      (EvmYul.toExecute .EVM evm addr) := by
  cases hPrecompile : EvmYul.PrecompiledContract.ofAddress? addr with
  | some precompiled =>
      exact CompiledAccountMapRel.toExecute_precompiled hPrecompile
  | none =>
      simp [EvmYul.toExecute, hPrecompile]
      cases hYul : yul.find? addr with
      | none =>
          have hEvm := hWorld.not_find_evm_of_not_find_yul hYul
          simp [hEvm]
          exact CompiledToExecuteRel.code CompiledCodeRel.empty
      | some yulAccount =>
          rcases hWorld.find_yul hYul with
            ⟨evmAccount, hEvmFind, hAccount⟩
          simp [hEvmFind]
          exact CompiledToExecuteRel.code hAccount.code

structure CompiledPrecompileResultRel
    (yulRes :
      Bool × EvmYul.AccountMap .Yul × EvmYul.UInt256 ×
        EvmYul.Substate × ByteArray)
    (evmRes :
      Bool × EvmYul.AccountMap .EVM × EvmYul.UInt256 ×
        EvmYul.Substate × ByteArray) : Prop where
  success : yulRes.1 = evmRes.1
  accountMap : CompiledAccountMapRel yulRes.2.1 evmRes.2.1
  gas : yulRes.2.2.1 = evmRes.2.2.1
  substate : yulRes.2.2.2.1 = evmRes.2.2.2.1
  output : yulRes.2.2.2.2 = evmRes.2.2.2.2

theorem CompiledPrecompileResultRel.same
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    (success : Bool) (gas : EvmYul.UInt256)
    (substate : EvmYul.Substate) (output : ByteArray) :
    CompiledPrecompileResultRel
      (success, yul, gas, substate, output)
      (success, evm, gas, substate, output) :=
  ⟨rfl, hWorld, rfl, rfl, rfl⟩

theorem CompiledPrecompileResultRel.empty
    (success : Bool) (gas : EvmYul.UInt256)
    (substate : EvmYul.Substate) (output : ByteArray) :
    CompiledPrecompileResultRel
      (success, (∅ : EvmYul.AccountMap .Yul), gas, substate, output)
      (success, (∅ : EvmYul.AccountMap .EVM), gas, substate, output) :=
  ⟨rfl, CompiledAccountMapRel.empty, rfl, rfl, rfl⟩

theorem CompiledPrecompileResultRel.accountMap_merge
    {yulParent : EvmYul.AccountMap .Yul}
    {evmParent : EvmYul.AccountMap .EVM}
    {yulRes :
      Bool × EvmYul.AccountMap .Yul × EvmYul.UInt256 ×
        EvmYul.Substate × ByteArray}
    {evmRes :
      Bool × EvmYul.AccountMap .EVM × EvmYul.UInt256 ×
        EvmYul.Substate × ByteArray}
    (hParent : CompiledAccountMapRel yulParent evmParent)
    (hResult : CompiledPrecompileResultRel yulRes evmRes) :
    CompiledAccountMapRel
      (if yulRes.2.1.isEmpty then yulParent else yulRes.2.1)
      (if evmRes.2.1.isEmpty then evmParent else evmRes.2.1) := by
  exact
    CompiledAccountMapRel.if_empty_parent
      hParent hResult.accountMap hResult.accountMap.isEmpty_eq

theorem runPrecompiledContract_substate
    {τ : EvmYul.OperationType} (precompiled : EvmYul.PrecompiledContract)
    (accountMap : EvmYul.AccountMap τ) (gas : EvmYul.UInt256)
    (substate : EvmYul.Substate) (env : EvmYul.ExecutionEnv τ) :
    (runPrecompiledContract precompiled accountMap gas substate env).2.2.2.1 =
      substate := by
  cases precompiled
  · by_cases hGas : gas.toNat < 3000
    · simp [runPrecompiledContract, Ξ_ECREC, hGas]
    · simp [runPrecompiledContract, Ξ_ECREC, hGas]
  · by_cases hGas :
        gas.toNat < 60 + 12 * ((env.calldata.size + 31) / 32)
    · simp [runPrecompiledContract, Ξ_SHA256, hGas]
    · simp [runPrecompiledContract, Ξ_SHA256, hGas, dbgTrace]
  · by_cases hGas :
        gas.toNat < 600 + 120 * ((env.calldata.size + 31) / 32)
    · simp [runPrecompiledContract, Ξ_RIP160, hGas]
    · simp [runPrecompiledContract, Ξ_RIP160, hGas, dbgTrace]
  · by_cases hGas :
        gas.toNat < 15 + 3 * ((env.calldata.size + 31) / 32)
    · simp [runPrecompiledContract, Ξ_ID, hGas]
    · simp [runPrecompiledContract, Ξ_ID, hGas]
  · by_cases hGas : gas.toNat < Ξ_EXPMOD_gasCost env.calldata
    · simp [runPrecompiledContract, Ξ_EXPMOD, hGas]
    · simp [runPrecompiledContract, Ξ_EXPMOD, hGas]
  · by_cases hGas : gas.toNat < 150
    · simp [runPrecompiledContract, Ξ_BN_ADD, hGas]
    · simp [runPrecompiledContract, Ξ_BN_ADD, hGas]
      cases hBN : BN_ADD (env.calldata.readBytes 0 32)
          (env.calldata.readBytes 32 32)
          (env.calldata.readBytes 64 32)
          (env.calldata.readBytes 96 32) with
      | ok output => simp
      | error err => simp [dbgTrace]
  · by_cases hGas : gas.toNat < 6000
    · simp [runPrecompiledContract, Ξ_BN_MUL, hGas]
    · simp [runPrecompiledContract, Ξ_BN_MUL, hGas]
      cases hBN : BN_MUL (env.calldata.readBytes 0 32)
          (env.calldata.readBytes 32 32)
          (env.calldata.readBytes 64 32) with
      | ok output => simp
      | error err => simp [dbgTrace]
  · by_cases hGas :
        gas.toNat < 34000 * (env.calldata.size / 192) + 45000
    · simp [runPrecompiledContract, Ξ_SNARKV, hGas]
    · simp [runPrecompiledContract, Ξ_SNARKV, hGas]
      cases hSNARK : SNARKV env.calldata with
      | ok output => simp
      | error err => simp [dbgTrace]
  · by_cases hGas :
        gas.toNat <
          EvmYul.fromByteArrayBigEndian (env.calldata.extract 0 4)
    · simp [runPrecompiledContract, Ξ_BLAKE2_F, hGas, dbgTrace]
    · simp [runPrecompiledContract, Ξ_BLAKE2_F, hGas]
      cases hBLAKE : ffi.BLAKE2 env.calldata with
      | ok output => simp
      | error err => simp [dbgTrace]
  · by_cases hGas : gas.toNat < 50000
    · simp [runPrecompiledContract, Ξ_PointEval, hGas]
    · simp [runPrecompiledContract, Ξ_PointEval, hGas]
      cases hPoint : PointEval env.calldata with
      | ok output => simp
      | error err => simp [dbgTrace]

theorem runPrecompiledContract_failure_eq_empty
    {τ : EvmYul.OperationType} {precompiled : EvmYul.PrecompiledContract}
    {accountMap : EvmYul.AccountMap τ} {gas : EvmYul.UInt256}
    {substate : EvmYul.Substate} {env : EvmYul.ExecutionEnv τ}
    (hFailure :
      (runPrecompiledContract precompiled accountMap gas substate env).1 =
        false) :
    runPrecompiledContract precompiled accountMap gas substate env =
      (false, ∅, ⟨0⟩, substate, ByteArray.empty) := by
  cases precompiled
  · by_cases hGas : gas.toNat < 3000
    · simp [runPrecompiledContract, Ξ_ECREC, hGas]
    · simp [runPrecompiledContract, Ξ_ECREC, hGas] at hFailure
  · by_cases hGas :
        gas.toNat < 60 + 12 * ((env.calldata.size + 31) / 32)
    · simp [runPrecompiledContract, Ξ_SHA256, hGas]
    · simp [runPrecompiledContract, Ξ_SHA256, hGas, dbgTrace] at hFailure
  · by_cases hGas :
        gas.toNat < 600 + 120 * ((env.calldata.size + 31) / 32)
    · simp [runPrecompiledContract, Ξ_RIP160, hGas]
    · simp [runPrecompiledContract, Ξ_RIP160, hGas, dbgTrace] at hFailure
  · by_cases hGas :
        gas.toNat < 15 + 3 * ((env.calldata.size + 31) / 32)
    · simp [runPrecompiledContract, Ξ_ID, hGas]
    · simp [runPrecompiledContract, Ξ_ID, hGas] at hFailure
  · by_cases hGas : gas.toNat < Ξ_EXPMOD_gasCost env.calldata
    · simp [runPrecompiledContract, Ξ_EXPMOD, hGas]
    · simp [runPrecompiledContract, Ξ_EXPMOD, hGas] at hFailure
  · by_cases hGas : gas.toNat < 150
    · simp [runPrecompiledContract, Ξ_BN_ADD, hGas]
    · cases hBN : BN_ADD (env.calldata.readBytes 0 32)
          (env.calldata.readBytes 32 32)
          (env.calldata.readBytes 64 32)
          (env.calldata.readBytes 96 32) with
      | ok output =>
          simp [runPrecompiledContract, Ξ_BN_ADD, hGas, hBN] at hFailure
      | error err =>
          simp [runPrecompiledContract, Ξ_BN_ADD, hGas, hBN, dbgTrace]
  · by_cases hGas : gas.toNat < 6000
    · simp [runPrecompiledContract, Ξ_BN_MUL, hGas]
    · cases hBN : BN_MUL (env.calldata.readBytes 0 32)
          (env.calldata.readBytes 32 32)
          (env.calldata.readBytes 64 32) with
      | ok output =>
          simp [runPrecompiledContract, Ξ_BN_MUL, hGas, hBN] at hFailure
      | error err =>
          simp [runPrecompiledContract, Ξ_BN_MUL, hGas, hBN, dbgTrace]
  · by_cases hGas :
        gas.toNat < 34000 * (env.calldata.size / 192) + 45000
    · simp [runPrecompiledContract, Ξ_SNARKV, hGas]
    · cases hSNARK : SNARKV env.calldata with
      | ok output =>
          simp [runPrecompiledContract, Ξ_SNARKV, hGas, hSNARK] at hFailure
      | error err =>
          simp [runPrecompiledContract, Ξ_SNARKV, hGas, hSNARK, dbgTrace]
  · by_cases hGas :
        gas.toNat <
          EvmYul.fromByteArrayBigEndian (env.calldata.extract 0 4)
    · simp [runPrecompiledContract, Ξ_BLAKE2_F, hGas, dbgTrace]
    · cases hBLAKE : ffi.BLAKE2 env.calldata with
      | ok output =>
          simp [runPrecompiledContract, Ξ_BLAKE2_F, hGas, hBLAKE] at hFailure
      | error err =>
          simp [runPrecompiledContract, Ξ_BLAKE2_F, hGas, hBLAKE, dbgTrace]
  · by_cases hGas : gas.toNat < 50000
    · simp [runPrecompiledContract, Ξ_PointEval, hGas]
    · cases hPoint : PointEval env.calldata with
      | ok output =>
          simp [runPrecompiledContract, Ξ_PointEval, hGas, hPoint] at hFailure
      | error err =>
          simp [runPrecompiledContract, Ξ_PointEval, hGas, hPoint, dbgTrace]

theorem runPrecompiledContract_substate_merge_of_eq
    {precompiled : EvmYul.PrecompiledContract}
    {yulAccountMap : EvmYul.AccountMap .Yul}
    {evmAccountMap : EvmYul.AccountMap .EVM}
    {yulSubstate evmSubstate : EvmYul.Substate}
    {yulEnv : EvmYul.ExecutionEnv .Yul}
    {evmEnv : EvmYul.ExecutionEnv .EVM}
    (gas : EvmYul.UInt256)
    (hSubstate : yulSubstate = evmSubstate) :
    (runPrecompiledContract precompiled yulAccountMap gas
        yulSubstate yulEnv).2.2.2.1 =
      if (runPrecompiledContract precompiled evmAccountMap gas
          evmSubstate evmEnv).2.1.isEmpty then
        evmSubstate
      else
        (runPrecompiledContract precompiled evmAccountMap gas
          evmSubstate evmEnv).2.2.2.1 := by
  rw [runPrecompiledContract_substate]
  by_cases hEmpty :
      (runPrecompiledContract precompiled evmAccountMap gas
        evmSubstate evmEnv).2.1.isEmpty
  · simp [hEmpty, hSubstate]
  · rw [runPrecompiledContract_substate]
    simp [hEmpty, hSubstate]

theorem CompiledAccountMapRel.precompile_ecrec
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    {yI : EvmYul.ExecutionEnv .Yul} {eI : EvmYul.ExecutionEnv .EVM}
    (hCalldata : yI.calldata = eI.calldata)
    (gas : EvmYul.UInt256) (substate : EvmYul.Substate) :
    CompiledPrecompileResultRel
      (Ξ_ECREC yul gas substate yI)
      (Ξ_ECREC evm gas substate eI) := by
  by_cases hGas : gas.toNat < 3000
  · simp [Ξ_ECREC, hGas]
    exact CompiledPrecompileResultRel.empty false ⟨0⟩ substate .empty
  · simp [Ξ_ECREC, hGas, hCalldata]
    exact
      CompiledPrecompileResultRel.same hWorld true
        (gas - EvmYul.UInt256.ofNat 3000) substate _

theorem CompiledAccountMapRel.precompile_sha256
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    {yI : EvmYul.ExecutionEnv .Yul} {eI : EvmYul.ExecutionEnv .EVM}
    (hCalldata : yI.calldata = eI.calldata)
    (gas : EvmYul.UInt256) (substate : EvmYul.Substate) :
    CompiledPrecompileResultRel
      (Ξ_SHA256 yul gas substate yI)
      (Ξ_SHA256 evm gas substate eI) := by
  by_cases hGas : gas.toNat < 60 + 12 * ((eI.calldata.size + 31) / 32)
  · simp [Ξ_SHA256, hGas, hCalldata]
    exact CompiledPrecompileResultRel.empty false ⟨0⟩ substate .empty
  · simp [Ξ_SHA256, hGas, hCalldata]
    exact
      CompiledPrecompileResultRel.same hWorld true
        (gas -
          EvmYul.UInt256.ofNat (60 + 12 * ((eI.calldata.size + 31) / 32)))
        substate _

theorem CompiledAccountMapRel.precompile_rip160
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    {yI : EvmYul.ExecutionEnv .Yul} {eI : EvmYul.ExecutionEnv .EVM}
    (hCalldata : yI.calldata = eI.calldata)
    (gas : EvmYul.UInt256) (substate : EvmYul.Substate) :
    CompiledPrecompileResultRel
      (Ξ_RIP160 yul gas substate yI)
      (Ξ_RIP160 evm gas substate eI) := by
  by_cases hGas : gas.toNat < 600 + 120 * ((eI.calldata.size + 31) / 32)
  · simp [Ξ_RIP160, hGas, hCalldata]
    exact CompiledPrecompileResultRel.empty false ⟨0⟩ substate .empty
  · simp [Ξ_RIP160, hGas, hCalldata]
    exact
      CompiledPrecompileResultRel.same hWorld true
        (gas -
          EvmYul.UInt256.ofNat
            (600 + 120 * ((eI.calldata.size + 31) / 32)))
        substate _

theorem CompiledAccountMapRel.precompile_id
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    {yI : EvmYul.ExecutionEnv .Yul} {eI : EvmYul.ExecutionEnv .EVM}
    (hCalldata : yI.calldata = eI.calldata)
    (gas : EvmYul.UInt256) (substate : EvmYul.Substate) :
    CompiledPrecompileResultRel
      (Ξ_ID yul gas substate yI)
      (Ξ_ID evm gas substate eI) := by
  by_cases hGas : gas.toNat < 15 + 3 * ((eI.calldata.size + 31) / 32)
  · simp [Ξ_ID, hGas, hCalldata]
    exact CompiledPrecompileResultRel.empty false ⟨0⟩ substate .empty
  · simp [Ξ_ID, hGas, hCalldata]
    exact
      CompiledPrecompileResultRel.same hWorld true
        (gas -
          EvmYul.UInt256.ofNat (15 + 3 * ((eI.calldata.size + 31) / 32)))
        substate eI.calldata

theorem CompiledAccountMapRel.precompile_expmod
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    {yI : EvmYul.ExecutionEnv .Yul} {eI : EvmYul.ExecutionEnv .EVM}
    (hCalldata : yI.calldata = eI.calldata)
    (gas : EvmYul.UInt256) (substate : EvmYul.Substate) :
    CompiledPrecompileResultRel
      (Ξ_EXPMOD yul gas substate yI)
      (Ξ_EXPMOD evm gas substate eI) := by
  by_cases hGas : gas.toNat < Ξ_EXPMOD_gasCost eI.calldata
  · simp [Ξ_EXPMOD, hGas, hCalldata]
    exact CompiledPrecompileResultRel.empty false ⟨0⟩ substate .empty
  · simp [Ξ_EXPMOD, hGas, hCalldata]
    exact
      CompiledPrecompileResultRel.same hWorld true
        (gas -
          EvmYul.UInt256.ofNat (Ξ_EXPMOD_gasCost eI.calldata))
        substate (Ξ_EXPMOD_output eI.calldata)

theorem CompiledAccountMapRel.precompile_bn_add
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    {yI : EvmYul.ExecutionEnv .Yul} {eI : EvmYul.ExecutionEnv .EVM}
    (hCalldata : yI.calldata = eI.calldata)
    (gas : EvmYul.UInt256) (substate : EvmYul.Substate) :
    CompiledPrecompileResultRel
      (Ξ_BN_ADD yul gas substate yI)
      (Ξ_BN_ADD evm gas substate eI) := by
  by_cases hGas : gas.toNat < 150
  · simp [Ξ_BN_ADD, hGas]
    exact CompiledPrecompileResultRel.empty false ⟨0⟩ substate .empty
  · simp [Ξ_BN_ADD, hGas, hCalldata]
    split
    · exact
        CompiledPrecompileResultRel.same hWorld true
          (gas - EvmYul.UInt256.ofNat 150) substate _
    · exact CompiledPrecompileResultRel.empty false ⟨0⟩ substate .empty

theorem CompiledAccountMapRel.precompile_bn_mul
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    {yI : EvmYul.ExecutionEnv .Yul} {eI : EvmYul.ExecutionEnv .EVM}
    (hCalldata : yI.calldata = eI.calldata)
    (gas : EvmYul.UInt256) (substate : EvmYul.Substate) :
    CompiledPrecompileResultRel
      (Ξ_BN_MUL yul gas substate yI)
      (Ξ_BN_MUL evm gas substate eI) := by
  by_cases hGas : gas.toNat < 6000
  · simp [Ξ_BN_MUL, hGas]
    exact CompiledPrecompileResultRel.empty false ⟨0⟩ substate .empty
  · simp [Ξ_BN_MUL, hGas, hCalldata]
    split
    · exact
        CompiledPrecompileResultRel.same hWorld true
          (gas - EvmYul.UInt256.ofNat 6000) substate _
    · exact CompiledPrecompileResultRel.empty false ⟨0⟩ substate .empty

theorem CompiledAccountMapRel.precompile_snarkv
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    {yI : EvmYul.ExecutionEnv .Yul} {eI : EvmYul.ExecutionEnv .EVM}
    (hCalldata : yI.calldata = eI.calldata)
    (gas : EvmYul.UInt256) (substate : EvmYul.Substate) :
    CompiledPrecompileResultRel
      (Ξ_SNARKV yul gas substate yI)
      (Ξ_SNARKV evm gas substate eI) := by
  by_cases hGas : gas.toNat < 34000 * (eI.calldata.size / 192) + 45000
  · simp [Ξ_SNARKV, hGas, hCalldata]
    exact CompiledPrecompileResultRel.empty false ⟨0⟩ substate .empty
  · simp [Ξ_SNARKV, hGas, hCalldata]
    split
    · exact
        CompiledPrecompileResultRel.same hWorld true
          (gas -
            EvmYul.UInt256.ofNat
              (34000 * (eI.calldata.size / 192) + 45000))
          substate _
    · exact CompiledPrecompileResultRel.empty false ⟨0⟩ substate .empty

theorem CompiledAccountMapRel.precompile_blake2_f
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    {yI : EvmYul.ExecutionEnv .Yul} {eI : EvmYul.ExecutionEnv .EVM}
    (hCalldata : yI.calldata = eI.calldata)
    (gas : EvmYul.UInt256) (substate : EvmYul.Substate) :
    CompiledPrecompileResultRel
      (Ξ_BLAKE2_F yul gas substate yI)
      (Ξ_BLAKE2_F evm gas substate eI) := by
  by_cases hGas :
      gas.toNat < EvmYul.fromByteArrayBigEndian (eI.calldata.extract 0 4)
  · simp [Ξ_BLAKE2_F, hGas, hCalldata]
    exact CompiledPrecompileResultRel.empty false ⟨0⟩ substate .empty
  · simp [Ξ_BLAKE2_F, hGas, hCalldata]
    split
    · exact
        CompiledPrecompileResultRel.same hWorld true
          (gas -
            EvmYul.UInt256.ofNat
              (EvmYul.fromByteArrayBigEndian (eI.calldata.extract 0 4)))
          substate _
    · exact CompiledPrecompileResultRel.empty false ⟨0⟩ substate .empty

theorem CompiledAccountMapRel.precompile_point_eval
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    {yI : EvmYul.ExecutionEnv .Yul} {eI : EvmYul.ExecutionEnv .EVM}
    (hCalldata : yI.calldata = eI.calldata)
    (gas : EvmYul.UInt256) (substate : EvmYul.Substate) :
    CompiledPrecompileResultRel
      (Ξ_PointEval yul gas substate yI)
      (Ξ_PointEval evm gas substate eI) := by
  by_cases hGas : gas.toNat < 50000
  · simp [Ξ_PointEval, hGas]
    exact CompiledPrecompileResultRel.empty false ⟨0⟩ substate .empty
  · simp [Ξ_PointEval, hGas, hCalldata]
    split
    · exact
        CompiledPrecompileResultRel.same hWorld true
          (gas - EvmYul.UInt256.ofNat 50000) substate _
    · exact CompiledPrecompileResultRel.empty false ⟨0⟩ substate .empty

theorem CompiledAccountMapRel.runPrecompiledContract_preserve_of_calldata
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    {yI : EvmYul.ExecutionEnv .Yul} {eI : EvmYul.ExecutionEnv .EVM}
    (hCalldata : yI.calldata = eI.calldata)
    (precompiled : EvmYul.PrecompiledContract)
    (gas : EvmYul.UInt256) (substate : EvmYul.Substate) :
    CompiledPrecompileResultRel
      (runPrecompiledContract precompiled yul gas substate yI)
      (runPrecompiledContract precompiled evm gas substate eI) := by
  cases precompiled
  · exact hWorld.precompile_ecrec hCalldata gas substate
  · exact hWorld.precompile_sha256 hCalldata gas substate
  · exact hWorld.precompile_rip160 hCalldata gas substate
  · exact hWorld.precompile_id hCalldata gas substate
  · exact hWorld.precompile_expmod hCalldata gas substate
  · exact hWorld.precompile_bn_add hCalldata gas substate
  · exact hWorld.precompile_bn_mul hCalldata gas substate
  · exact hWorld.precompile_snarkv hCalldata gas substate
  · exact hWorld.precompile_blake2_f hCalldata gas substate
  · exact hWorld.precompile_point_eval hCalldata gas substate

theorem CompiledAccountMapRel.runPrecompiledContract_preserve
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    {cfg : Reference.StateRelConfig}
    {yI : EvmYul.ExecutionEnv .Yul} {eI : EvmYul.ExecutionEnv .EVM}
    (hEnv : Reference.ExecutionEnvRel cfg yI eI)
    (precompiled : EvmYul.PrecompiledContract)
    (gas : EvmYul.UInt256) (substate : EvmYul.Substate) :
    CompiledPrecompileResultRel
      (runPrecompiledContract precompiled yul gas substate yI)
      (runPrecompiledContract precompiled evm gas substate eI) :=
  hWorld.runPrecompiledContract_preserve_of_calldata
    hEnv.calldata precompiled gas substate

theorem CompiledAccountMapRel.runPrecompiledContract_accountMap_merge
    {yulParent : EvmYul.AccountMap .Yul}
    {evmParent : EvmYul.AccountMap .EVM}
    {yulCallMap : EvmYul.AccountMap .Yul}
    {evmCallMap : EvmYul.AccountMap .EVM}
    (hParent : CompiledAccountMapRel yulParent evmParent)
    (hCallMap : CompiledAccountMapRel yulCallMap evmCallMap)
    {cfg : Reference.StateRelConfig}
    {yulEnv : EvmYul.ExecutionEnv .Yul}
    {evmEnv : EvmYul.ExecutionEnv .EVM}
    (hEnv : Reference.ExecutionEnvRel cfg yulEnv evmEnv)
    (precompiled : EvmYul.PrecompiledContract)
    (gas : EvmYul.UInt256) (substate : EvmYul.Substate) :
    CompiledAccountMapRel
      (if (runPrecompiledContract precompiled yulCallMap gas
          substate yulEnv).2.1.isEmpty then
        yulParent
      else
        (runPrecompiledContract precompiled yulCallMap gas
          substate yulEnv).2.1)
      (if (runPrecompiledContract precompiled evmCallMap gas
          substate evmEnv).2.1.isEmpty then
        evmParent
      else
        (runPrecompiledContract precompiled evmCallMap gas
          substate evmEnv).2.1) := by
  exact
    CompiledPrecompileResultRel.accountMap_merge hParent
      (hCallMap.runPrecompiledContract_preserve hEnv precompiled gas substate)

theorem buildPrecompiledContractCallState_success_of_evm_run_rel
    {cfg : Reference.StateRelConfig}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.SharedState .EVM}
    (hShared : Reference.SharedStateRel cfg yul evm)
    (hParentWorld : CompiledAccountMapRel yul.accountMap evm.accountMap)
    (hCfgAccountMap :
      ∀ {yulMap : EvmYul.AccountMap .Yul}
        {evmMap : EvmYul.AccountMap .EVM},
        CompiledAccountMapRel yulMap evmMap →
          cfg.accountMapRel yulMap evmMap)
    (store : EvmYul.Yul.VarStore)
    {yulCallMap : EvmYul.AccountMap .Yul}
    {evmCallMap : EvmYul.AccountMap .EVM}
    (hCallMap : CompiledAccountMapRel yulCallMap evmCallMap)
    {yulEnv : EvmYul.ExecutionEnv .Yul}
    {evmEnv : EvmYul.ExecutionEnv .EVM}
    (hCalldata : yulEnv.calldata = evmEnv.calldata)
    (precompiled : EvmYul.PrecompiledContract)
    (gas : EvmYul.UInt256)
    (inOffset inSize outOffset outSize : EvmYul.UInt256)
    {targetGas : EvmYul.UInt256}
    (hSuccess :
      (runPrecompiledContract precompiled evmCallMap gas
        evm.substate evmEnv).1 = true)
    (hGas :
      cfg.gasAvailableRel
        (yul.toMachineState.finishExternalCall
          (runPrecompiledContract precompiled evmCallMap gas
            evm.substate evmEnv).2.2.2.2
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    ∃ yulAfter,
      EvmYul.Yul.buildPrecompiledContractCallState
          (.Ok yul store) yulCallMap precompiled gas yulEnv
          inOffset inSize outOffset outSize =
        .ok (.Ok yulAfter store, [⟨1⟩]) ∧
      Reference.SharedStateRel cfg yulAfter
        { evm with
          toMachineState :=
            { evm.toMachineState.finishExternalCall
                (runPrecompiledContract precompiled evmCallMap gas
                  evm.substate evmEnv).2.2.2.2
                inOffset inSize outOffset outSize with
              gasAvailable := targetGas }
          accountMap :=
            if (runPrecompiledContract precompiled evmCallMap gas
                evm.substate evmEnv).2.1.isEmpty then
              evm.accountMap
            else
              (runPrecompiledContract precompiled evmCallMap gas
                evm.substate evmEnv).2.1
          substate :=
            if (runPrecompiledContract precompiled evmCallMap gas
                evm.substate evmEnv).2.1.isEmpty then
              evm.substate
            else
              (runPrecompiledContract precompiled evmCallMap gas
                evm.substate evmEnv).2.2.2.1 } := by
  have hParentSubstate : yul.substate = evm.substate := by
    rcases hShared with ⟨hChain, _hMachine⟩
    exact hChain.substate
  have hResult :
      CompiledPrecompileResultRel
        (runPrecompiledContract precompiled yulCallMap gas
          yul.substate yulEnv)
        (runPrecompiledContract precompiled evmCallMap gas
          evm.substate evmEnv) := by
    simpa [hParentSubstate] using
      hCallMap.runPrecompiledContract_preserve_of_calldata
        hCalldata precompiled gas yul.substate
  have hYulSuccess :
      (runPrecompiledContract precompiled yulCallMap gas
        yul.substate yulEnv).1 = true :=
    hResult.success.trans hSuccess
  have hYulRun :
      runPrecompiledContract precompiled yulCallMap gas
          yul.substate yulEnv =
        (true,
          (runPrecompiledContract precompiled yulCallMap gas
            yul.substate yulEnv).2.1,
          (runPrecompiledContract precompiled yulCallMap gas
            yul.substate yulEnv).2.2.1,
          (runPrecompiledContract precompiled yulCallMap gas
            yul.substate yulEnv).2.2.2.1,
          (runPrecompiledContract precompiled yulCallMap gas
            yul.substate yulEnv).2.2.2.2) := by
    simpa [hYulSuccess] using
      (show
        runPrecompiledContract precompiled yulCallMap gas
            yul.substate yulEnv =
          ((runPrecompiledContract precompiled yulCallMap gas
              yul.substate yulEnv).1,
            (runPrecompiledContract precompiled yulCallMap gas
              yul.substate yulEnv).2.1,
            (runPrecompiledContract precompiled yulCallMap gas
              yul.substate yulEnv).2.2.1,
            (runPrecompiledContract precompiled yulCallMap gas
              yul.substate yulEnv).2.2.2.1,
            (runPrecompiledContract precompiled yulCallMap gas
              yul.substate yulEnv).2.2.2.2) from rfl)
  have hAccountMap :
      cfg.accountMapRel
        (if (runPrecompiledContract precompiled yulCallMap gas
            yul.substate yulEnv).2.1.isEmpty then
          yul.accountMap
        else
          (runPrecompiledContract precompiled yulCallMap gas
            yul.substate yulEnv).2.1)
        (if (runPrecompiledContract precompiled evmCallMap gas
            evm.substate evmEnv).2.1.isEmpty then
          evm.accountMap
        else
          (runPrecompiledContract precompiled evmCallMap gas
            evm.substate evmEnv).2.1) :=
    hCfgAccountMap <| by
      exact
        CompiledPrecompileResultRel.accountMap_merge
          hParentWorld hResult
  have hSubstate :
      (runPrecompiledContract precompiled yulCallMap gas
          yul.substate yulEnv).2.2.2.1 =
        if (runPrecompiledContract precompiled evmCallMap gas
            evm.substate evmEnv).2.1.isEmpty then
          evm.substate
        else
          (runPrecompiledContract precompiled evmCallMap gas
            evm.substate evmEnv).2.2.2.1 := by
    simpa [hParentSubstate] using
      (runPrecompiledContract_substate_merge_of_eq
        (precompiled := precompiled)
        (yulAccountMap := yulCallMap)
        (evmAccountMap := evmCallMap)
        (yulSubstate := yul.substate)
        (evmSubstate := evm.substate)
        (yulEnv := yulEnv)
        (evmEnv := evmEnv)
        gas hParentSubstate)
  have hOutput :
      (runPrecompiledContract precompiled yulCallMap gas
          yul.substate yulEnv).2.2.2.2 =
        (runPrecompiledContract precompiled evmCallMap gas
          evm.substate evmEnv).2.2.2.2 :=
    hResult.output
  have hGasYul :
      cfg.gasAvailableRel
        (yul.toMachineState.finishExternalCall
          (runPrecompiledContract precompiled yulCallMap gas
            yul.substate yulEnv).2.2.2.2
          inOffset inSize outOffset outSize).gasAvailable
        targetGas := by
    simpa [hOutput] using hGas
  rcases
    buildPrecompiledContractCallState_success_rel
      hShared store
      (precompiled := precompiled)
      (gas := gas)
      (yulEnv := yulEnv)
      (returnData :=
        (runPrecompiledContract precompiled yulCallMap gas
          yul.substate yulEnv).2.2.2.2)
      (inOffset := inOffset)
      (inSize := inSize)
      (outOffset := outOffset)
      (outSize := outSize)
      hYulRun hAccountMap hSubstate hGasYul with
    ⟨yulAfter, hBuild, hRel⟩
  refine ⟨yulAfter, hBuild, ?_⟩
  simpa [hOutput] using hRel

theorem buildPrecompiledContractCallState_failure_of_evm_run_rel
    {cfg : Reference.StateRelConfig}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.SharedState .EVM}
    (hShared : Reference.SharedStateRel cfg yul evm)
    (store : EvmYul.Yul.VarStore)
    {yulCallMap : EvmYul.AccountMap .Yul}
    {evmCallMap : EvmYul.AccountMap .EVM}
    (hCallMap : CompiledAccountMapRel yulCallMap evmCallMap)
    {yulEnv : EvmYul.ExecutionEnv .Yul}
    {evmEnv : EvmYul.ExecutionEnv .EVM}
    (hCalldata : yulEnv.calldata = evmEnv.calldata)
    (precompiled : EvmYul.PrecompiledContract)
    (gas : EvmYul.UInt256)
    (inOffset inSize outOffset outSize : EvmYul.UInt256)
    {targetGas : EvmYul.UInt256}
    (hFailure :
      (runPrecompiledContract precompiled evmCallMap gas
        evm.substate evmEnv).1 = false)
    (hGas :
      cfg.gasAvailableRel
        (yul.toMachineState.finishExternalCall ByteArray.empty
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    ∃ yulAfter,
      EvmYul.Yul.buildPrecompiledContractCallState
          (.Ok yul store) yulCallMap precompiled gas yulEnv
          inOffset inSize outOffset outSize =
        .ok (.Ok yulAfter store, [⟨0⟩]) ∧
      Reference.SharedStateRel cfg yulAfter
        { evm with
          toMachineState :=
            { evm.toMachineState.finishExternalCall ByteArray.empty
                inOffset inSize outOffset outSize with
              gasAvailable := targetGas } } := by
  have hParentSubstate : yul.substate = evm.substate := by
    rcases hShared with ⟨hChain, _hMachine⟩
    exact hChain.substate
  have hResult :
      CompiledPrecompileResultRel
        (runPrecompiledContract precompiled yulCallMap gas
          yul.substate yulEnv)
        (runPrecompiledContract precompiled evmCallMap gas
          evm.substate evmEnv) := by
    simpa [hParentSubstate] using
      hCallMap.runPrecompiledContract_preserve_of_calldata
        hCalldata precompiled gas yul.substate
  have hYulFailure :
      (runPrecompiledContract precompiled yulCallMap gas
        yul.substate yulEnv).1 = false :=
    hResult.success.trans hFailure
  have hYulRun :
      runPrecompiledContract precompiled yulCallMap gas
          yul.substate yulEnv =
        (false,
          (runPrecompiledContract precompiled yulCallMap gas
            yul.substate yulEnv).2.1,
          (runPrecompiledContract precompiled yulCallMap gas
            yul.substate yulEnv).2.2.1,
          (runPrecompiledContract precompiled yulCallMap gas
            yul.substate yulEnv).2.2.2.1,
          (runPrecompiledContract precompiled yulCallMap gas
            yul.substate yulEnv).2.2.2.2) := by
    simpa [hYulFailure] using
      (show
        runPrecompiledContract precompiled yulCallMap gas
            yul.substate yulEnv =
          ((runPrecompiledContract precompiled yulCallMap gas
              yul.substate yulEnv).1,
            (runPrecompiledContract precompiled yulCallMap gas
              yul.substate yulEnv).2.1,
            (runPrecompiledContract precompiled yulCallMap gas
              yul.substate yulEnv).2.2.1,
            (runPrecompiledContract precompiled yulCallMap gas
              yul.substate yulEnv).2.2.2.1,
            (runPrecompiledContract precompiled yulCallMap gas
              yul.substate yulEnv).2.2.2.2) from rfl)
  exact
    buildPrecompiledContractCallState_failure_rel
      hShared store
      (precompiled := precompiled)
      (gas := gas)
      (yulEnv := yulEnv)
      (returnData :=
        (runPrecompiledContract precompiled yulCallMap gas
          yul.substate yulEnv).2.2.2.2)
      (inOffset := inOffset)
      (inSize := inSize)
      (outOffset := outOffset)
      (outSize := outSize)
      hYulRun hGas

theorem call_precompiled_success_rel
    {cfg : Reference.StateRelConfig}
    {fuel gasCost : Nat}
    {blobVersionedHashes : List ByteArray}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.EVM.State}
    (hShared : Reference.SharedStateRel cfg yul evm.toSharedState)
    (hParentWorld : CompiledAccountMapRel yul.accountMap evm.accountMap)
    (hCfgAccountMap :
      ∀ {yulMap : EvmYul.AccountMap .Yul}
        {evmMap : EvmYul.AccountMap .EVM},
        CompiledAccountMapRel yulMap evmMap →
          cfg.accountMapRel yulMap evmMap)
    (store : EvmYul.Yul.VarStore)
    {gas address value inOffset inSize outOffset outSize : EvmYul.UInt256}
    {precompiled : EvmYul.PrecompiledContract}
    (hEnough :
      value ≤
        (evm.accountMap.find? evm.executionEnv.codeOwner |>.option ⟨0⟩
          (·.balance)))
    (hDepth : evm.executionEnv.depth < 1024)
    (hPrecompile :
      EvmYul.PrecompiledContract.ofAddress?
        (EvmYul.AccountAddress.ofUInt256 address) = some precompiled)
    (hSuccess :
      let target := EvmYul.AccountAddress.ofUInt256 address
      let callMap :=
        evmCallTransfer evm.accountMap evm.executionEnv.codeOwner target value
      let callGas :=
        EvmYul.EVM.Ccallgas target target value gas evm.accountMap
          evm.toMachineState evm.substate
      let accessedSubstate :=
        (EvmYul.State.addAccessedAccount evm.toState target).substate
      let childEnv :=
        EvmYul.EVM.thetaCallExecutionEnv blobVersionedHashes
          evm.executionEnv.codeOwner evm.executionEnv.sender target
          (.Precompiled precompiled)
          (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice)
          value
          (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
          (evm.executionEnv.depth + 1) evm.executionEnv.header
          evm.executionEnv.perm
      (runPrecompiledContract precompiled callMap
        (EvmYul.UInt256.ofNat callGas) accessedSubstate childEnv).1 =
        true)
    (hGas :
      let target := EvmYul.AccountAddress.ofUInt256 address
      let callMap :=
        evmCallTransfer evm.accountMap evm.executionEnv.codeOwner target value
      let callGas :=
        EvmYul.EVM.Ccallgas target target value gas evm.accountMap
          evm.toMachineState evm.substate
      let charged : EvmYul.EVM.State :=
        { evm with
          gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
      let accessedSubstate :=
        (EvmYul.State.addAccessedAccount charged.toState target).substate
      let childEnv :=
        EvmYul.EVM.thetaCallExecutionEnv blobVersionedHashes
          evm.executionEnv.codeOwner evm.executionEnv.sender target
          (.Precompiled precompiled)
          (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice)
          value
          (charged.memory.readWithPadding inOffset.toNat inSize.toNat)
          (evm.executionEnv.depth + 1) evm.executionEnv.header
          evm.executionEnv.perm
      let precompileResult :=
        runPrecompiledContract precompiled callMap
          (EvmYul.UInt256.ofNat callGas) accessedSubstate childEnv
      let targetGas :=
        (charged.toMachineState.finishExternalCall precompileResult.2.2.2.2
          inOffset inSize outOffset outSize).gasAvailable +
          precompileResult.2.2.1
      cfg.gasAvailableRel
        (yul.toMachineState.finishExternalCall
          precompileResult.2.2.2.2 inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    let target := EvmYul.AccountAddress.ofUInt256 address
    let callMap :=
      evmCallTransfer evm.accountMap evm.executionEnv.codeOwner target value
    let callGas :=
      EvmYul.EVM.Ccallgas target target value gas evm.accountMap
        evm.toMachineState evm.substate
    let charged : EvmYul.EVM.State :=
      { evm with gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
    let accessedSubstate :=
      (EvmYul.State.addAccessedAccount charged.toState target).substate
    let yulEnv : EvmYul.ExecutionEnv .Yul :=
      { yul.executionEnv with
        calldata :=
          yul.toMachineState.memory.readWithPadding
            inOffset.toNat inSize.toNat
        code := default
        codeOwner := target
        source := yul.executionEnv.codeOwner
        weiValue := value
        depth := yul.executionEnv.depth + 1 }
    let evmEnv :=
      EvmYul.EVM.thetaCallExecutionEnv blobVersionedHashes
        evm.executionEnv.codeOwner evm.executionEnv.sender target
        (.Precompiled precompiled)
        (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice)
        value
        (charged.memory.readWithPadding inOffset.toNat inSize.toNat)
        (evm.executionEnv.depth + 1) evm.executionEnv.header
        evm.executionEnv.perm
    let precompileResult :=
      runPrecompiledContract precompiled callMap
        (EvmYul.UInt256.ofNat callGas) accessedSubstate evmEnv
    let targetGas :=
      (charged.toMachineState.finishExternalCall precompileResult.2.2.2.2
        inOffset inSize outOffset outSize).gasAvailable +
        precompileResult.2.2.1
    let evmAfter : EvmYul.EVM.State :=
      { charged with
        toMachineState :=
          { charged.toMachineState.finishExternalCall
              precompileResult.2.2.2.2 inOffset inSize outOffset outSize with
            gasAvailable := targetGas }
        accountMap :=
          if precompileResult.2.1.isEmpty then evm.accountMap
          else precompileResult.2.1
        substate :=
          if precompileResult.2.1.isEmpty then accessedSubstate
          else precompileResult.2.2.2.1 }
    EvmYul.EVM.call fuel.succ.succ gasCost blobVersionedHashes gas
        (EvmYul.UInt256.ofNat evm.executionEnv.codeOwner) address address
        value value inOffset inSize outOffset outSize evm.executionEnv.perm
        evm =
      .ok (⟨1⟩, evmAfter) ∧
      ∃ yulCallMap,
        EvmYul.Yul.callTransferAccountMap? yul.accountMap
            yul.executionEnv.codeOwner target value =
          some yulCallMap ∧
        CompiledAccountMapRel yulCallMap callMap ∧
        EvmYul.PrecompiledContract.ofAddress? target = some precompiled ∧
        ∃ yulAfter,
          EvmYul.Yul.buildPrecompiledContractCallState
              (EvmYul.Yul.addAccessedAccount (.Ok yul store) target)
              yulCallMap precompiled (EvmYul.UInt256.ofNat callGas)
              yulEnv inOffset inSize outOffset outSize =
            .ok (.Ok yulAfter store, [⟨1⟩]) ∧
          Reference.SharedStateRel cfg yulAfter evmAfter.toSharedState := by
  constructor
  · exact
      EVM_call_precompiled_success_eq hEnough hDepth hPrecompile hSuccess
  · dsimp
    let target := EvmYul.AccountAddress.ofUInt256 address
    let callMap :=
      evmCallTransfer evm.accountMap evm.executionEnv.codeOwner target value
    let callGas :=
      EvmYul.EVM.Ccallgas target target value gas evm.accountMap
        evm.toMachineState evm.substate
    let charged : EvmYul.EVM.State :=
      { evm with
        gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
    let yulAccessed : EvmYul.SharedState .Yul :=
      { yul with
        toState := EvmYul.State.addAccessedAccount yul.toState target }
    let evmAccessed : EvmYul.SharedState .EVM :=
      { evm.toSharedState with
        toState := EvmYul.State.addAccessedAccount evm.toState target }
    let yulEnv : EvmYul.ExecutionEnv .Yul :=
      { yul.executionEnv with
        calldata :=
          yul.toMachineState.memory.readWithPadding
            inOffset.toNat inSize.toNat
        code := default
        codeOwner := target
        source := yul.executionEnv.codeOwner
        weiValue := value
        depth := yul.executionEnv.depth + 1 }
    let evmEnv :=
      EvmYul.EVM.thetaCallExecutionEnv blobVersionedHashes
        evm.executionEnv.codeOwner evm.executionEnv.sender target
        (.Precompiled precompiled)
        (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice)
        value
        (charged.memory.readWithPadding inOffset.toNat inSize.toNat)
        (evm.executionEnv.depth + 1) evm.executionEnv.header
        evm.executionEnv.perm
    have hOwner :
        yul.executionEnv.codeOwner = evm.executionEnv.codeOwner := by
      rcases hShared with ⟨hChain, _hMachine⟩
      simpa using hChain.executionEnv.codeOwner
    rcases
        hParentWorld.callTransferAccountMap?_of_evm_enough
          (source := yul.executionEnv.codeOwner)
          (recipient := target)
          (value := value)
          (by simpa [hOwner] using hEnough) with
      ⟨yulCallMap, hTransfer, hCallMapRel⟩
    have hSharedAccessed :
        Reference.SharedStateRel cfg yulAccessed evmAccessed := by
      simpa [yulAccessed, evmAccessed, charged, target] using
        sharedStateRel_addAccessedAccount hShared target
    have hCalldata : yulEnv.calldata = evmEnv.calldata := by
      rcases hShared with ⟨_hChain, hMachine⟩
      simpa [yulEnv, evmEnv, EvmYul.EVM.thetaCallExecutionEnv, charged] using
        congrArg
          (fun memory =>
            memory.readWithPadding inOffset.toNat inSize.toNat)
          hMachine.memory
    have hSuccess' :
        (runPrecompiledContract precompiled callMap
          (EvmYul.UInt256.ofNat callGas) evmAccessed.substate evmEnv).1 =
          true := by
      simpa [target, callMap, callGas, charged, evmAccessed, evmEnv] using
        hSuccess
    have hGas' :
        cfg.gasAvailableRel
          (yulAccessed.toMachineState.finishExternalCall
            (runPrecompiledContract precompiled callMap
              (EvmYul.UInt256.ofNat callGas)
              evmAccessed.substate evmEnv).2.2.2.2
            inOffset inSize outOffset outSize).gasAvailable
          ((charged.toMachineState.finishExternalCall
              (runPrecompiledContract precompiled callMap
                (EvmYul.UInt256.ofNat callGas)
                evmAccessed.substate evmEnv).2.2.2.2
              inOffset inSize outOffset outSize).gasAvailable +
            (runPrecompiledContract precompiled callMap
              (EvmYul.UInt256.ofNat callGas)
              evmAccessed.substate evmEnv).2.2.1) := by
      simpa [target, callMap, callGas, charged, evmAccessed, evmEnv,
        yulAccessed] using hGas
    rcases
        buildPrecompiledContractCallState_success_of_evm_run_rel
          hSharedAccessed hParentWorld hCfgAccountMap store
          (hCallMap := by simpa [callMap, hOwner] using hCallMapRel)
          (hCalldata := hCalldata)
          (precompiled := precompiled)
          (gas := EvmYul.UInt256.ofNat callGas)
          (inOffset := inOffset)
          (inSize := inSize)
          (outOffset := outOffset)
          (outSize := outSize)
          hSuccess' hGas' with
      ⟨yulAfter, hBuild, hRel⟩
    refine ⟨yulCallMap, hTransfer, ?_, hPrecompile, yulAfter, ?_, ?_⟩
    · simpa [callMap, hOwner] using hCallMapRel
    · simpa [yulAccessed, yulEnv, target,
        EvmYul.Yul.addAccessedAccount, EvmYul.Yul.State.setState,
        EvmYul.Yul.State.toState] using hBuild
    · simpa [target, callMap, callGas, charged, evmAccessed, evmEnv] using hRel

theorem call_precompiled_failure_rel
    {cfg : Reference.StateRelConfig}
    {fuel gasCost : Nat}
    {blobVersionedHashes : List ByteArray}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.EVM.State}
    (hShared : Reference.SharedStateRel cfg yul evm.toSharedState)
    (hParentWorld : CompiledAccountMapRel yul.accountMap evm.accountMap)
    (store : EvmYul.Yul.VarStore)
    {gas address value inOffset inSize outOffset outSize : EvmYul.UInt256}
    {precompiled : EvmYul.PrecompiledContract}
    (hEnough :
      value ≤
        (evm.accountMap.find? evm.executionEnv.codeOwner |>.option ⟨0⟩
          (·.balance)))
    (hDepth : evm.executionEnv.depth < 1024)
    (hPrecompile :
      EvmYul.PrecompiledContract.ofAddress?
        (EvmYul.AccountAddress.ofUInt256 address) = some precompiled)
    (hFailure :
      let target := EvmYul.AccountAddress.ofUInt256 address
      let callMap :=
        evmCallTransfer evm.accountMap evm.executionEnv.codeOwner target value
      let callGas :=
        EvmYul.EVM.Ccallgas target target value gas evm.accountMap
          evm.toMachineState evm.substate
      let accessedSubstate :=
        (EvmYul.State.addAccessedAccount evm.toState target).substate
      let childEnv :=
        EvmYul.EVM.thetaCallExecutionEnv blobVersionedHashes
          evm.executionEnv.codeOwner evm.executionEnv.sender target
          (.Precompiled precompiled)
          (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice)
          value
          (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
          (evm.executionEnv.depth + 1) evm.executionEnv.header
          evm.executionEnv.perm
      (runPrecompiledContract precompiled callMap
        (EvmYul.UInt256.ofNat callGas) accessedSubstate childEnv).1 =
        false)
    (hGas :
      let target := EvmYul.AccountAddress.ofUInt256 address
      let callMap :=
        evmCallTransfer evm.accountMap evm.executionEnv.codeOwner target value
      let callGas :=
        EvmYul.EVM.Ccallgas target target value gas evm.accountMap
          evm.toMachineState evm.substate
      let charged : EvmYul.EVM.State :=
        { evm with
          gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
      let accessedSubstate :=
        (EvmYul.State.addAccessedAccount charged.toState target).substate
      let childEnv :=
        EvmYul.EVM.thetaCallExecutionEnv blobVersionedHashes
          evm.executionEnv.codeOwner evm.executionEnv.sender target
          (.Precompiled precompiled)
          (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice)
          value
          (charged.memory.readWithPadding inOffset.toNat inSize.toNat)
          (evm.executionEnv.depth + 1) evm.executionEnv.header
          evm.executionEnv.perm
      let precompileResult :=
        runPrecompiledContract precompiled callMap
          (EvmYul.UInt256.ofNat callGas) accessedSubstate childEnv
      let targetGas :=
        (charged.toMachineState.finishExternalCall precompileResult.2.2.2.2
          inOffset inSize outOffset outSize).gasAvailable +
          precompileResult.2.2.1
      cfg.gasAvailableRel
        (yul.toMachineState.finishExternalCall ByteArray.empty
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    let target := EvmYul.AccountAddress.ofUInt256 address
    let callMap :=
      evmCallTransfer evm.accountMap evm.executionEnv.codeOwner target value
    let callGas :=
      EvmYul.EVM.Ccallgas target target value gas evm.accountMap
        evm.toMachineState evm.substate
    let charged : EvmYul.EVM.State :=
      { evm with gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
    let accessedSubstate :=
      (EvmYul.State.addAccessedAccount charged.toState target).substate
    let yulEnv : EvmYul.ExecutionEnv .Yul :=
      { yul.executionEnv with
        calldata :=
          yul.toMachineState.memory.readWithPadding
            inOffset.toNat inSize.toNat
        code := default
        codeOwner := target
        source := yul.executionEnv.codeOwner
        weiValue := value
        depth := yul.executionEnv.depth + 1 }
    let evmEnv :=
      EvmYul.EVM.thetaCallExecutionEnv blobVersionedHashes
        evm.executionEnv.codeOwner evm.executionEnv.sender target
        (.Precompiled precompiled)
        (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice)
        value
        (charged.memory.readWithPadding inOffset.toNat inSize.toNat)
        (evm.executionEnv.depth + 1) evm.executionEnv.header
        evm.executionEnv.perm
    let precompileResult :=
      runPrecompiledContract precompiled callMap
        (EvmYul.UInt256.ofNat callGas) accessedSubstate evmEnv
    let targetGas :=
      (charged.toMachineState.finishExternalCall precompileResult.2.2.2.2
        inOffset inSize outOffset outSize).gasAvailable +
        precompileResult.2.2.1
    let evmAfter : EvmYul.EVM.State :=
      { charged with
        toMachineState :=
          { charged.toMachineState.finishExternalCall
              precompileResult.2.2.2.2 inOffset inSize outOffset outSize with
            gasAvailable := targetGas }
        accountMap :=
          if precompileResult.2.1.isEmpty then evm.accountMap
          else precompileResult.2.1
        substate :=
          if precompileResult.2.1.isEmpty then accessedSubstate
          else precompileResult.2.2.2.1 }
    EvmYul.EVM.call fuel.succ.succ gasCost blobVersionedHashes gas
        (EvmYul.UInt256.ofNat evm.executionEnv.codeOwner) address address
        value value inOffset inSize outOffset outSize evm.executionEnv.perm
        evm =
      .ok (⟨0⟩, evmAfter) ∧
      ∃ yulCallMap,
        EvmYul.Yul.callTransferAccountMap? yul.accountMap
            yul.executionEnv.codeOwner target value =
          some yulCallMap ∧
        CompiledAccountMapRel yulCallMap callMap ∧
        EvmYul.PrecompiledContract.ofAddress? target = some precompiled ∧
        ∃ yulAfter,
          EvmYul.Yul.buildPrecompiledContractCallState
              (EvmYul.Yul.addAccessedAccount (.Ok yul store) target)
              yulCallMap precompiled (EvmYul.UInt256.ofNat callGas)
              yulEnv inOffset inSize outOffset outSize =
            .ok (.Ok yulAfter store, [⟨0⟩]) ∧
          Reference.SharedStateRel cfg yulAfter evmAfter.toSharedState := by
  constructor
  · exact
      EVM_call_precompiled_failure_eq hEnough hDepth hPrecompile hFailure
  · dsimp
    let target := EvmYul.AccountAddress.ofUInt256 address
    let callMap :=
      evmCallTransfer evm.accountMap evm.executionEnv.codeOwner target value
    let callGas :=
      EvmYul.EVM.Ccallgas target target value gas evm.accountMap
        evm.toMachineState evm.substate
    let charged : EvmYul.EVM.State :=
      { evm with
        gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
    let yulAccessed : EvmYul.SharedState .Yul :=
      { yul with
        toState := EvmYul.State.addAccessedAccount yul.toState target }
    let evmAccessed : EvmYul.SharedState .EVM :=
      { evm.toSharedState with
        toState := EvmYul.State.addAccessedAccount evm.toState target }
    let yulEnv : EvmYul.ExecutionEnv .Yul :=
      { yul.executionEnv with
        calldata :=
          yul.toMachineState.memory.readWithPadding
            inOffset.toNat inSize.toNat
        code := default
        codeOwner := target
        source := yul.executionEnv.codeOwner
        weiValue := value
        depth := yul.executionEnv.depth + 1 }
    let evmEnv :=
      EvmYul.EVM.thetaCallExecutionEnv blobVersionedHashes
        evm.executionEnv.codeOwner evm.executionEnv.sender target
        (.Precompiled precompiled)
        (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice)
        value
        (charged.memory.readWithPadding inOffset.toNat inSize.toNat)
        (evm.executionEnv.depth + 1) evm.executionEnv.header
        evm.executionEnv.perm
    have hOwner :
        yul.executionEnv.codeOwner = evm.executionEnv.codeOwner := by
      rcases hShared with ⟨hChain, _hMachine⟩
      simpa using hChain.executionEnv.codeOwner
    rcases
        hParentWorld.callTransferAccountMap?_of_evm_enough
          (source := yul.executionEnv.codeOwner)
          (recipient := target)
          (value := value)
          (by simpa [hOwner] using hEnough) with
      ⟨yulCallMap, hTransfer, hCallMapRel⟩
    have hSharedAccessed :
        Reference.SharedStateRel cfg yulAccessed evmAccessed := by
      simpa [yulAccessed, evmAccessed, charged, target] using
        sharedStateRel_addAccessedAccount hShared target
    have hCalldata : yulEnv.calldata = evmEnv.calldata := by
      rcases hShared with ⟨_hChain, hMachine⟩
      simpa [yulEnv, evmEnv, EvmYul.EVM.thetaCallExecutionEnv, charged] using
        congrArg
          (fun memory =>
            memory.readWithPadding inOffset.toNat inSize.toNat)
          hMachine.memory
    have hFailure' :
        (runPrecompiledContract precompiled callMap
          (EvmYul.UInt256.ofNat callGas) evmAccessed.substate evmEnv).1 =
          false := by
      simpa [target, callMap, callGas, charged, evmAccessed, evmEnv] using
        hFailure
    have hRunEmpty :
        runPrecompiledContract precompiled callMap
            (EvmYul.UInt256.ofNat callGas) evmAccessed.substate evmEnv =
          (false, ∅, ⟨0⟩, evmAccessed.substate, ByteArray.empty) :=
      runPrecompiledContract_failure_eq_empty hFailure'
    have hGas' :
        cfg.gasAvailableRel
          (yulAccessed.toMachineState.finishExternalCall ByteArray.empty
            inOffset inSize outOffset outSize).gasAvailable
          ((charged.toMachineState.finishExternalCall
              (runPrecompiledContract precompiled callMap
                (EvmYul.UInt256.ofNat callGas)
                evmAccessed.substate evmEnv).2.2.2.2
              inOffset inSize outOffset outSize).gasAvailable +
            (runPrecompiledContract precompiled callMap
              (EvmYul.UInt256.ofNat callGas)
              evmAccessed.substate evmEnv).2.2.1) := by
      simpa [target, callMap, callGas, charged, evmAccessed, evmEnv,
        yulAccessed] using hGas
    rcases
        buildPrecompiledContractCallState_failure_of_evm_run_rel
          hSharedAccessed store
          (hCallMap := by simpa [callMap, hOwner] using hCallMapRel)
          (hCalldata := hCalldata)
          (precompiled := precompiled)
          (gas := EvmYul.UInt256.ofNat callGas)
          (inOffset := inOffset)
          (inSize := inSize)
          (outOffset := outOffset)
          (outSize := outSize)
          hFailure' hGas' with
      ⟨yulAfter, hBuild, hRel⟩
    refine ⟨yulCallMap, hTransfer, ?_, hPrecompile, yulAfter, ?_, ?_⟩
    · simpa [callMap, hOwner] using hCallMapRel
    · simpa [yulAccessed, yulEnv, target,
        EvmYul.Yul.addAccessedAccount, EvmYul.Yul.State.setState,
        EvmYul.Yul.State.toState] using hBuild
    · simpa [target, callMap, callGas, charged, evmAccessed, evmEnv,
        hRunEmpty] using hRel

theorem primCall_CALL_precompiled_success_rel
    {cfg : Reference.StateRelConfig}
    {fuel gasCost : Nat}
    {blobVersionedHashes : List ByteArray}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.EVM.State}
    (hShared : Reference.SharedStateRel cfg yul evm.toSharedState)
    (hParentWorld : CompiledAccountMapRel yul.accountMap evm.accountMap)
    (hCfgAccountMap :
      ∀ {yulMap : EvmYul.AccountMap .Yul}
        {evmMap : EvmYul.AccountMap .EVM},
        CompiledAccountMapRel yulMap evmMap →
          cfg.accountMapRel yulMap evmMap)
    (store : EvmYul.Yul.VarStore)
    {gas address value inOffset inSize outOffset outSize : EvmYul.UInt256}
    {precompiled : EvmYul.PrecompiledContract}
    (hStaticAllowed :
      ¬ (¬ yul.executionEnv.perm ∧ value ≠ ⟨0⟩))
    (hEnough :
      value ≤
        (evm.accountMap.find? evm.executionEnv.codeOwner |>.option ⟨0⟩
          (·.balance)))
    (hDepth : evm.executionEnv.depth < 1024)
    (hPrecompile :
      EvmYul.PrecompiledContract.ofAddress?
        (EvmYul.AccountAddress.ofUInt256 address) = some precompiled)
    (hSuccess :
      let target := EvmYul.AccountAddress.ofUInt256 address
      let callMap :=
        evmCallTransfer evm.accountMap evm.executionEnv.codeOwner target value
      let callGas :=
        EvmYul.EVM.Ccallgas target target value gas evm.accountMap
          evm.toMachineState evm.substate
      let accessedSubstate :=
        (EvmYul.State.addAccessedAccount evm.toState target).substate
      let childEnv :=
        EvmYul.EVM.thetaCallExecutionEnv blobVersionedHashes
          evm.executionEnv.codeOwner evm.executionEnv.sender target
          (.Precompiled precompiled)
          (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice)
          value
          (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
          (evm.executionEnv.depth + 1) evm.executionEnv.header
          evm.executionEnv.perm
      (runPrecompiledContract precompiled callMap
        (EvmYul.UInt256.ofNat callGas) accessedSubstate childEnv).1 =
        true)
    (hGas :
      let target := EvmYul.AccountAddress.ofUInt256 address
      let callMap :=
        evmCallTransfer evm.accountMap evm.executionEnv.codeOwner target value
      let callGas :=
        EvmYul.EVM.Ccallgas target target value gas evm.accountMap
          evm.toMachineState evm.substate
      let charged : EvmYul.EVM.State :=
        { evm with
          gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
      let accessedSubstate :=
        (EvmYul.State.addAccessedAccount charged.toState target).substate
      let childEnv :=
        EvmYul.EVM.thetaCallExecutionEnv blobVersionedHashes
          evm.executionEnv.codeOwner evm.executionEnv.sender target
          (.Precompiled precompiled)
          (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice)
          value
          (charged.memory.readWithPadding inOffset.toNat inSize.toNat)
          (evm.executionEnv.depth + 1) evm.executionEnv.header
          evm.executionEnv.perm
      let precompileResult :=
        runPrecompiledContract precompiled callMap
          (EvmYul.UInt256.ofNat callGas) accessedSubstate childEnv
      let targetGas :=
        (charged.toMachineState.finishExternalCall precompileResult.2.2.2.2
          inOffset inSize outOffset outSize).gasAvailable +
          precompileResult.2.2.1
      cfg.gasAvailableRel
        (yul.toMachineState.finishExternalCall
          precompileResult.2.2.2.2 inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    let target := EvmYul.AccountAddress.ofUInt256 address
    let callMap :=
      evmCallTransfer evm.accountMap evm.executionEnv.codeOwner target value
    let callGas :=
      EvmYul.EVM.Ccallgas target target value gas evm.accountMap
        evm.toMachineState evm.substate
    let charged : EvmYul.EVM.State :=
      { evm with gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
    let accessedSubstate :=
      (EvmYul.State.addAccessedAccount charged.toState target).substate
    let _yulEnv : EvmYul.ExecutionEnv .Yul :=
      { yul.executionEnv with
        calldata :=
          yul.toMachineState.memory.readWithPadding
            inOffset.toNat inSize.toNat
        code := default
        codeOwner := target
        source := yul.executionEnv.codeOwner
        weiValue := value
        depth := yul.executionEnv.depth + 1 }
    let evmEnv :=
      EvmYul.EVM.thetaCallExecutionEnv blobVersionedHashes
        evm.executionEnv.codeOwner evm.executionEnv.sender target
        (.Precompiled precompiled)
        (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice)
        value
        (charged.memory.readWithPadding inOffset.toNat inSize.toNat)
        (evm.executionEnv.depth + 1) evm.executionEnv.header
        evm.executionEnv.perm
    let precompileResult :=
      runPrecompiledContract precompiled callMap
        (EvmYul.UInt256.ofNat callGas) accessedSubstate evmEnv
    let targetGas :=
      (charged.toMachineState.finishExternalCall precompileResult.2.2.2.2
        inOffset inSize outOffset outSize).gasAvailable +
        precompileResult.2.2.1
    let evmAfter : EvmYul.EVM.State :=
      { charged with
        toMachineState :=
          { charged.toMachineState.finishExternalCall
              precompileResult.2.2.2.2 inOffset inSize outOffset outSize with
            gasAvailable := targetGas }
        accountMap :=
          if precompileResult.2.1.isEmpty then evm.accountMap
          else precompileResult.2.1
        substate :=
          if precompileResult.2.1.isEmpty then accessedSubstate
          else precompileResult.2.2.2.1 }
    EvmYul.EVM.call fuel.succ.succ gasCost blobVersionedHashes gas
        (EvmYul.UInt256.ofNat evm.executionEnv.codeOwner) address address
        value value inOffset inSize outOffset outSize evm.executionEnv.perm
        evm =
      .ok (⟨1⟩, evmAfter) ∧
      ∃ yulAfter,
        EvmYul.Yul.primCall fuel.succ (.Ok yul store) .CALL
            [gas, address, value, inOffset, inSize, outOffset, outSize] =
          .ok (.Ok yulAfter store, [⟨1⟩]) ∧
        Reference.SharedStateRel cfg yulAfter evmAfter.toSharedState := by
  dsimp at hGas ⊢
  rcases
      call_precompiled_success_rel hShared hParentWorld hCfgAccountMap store
        hEnough hDepth hPrecompile hSuccess hGas with
    ⟨hEvm, yulCallMap, hTransfer, _hCallMapRel, hPrecompileYul,
      yulAfter, hBuild, hRel⟩
  refine ⟨hEvm, yulAfter, ?_, hRel⟩
  have hDepthEq :
      yul.executionEnv.depth = evm.executionEnv.depth := by
    rcases hShared with ⟨hChain, _hMachine⟩
    simpa using hChain.executionEnv.depth
  have hNotDepthLimit : ¬ yul.executionEnv.depth ≥ 1024 := by
    omega
  have hStaticAllowed' :
      ¬ (yul.executionEnv.perm = false ∧ ¬ value = ⟨0⟩) := by
    intro hStatic
    exact hStaticAllowed (by simpa using hStatic)
  have hCallGasEq :
      EvmYul.EVM.Ccallgas
          (EvmYul.AccountAddress.ofUInt256 address)
          (EvmYul.AccountAddress.ofUInt256 address)
          value gas yul.accountMap yul.toMachineState yul.substate =
        EvmYul.EVM.Ccallgas
          (EvmYul.AccountAddress.ofUInt256 address)
          (EvmYul.AccountAddress.ofUInt256 address)
          value gas evm.accountMap evm.toMachineState evm.substate := by
    rcases hShared with ⟨hChain, hMachine⟩
    exact
      hParentWorld.Ccallgas_eq
        (machineStateRel_gasAvailable_eq hMachine) hChain.substate
  simpa [EvmYul.Yul.primCall, hStaticAllowed', hTransfer,
    hCallGasEq,
    hNotDepthLimit, hPrecompileYul, EvmYul.toExecute,
    EvmYul.Yul.addAccessedAccount,
    EvmYul.State.addAccessedAccount,
    EvmYul.Yul.State.sharedState,
    EvmYul.Yul.State.executionEnv,
    EvmYul.Yul.State.setState, EvmYul.Yul.State.toState,
    EvmYul.Yul.State.toSharedState,
    EvmYul.Yul.State.toMachineState] using hBuild

theorem primCall_CALL_precompiled_success_rel_stateRelConfig
    {varStackRel : Reference.VarStackRel}
    {terminalCfgRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop}
    {revertCfgRel : Reference.State → EVMState → Prop}
    {gasAvailableRel : Word → Word → Prop}
    {gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm}
    {totalGasRel : Nat → Nat → Prop}
    {fuel gasCost : Nat}
    {blobVersionedHashes : List ByteArray}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.EVM.State}
    (hShared :
      Reference.SharedStateRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        yul evm.toSharedState)
    (store : EvmYul.Yul.VarStore)
    {gas address value inOffset inSize outOffset outSize : EvmYul.UInt256}
    {precompiled : EvmYul.PrecompiledContract}
    (hStaticAllowed :
      ¬ (¬ yul.executionEnv.perm ∧ value ≠ ⟨0⟩))
    (hEnough :
      value ≤
        (evm.accountMap.find? evm.executionEnv.codeOwner |>.option ⟨0⟩
          (·.balance)))
    (hDepth : evm.executionEnv.depth < 1024)
    (hPrecompile :
      EvmYul.PrecompiledContract.ofAddress?
        (EvmYul.AccountAddress.ofUInt256 address) = some precompiled)
    (hSuccess :
      let target := EvmYul.AccountAddress.ofUInt256 address
      let callMap :=
        evmCallTransfer evm.accountMap evm.executionEnv.codeOwner target value
      let callGas :=
        EvmYul.EVM.Ccallgas target target value gas evm.accountMap
          evm.toMachineState evm.substate
      let accessedSubstate :=
        (EvmYul.State.addAccessedAccount evm.toState target).substate
      let childEnv :=
        EvmYul.EVM.thetaCallExecutionEnv blobVersionedHashes
          evm.executionEnv.codeOwner evm.executionEnv.sender target
          (.Precompiled precompiled)
          (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice)
          value
          (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
          (evm.executionEnv.depth + 1) evm.executionEnv.header
          evm.executionEnv.perm
      (runPrecompiledContract precompiled callMap
        (EvmYul.UInt256.ofNat callGas) accessedSubstate childEnv).1 =
        true)
    (hGas :
      let target := EvmYul.AccountAddress.ofUInt256 address
      let callMap :=
        evmCallTransfer evm.accountMap evm.executionEnv.codeOwner target value
      let callGas :=
        EvmYul.EVM.Ccallgas target target value gas evm.accountMap
          evm.toMachineState evm.substate
      let charged : EvmYul.EVM.State :=
        { evm with
          gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
      let accessedSubstate :=
        (EvmYul.State.addAccessedAccount charged.toState target).substate
      let childEnv :=
        EvmYul.EVM.thetaCallExecutionEnv blobVersionedHashes
          evm.executionEnv.codeOwner evm.executionEnv.sender target
          (.Precompiled precompiled)
          (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice)
          value
          (charged.memory.readWithPadding inOffset.toNat inSize.toNat)
          (evm.executionEnv.depth + 1) evm.executionEnv.header
          evm.executionEnv.perm
      let precompileResult :=
        runPrecompiledContract precompiled callMap
          (EvmYul.UInt256.ofNat callGas) accessedSubstate childEnv
      let targetGas :=
        (charged.toMachineState.finishExternalCall precompileResult.2.2.2.2
          inOffset inSize outOffset outSize).gasAvailable +
          precompileResult.2.2.1
      gasAvailableRel
        (yul.toMachineState.finishExternalCall
          precompileResult.2.2.2.2 inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    let target := EvmYul.AccountAddress.ofUInt256 address
    let callMap :=
      evmCallTransfer evm.accountMap evm.executionEnv.codeOwner target value
    let callGas :=
      EvmYul.EVM.Ccallgas target target value gas evm.accountMap
        evm.toMachineState evm.substate
    let charged : EvmYul.EVM.State :=
      { evm with gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
    let accessedSubstate :=
      (EvmYul.State.addAccessedAccount charged.toState target).substate
    let _yulEnv : EvmYul.ExecutionEnv .Yul :=
      { yul.executionEnv with
        calldata :=
          yul.toMachineState.memory.readWithPadding
            inOffset.toNat inSize.toNat
        code := default
        codeOwner := target
        source := yul.executionEnv.codeOwner
        weiValue := value
        depth := yul.executionEnv.depth + 1 }
    let evmEnv :=
      EvmYul.EVM.thetaCallExecutionEnv blobVersionedHashes
        evm.executionEnv.codeOwner evm.executionEnv.sender target
        (.Precompiled precompiled)
        (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice)
        value
        (charged.memory.readWithPadding inOffset.toNat inSize.toNat)
        (evm.executionEnv.depth + 1) evm.executionEnv.header
        evm.executionEnv.perm
    let precompileResult :=
      runPrecompiledContract precompiled callMap
        (EvmYul.UInt256.ofNat callGas) accessedSubstate evmEnv
    let targetGas :=
      (charged.toMachineState.finishExternalCall precompileResult.2.2.2.2
        inOffset inSize outOffset outSize).gasAvailable +
        precompileResult.2.2.1
    let evmAfter : EvmYul.EVM.State :=
      { charged with
        toMachineState :=
          { charged.toMachineState.finishExternalCall
              precompileResult.2.2.2.2 inOffset inSize outOffset outSize with
            gasAvailable := targetGas }
        accountMap :=
          if precompileResult.2.1.isEmpty then evm.accountMap
          else precompileResult.2.1
        substate :=
          if precompileResult.2.1.isEmpty then accessedSubstate
          else precompileResult.2.2.2.1 }
    EvmYul.EVM.call fuel.succ.succ gasCost blobVersionedHashes gas
        (EvmYul.UInt256.ofNat evm.executionEnv.codeOwner) address address
        value value inOffset inSize outOffset outSize evm.executionEnv.perm
        evm =
      .ok (⟨1⟩, evmAfter) ∧
      ∃ yulAfter,
        EvmYul.Yul.primCall fuel.succ (.Ok yul store) .CALL
            [gas, address, value, inOffset, inSize, outOffset, outSize] =
          .ok (.Ok yulAfter store, [⟨1⟩]) ∧
        Reference.SharedStateRel
          (stateRelConfig varStackRel terminalCfgRel revertCfgRel
            gasAvailableRel gasValueRel totalGasRel)
          yulAfter evmAfter.toSharedState := by
  exact
    primCall_CALL_precompiled_success_rel
      (cfg :=
        stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
      hShared
      (compiledAccountMapRel_of_sharedStateRel_stateRelConfig hShared)
      (fun hRel => stateRelConfig_accountMapRel_of_compiledAccountMapRel hRel)
      store hStaticAllowed hEnough hDepth hPrecompile hSuccess hGas

theorem primCall_CALL_precompiled_failure_rel
    {cfg : Reference.StateRelConfig}
    {fuel gasCost : Nat}
    {blobVersionedHashes : List ByteArray}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.EVM.State}
    (hShared : Reference.SharedStateRel cfg yul evm.toSharedState)
    (hParentWorld : CompiledAccountMapRel yul.accountMap evm.accountMap)
    (store : EvmYul.Yul.VarStore)
    {gas address value inOffset inSize outOffset outSize : EvmYul.UInt256}
    {precompiled : EvmYul.PrecompiledContract}
    (hStaticAllowed :
      ¬ (¬ yul.executionEnv.perm ∧ value ≠ ⟨0⟩))
    (hEnough :
      value ≤
        (evm.accountMap.find? evm.executionEnv.codeOwner |>.option ⟨0⟩
          (·.balance)))
    (hDepth : evm.executionEnv.depth < 1024)
    (hPrecompile :
      EvmYul.PrecompiledContract.ofAddress?
        (EvmYul.AccountAddress.ofUInt256 address) = some precompiled)
    (hFailure :
      let target := EvmYul.AccountAddress.ofUInt256 address
      let callMap :=
        evmCallTransfer evm.accountMap evm.executionEnv.codeOwner target value
      let callGas :=
        EvmYul.EVM.Ccallgas target target value gas evm.accountMap
          evm.toMachineState evm.substate
      let accessedSubstate :=
        (EvmYul.State.addAccessedAccount evm.toState target).substate
      let childEnv :=
        EvmYul.EVM.thetaCallExecutionEnv blobVersionedHashes
          evm.executionEnv.codeOwner evm.executionEnv.sender target
          (.Precompiled precompiled)
          (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice)
          value
          (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
          (evm.executionEnv.depth + 1) evm.executionEnv.header
          evm.executionEnv.perm
      (runPrecompiledContract precompiled callMap
        (EvmYul.UInt256.ofNat callGas) accessedSubstate childEnv).1 =
        false)
    (hGas :
      let target := EvmYul.AccountAddress.ofUInt256 address
      let callMap :=
        evmCallTransfer evm.accountMap evm.executionEnv.codeOwner target value
      let callGas :=
        EvmYul.EVM.Ccallgas target target value gas evm.accountMap
          evm.toMachineState evm.substate
      let charged : EvmYul.EVM.State :=
        { evm with
          gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
      let accessedSubstate :=
        (EvmYul.State.addAccessedAccount charged.toState target).substate
      let childEnv :=
        EvmYul.EVM.thetaCallExecutionEnv blobVersionedHashes
          evm.executionEnv.codeOwner evm.executionEnv.sender target
          (.Precompiled precompiled)
          (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice)
          value
          (charged.memory.readWithPadding inOffset.toNat inSize.toNat)
          (evm.executionEnv.depth + 1) evm.executionEnv.header
          evm.executionEnv.perm
      let precompileResult :=
        runPrecompiledContract precompiled callMap
          (EvmYul.UInt256.ofNat callGas) accessedSubstate childEnv
      let targetGas :=
        (charged.toMachineState.finishExternalCall precompileResult.2.2.2.2
          inOffset inSize outOffset outSize).gasAvailable +
          precompileResult.2.2.1
      cfg.gasAvailableRel
        (yul.toMachineState.finishExternalCall ByteArray.empty
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    let target := EvmYul.AccountAddress.ofUInt256 address
    let callMap :=
      evmCallTransfer evm.accountMap evm.executionEnv.codeOwner target value
    let callGas :=
      EvmYul.EVM.Ccallgas target target value gas evm.accountMap
        evm.toMachineState evm.substate
    let charged : EvmYul.EVM.State :=
      { evm with gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
    let accessedSubstate :=
      (EvmYul.State.addAccessedAccount charged.toState target).substate
    let _yulEnv : EvmYul.ExecutionEnv .Yul :=
      { yul.executionEnv with
        calldata :=
          yul.toMachineState.memory.readWithPadding
            inOffset.toNat inSize.toNat
        code := default
        codeOwner := target
        source := yul.executionEnv.codeOwner
        weiValue := value
        depth := yul.executionEnv.depth + 1 }
    let evmEnv :=
      EvmYul.EVM.thetaCallExecutionEnv blobVersionedHashes
        evm.executionEnv.codeOwner evm.executionEnv.sender target
        (.Precompiled precompiled)
        (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice)
        value
        (charged.memory.readWithPadding inOffset.toNat inSize.toNat)
        (evm.executionEnv.depth + 1) evm.executionEnv.header
        evm.executionEnv.perm
    let precompileResult :=
      runPrecompiledContract precompiled callMap
        (EvmYul.UInt256.ofNat callGas) accessedSubstate evmEnv
    let targetGas :=
      (charged.toMachineState.finishExternalCall precompileResult.2.2.2.2
        inOffset inSize outOffset outSize).gasAvailable +
        precompileResult.2.2.1
    let evmAfter : EvmYul.EVM.State :=
      { charged with
        toMachineState :=
          { charged.toMachineState.finishExternalCall
              precompileResult.2.2.2.2 inOffset inSize outOffset outSize with
            gasAvailable := targetGas }
        accountMap :=
          if precompileResult.2.1.isEmpty then evm.accountMap
          else precompileResult.2.1
        substate :=
          if precompileResult.2.1.isEmpty then accessedSubstate
          else precompileResult.2.2.2.1 }
    EvmYul.EVM.call fuel.succ.succ gasCost blobVersionedHashes gas
        (EvmYul.UInt256.ofNat evm.executionEnv.codeOwner) address address
        value value inOffset inSize outOffset outSize evm.executionEnv.perm
        evm =
      .ok (⟨0⟩, evmAfter) ∧
      ∃ yulAfter,
        EvmYul.Yul.primCall fuel.succ (.Ok yul store) .CALL
            [gas, address, value, inOffset, inSize, outOffset, outSize] =
          .ok (.Ok yulAfter store, [⟨0⟩]) ∧
        Reference.SharedStateRel cfg yulAfter evmAfter.toSharedState := by
  dsimp at hGas ⊢
  rcases
      call_precompiled_failure_rel hShared hParentWorld store
        hEnough hDepth hPrecompile hFailure hGas with
    ⟨hEvm, yulCallMap, hTransfer, _hCallMapRel, hPrecompileYul,
      yulAfter, hBuild, hRel⟩
  refine ⟨hEvm, yulAfter, ?_, hRel⟩
  have hDepthEq :
      yul.executionEnv.depth = evm.executionEnv.depth := by
    rcases hShared with ⟨hChain, _hMachine⟩
    simpa using hChain.executionEnv.depth
  have hNotDepthLimit : ¬ yul.executionEnv.depth ≥ 1024 := by
    omega
  have hStaticAllowed' :
      ¬ (yul.executionEnv.perm = false ∧ ¬ value = ⟨0⟩) := by
    intro hStatic
    exact hStaticAllowed (by simpa using hStatic)
  have hCallGasEq :
      EvmYul.EVM.Ccallgas
          (EvmYul.AccountAddress.ofUInt256 address)
          (EvmYul.AccountAddress.ofUInt256 address)
          value gas yul.accountMap yul.toMachineState yul.substate =
        EvmYul.EVM.Ccallgas
          (EvmYul.AccountAddress.ofUInt256 address)
          (EvmYul.AccountAddress.ofUInt256 address)
          value gas evm.accountMap evm.toMachineState evm.substate := by
    rcases hShared with ⟨hChain, hMachine⟩
    exact
      hParentWorld.Ccallgas_eq
        (machineStateRel_gasAvailable_eq hMachine) hChain.substate
  simpa [EvmYul.Yul.primCall, hStaticAllowed', hTransfer,
    hCallGasEq,
    hNotDepthLimit, hPrecompileYul, EvmYul.toExecute,
    EvmYul.Yul.addAccessedAccount,
    EvmYul.State.addAccessedAccount,
    EvmYul.Yul.State.sharedState,
    EvmYul.Yul.State.executionEnv,
    EvmYul.Yul.State.setState, EvmYul.Yul.State.toState,
    EvmYul.Yul.State.toSharedState,
    EvmYul.Yul.State.toMachineState] using hBuild

theorem primCall_CALL_precompiled_failure_rel_stateRelConfig
    {varStackRel : Reference.VarStackRel}
    {terminalCfgRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop}
    {revertCfgRel : Reference.State → EVMState → Prop}
    {gasAvailableRel : Word → Word → Prop}
    {gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm}
    {totalGasRel : Nat → Nat → Prop}
    {fuel gasCost : Nat}
    {blobVersionedHashes : List ByteArray}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.EVM.State}
    (hShared :
      Reference.SharedStateRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        yul evm.toSharedState)
    (store : EvmYul.Yul.VarStore)
    {gas address value inOffset inSize outOffset outSize : EvmYul.UInt256}
    {precompiled : EvmYul.PrecompiledContract}
    (hStaticAllowed :
      ¬ (¬ yul.executionEnv.perm ∧ value ≠ ⟨0⟩))
    (hEnough :
      value ≤
        (evm.accountMap.find? evm.executionEnv.codeOwner |>.option ⟨0⟩
          (·.balance)))
    (hDepth : evm.executionEnv.depth < 1024)
    (hPrecompile :
      EvmYul.PrecompiledContract.ofAddress?
        (EvmYul.AccountAddress.ofUInt256 address) = some precompiled)
    (hFailure :
      let target := EvmYul.AccountAddress.ofUInt256 address
      let callMap :=
        evmCallTransfer evm.accountMap evm.executionEnv.codeOwner target value
      let callGas :=
        EvmYul.EVM.Ccallgas target target value gas evm.accountMap
          evm.toMachineState evm.substate
      let accessedSubstate :=
        (EvmYul.State.addAccessedAccount evm.toState target).substate
      let childEnv :=
        EvmYul.EVM.thetaCallExecutionEnv blobVersionedHashes
          evm.executionEnv.codeOwner evm.executionEnv.sender target
          (.Precompiled precompiled)
          (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice)
          value
          (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
          (evm.executionEnv.depth + 1) evm.executionEnv.header
          evm.executionEnv.perm
      (runPrecompiledContract precompiled callMap
        (EvmYul.UInt256.ofNat callGas) accessedSubstate childEnv).1 =
        false)
    (hGas :
      let target := EvmYul.AccountAddress.ofUInt256 address
      let callMap :=
        evmCallTransfer evm.accountMap evm.executionEnv.codeOwner target value
      let callGas :=
        EvmYul.EVM.Ccallgas target target value gas evm.accountMap
          evm.toMachineState evm.substate
      let charged : EvmYul.EVM.State :=
        { evm with
          gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
      let accessedSubstate :=
        (EvmYul.State.addAccessedAccount charged.toState target).substate
      let childEnv :=
        EvmYul.EVM.thetaCallExecutionEnv blobVersionedHashes
          evm.executionEnv.codeOwner evm.executionEnv.sender target
          (.Precompiled precompiled)
          (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice)
          value
          (charged.memory.readWithPadding inOffset.toNat inSize.toNat)
          (evm.executionEnv.depth + 1) evm.executionEnv.header
          evm.executionEnv.perm
      let precompileResult :=
        runPrecompiledContract precompiled callMap
          (EvmYul.UInt256.ofNat callGas) accessedSubstate childEnv
      let targetGas :=
        (charged.toMachineState.finishExternalCall precompileResult.2.2.2.2
          inOffset inSize outOffset outSize).gasAvailable +
          precompileResult.2.2.1
      gasAvailableRel
        (yul.toMachineState.finishExternalCall ByteArray.empty
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    let target := EvmYul.AccountAddress.ofUInt256 address
    let callMap :=
      evmCallTransfer evm.accountMap evm.executionEnv.codeOwner target value
    let callGas :=
      EvmYul.EVM.Ccallgas target target value gas evm.accountMap
        evm.toMachineState evm.substate
    let charged : EvmYul.EVM.State :=
      { evm with gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
    let accessedSubstate :=
      (EvmYul.State.addAccessedAccount charged.toState target).substate
    let _yulEnv : EvmYul.ExecutionEnv .Yul :=
      { yul.executionEnv with
        calldata :=
          yul.toMachineState.memory.readWithPadding
            inOffset.toNat inSize.toNat
        code := default
        codeOwner := target
        source := yul.executionEnv.codeOwner
        weiValue := value
        depth := yul.executionEnv.depth + 1 }
    let evmEnv :=
      EvmYul.EVM.thetaCallExecutionEnv blobVersionedHashes
        evm.executionEnv.codeOwner evm.executionEnv.sender target
        (.Precompiled precompiled)
        (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice)
        value
        (charged.memory.readWithPadding inOffset.toNat inSize.toNat)
        (evm.executionEnv.depth + 1) evm.executionEnv.header
        evm.executionEnv.perm
    let precompileResult :=
      runPrecompiledContract precompiled callMap
        (EvmYul.UInt256.ofNat callGas) accessedSubstate evmEnv
    let targetGas :=
      (charged.toMachineState.finishExternalCall precompileResult.2.2.2.2
        inOffset inSize outOffset outSize).gasAvailable +
        precompileResult.2.2.1
    let evmAfter : EvmYul.EVM.State :=
      { charged with
        toMachineState :=
          { charged.toMachineState.finishExternalCall
              precompileResult.2.2.2.2 inOffset inSize outOffset outSize with
            gasAvailable := targetGas }
        accountMap :=
          if precompileResult.2.1.isEmpty then evm.accountMap
          else precompileResult.2.1
        substate :=
          if precompileResult.2.1.isEmpty then accessedSubstate
          else precompileResult.2.2.2.1 }
    EvmYul.EVM.call fuel.succ.succ gasCost blobVersionedHashes gas
        (EvmYul.UInt256.ofNat evm.executionEnv.codeOwner) address address
        value value inOffset inSize outOffset outSize evm.executionEnv.perm
        evm =
      .ok (⟨0⟩, evmAfter) ∧
      ∃ yulAfter,
        EvmYul.Yul.primCall fuel.succ (.Ok yul store) .CALL
            [gas, address, value, inOffset, inSize, outOffset, outSize] =
          .ok (.Ok yulAfter store, [⟨0⟩]) ∧
        Reference.SharedStateRel
          (stateRelConfig varStackRel terminalCfgRel revertCfgRel
            gasAvailableRel gasValueRel totalGasRel)
          yulAfter evmAfter.toSharedState := by
  exact
    primCall_CALL_precompiled_failure_rel
      (cfg :=
        stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
      hShared
      (compiledAccountMapRel_of_sharedStateRel_stateRelConfig hShared)
      store hStaticAllowed hEnough hDepth hPrecompile hFailure hGas

theorem CALLPrimitiveRel.precompiledSuccess_stateRelConfig
    {varStackRel : Reference.VarStackRel}
    {terminalCfgRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop}
    {revertCfgRel : Reference.State → EVMState → Prop}
    {gasAvailableRel : Word → Word → Prop}
    {gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm}
    {totalGasRel : Nat → Nat → Prop}
    {fuel gasCost : Nat}
    {blobVersionedHashes : List ByteArray}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.EVM.State}
    (hShared :
      Reference.SharedStateRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        yul evm.toSharedState)
    (store : EvmYul.Yul.VarStore)
    {gas address value inOffset inSize outOffset outSize : EvmYul.UInt256}
    {precompiled : EvmYul.PrecompiledContract}
    (hStaticAllowed :
      ¬ (¬ yul.executionEnv.perm ∧ value ≠ ⟨0⟩))
    (hEnough :
      value ≤
        (evm.accountMap.find? evm.executionEnv.codeOwner |>.option ⟨0⟩
          (·.balance)))
    (hDepth : evm.executionEnv.depth < 1024)
    (hPrecompile :
      EvmYul.PrecompiledContract.ofAddress?
        (EvmYul.AccountAddress.ofUInt256 address) = some precompiled)
    (hSuccess :
      let target := EvmYul.AccountAddress.ofUInt256 address
      let callMap :=
        evmCallTransfer evm.accountMap evm.executionEnv.codeOwner target value
      let callGas :=
        EvmYul.EVM.Ccallgas target target value gas evm.accountMap
          evm.toMachineState evm.substate
      let accessedSubstate :=
        (EvmYul.State.addAccessedAccount evm.toState target).substate
      let childEnv :=
        EvmYul.EVM.thetaCallExecutionEnv blobVersionedHashes
          evm.executionEnv.codeOwner evm.executionEnv.sender target
          (.Precompiled precompiled)
          (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice)
          value
          (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
          (evm.executionEnv.depth + 1) evm.executionEnv.header
          evm.executionEnv.perm
      (runPrecompiledContract precompiled callMap
        (EvmYul.UInt256.ofNat callGas) accessedSubstate childEnv).1 =
        true)
    (hGas :
      let target := EvmYul.AccountAddress.ofUInt256 address
      let callMap :=
        evmCallTransfer evm.accountMap evm.executionEnv.codeOwner target value
      let callGas :=
        EvmYul.EVM.Ccallgas target target value gas evm.accountMap
          evm.toMachineState evm.substate
      let charged : EvmYul.EVM.State :=
        { evm with
          gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
      let accessedSubstate :=
        (EvmYul.State.addAccessedAccount charged.toState target).substate
      let childEnv :=
        EvmYul.EVM.thetaCallExecutionEnv blobVersionedHashes
          evm.executionEnv.codeOwner evm.executionEnv.sender target
          (.Precompiled precompiled)
          (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice)
          value
          (charged.memory.readWithPadding inOffset.toNat inSize.toNat)
          (evm.executionEnv.depth + 1) evm.executionEnv.header
          evm.executionEnv.perm
      let precompileResult :=
        runPrecompiledContract precompiled callMap
          (EvmYul.UInt256.ofNat callGas) accessedSubstate childEnv
      let targetGas :=
        (charged.toMachineState.finishExternalCall precompileResult.2.2.2.2
          inOffset inSize outOffset outSize).gasAvailable +
          precompileResult.2.2.1
      gasAvailableRel
        (yul.toMachineState.finishExternalCall
          precompileResult.2.2.2.2 inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    CALLPrimitiveRel
      (stateRelConfig varStackRel terminalCfgRel revertCfgRel
        gasAvailableRel gasValueRel totalGasRel)
      fuel.succ fuel.succ.succ gasCost blobVersionedHashes yul evm store
      gas address value inOffset inSize outOffset outSize := by
  let target := EvmYul.AccountAddress.ofUInt256 address
  let callMap :=
    evmCallTransfer evm.accountMap evm.executionEnv.codeOwner target value
  let callGas :=
    EvmYul.EVM.Ccallgas target target value gas evm.accountMap
      evm.toMachineState evm.substate
  let charged : EvmYul.EVM.State :=
    { evm with gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
  let accessedSubstate :=
    (EvmYul.State.addAccessedAccount charged.toState target).substate
  let evmEnv :=
    EvmYul.EVM.thetaCallExecutionEnv blobVersionedHashes
      evm.executionEnv.codeOwner evm.executionEnv.sender target
      (.Precompiled precompiled)
      (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice)
      value
      (charged.memory.readWithPadding inOffset.toNat inSize.toNat)
      (evm.executionEnv.depth + 1) evm.executionEnv.header
      evm.executionEnv.perm
  let precompileResult :=
    runPrecompiledContract precompiled callMap
      (EvmYul.UInt256.ofNat callGas) accessedSubstate evmEnv
  let targetGas :=
    (charged.toMachineState.finishExternalCall precompileResult.2.2.2.2
      inOffset inSize outOffset outSize).gasAvailable +
      precompileResult.2.2.1
  let evmAfter : EvmYul.EVM.State :=
    { charged with
      toMachineState :=
        { charged.toMachineState.finishExternalCall
            precompileResult.2.2.2.2 inOffset inSize outOffset outSize with
          gasAvailable := targetGas }
      accountMap :=
        if precompileResult.2.1.isEmpty then evm.accountMap
        else precompileResult.2.1
      substate :=
        if precompileResult.2.1.isEmpty then accessedSubstate
        else precompileResult.2.2.2.1 }
  rcases
      primCall_CALL_precompiled_success_rel_stateRelConfig
        hShared store hStaticAllowed hEnough hDepth hPrecompile hSuccess hGas
    with
    ⟨hEvm, yulAfter, hYul, hRel⟩
  refine ⟨⟨1⟩, evmAfter, yulAfter, ?_, ?_, ?_⟩
  · simpa [evmAfter, targetGas, precompileResult, evmEnv,
      accessedSubstate, charged, callGas, callMap, target] using hEvm
  · exact hYul
  · simpa [evmAfter, targetGas, precompileResult, evmEnv,
      accessedSubstate, charged, callGas, callMap, target] using hRel

theorem CALLPrimitiveRel.precompiledFailure_stateRelConfig
    {varStackRel : Reference.VarStackRel}
    {terminalCfgRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop}
    {revertCfgRel : Reference.State → EVMState → Prop}
    {gasAvailableRel : Word → Word → Prop}
    {gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm}
    {totalGasRel : Nat → Nat → Prop}
    {fuel gasCost : Nat}
    {blobVersionedHashes : List ByteArray}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.EVM.State}
    (hShared :
      Reference.SharedStateRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        yul evm.toSharedState)
    (store : EvmYul.Yul.VarStore)
    {gas address value inOffset inSize outOffset outSize : EvmYul.UInt256}
    {precompiled : EvmYul.PrecompiledContract}
    (hStaticAllowed :
      ¬ (¬ yul.executionEnv.perm ∧ value ≠ ⟨0⟩))
    (hEnough :
      value ≤
        (evm.accountMap.find? evm.executionEnv.codeOwner |>.option ⟨0⟩
          (·.balance)))
    (hDepth : evm.executionEnv.depth < 1024)
    (hPrecompile :
      EvmYul.PrecompiledContract.ofAddress?
        (EvmYul.AccountAddress.ofUInt256 address) = some precompiled)
    (hFailure :
      let target := EvmYul.AccountAddress.ofUInt256 address
      let callMap :=
        evmCallTransfer evm.accountMap evm.executionEnv.codeOwner target value
      let callGas :=
        EvmYul.EVM.Ccallgas target target value gas evm.accountMap
          evm.toMachineState evm.substate
      let accessedSubstate :=
        (EvmYul.State.addAccessedAccount evm.toState target).substate
      let childEnv :=
        EvmYul.EVM.thetaCallExecutionEnv blobVersionedHashes
          evm.executionEnv.codeOwner evm.executionEnv.sender target
          (.Precompiled precompiled)
          (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice)
          value
          (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
          (evm.executionEnv.depth + 1) evm.executionEnv.header
          evm.executionEnv.perm
      (runPrecompiledContract precompiled callMap
        (EvmYul.UInt256.ofNat callGas) accessedSubstate childEnv).1 =
        false)
    (hGas :
      let target := EvmYul.AccountAddress.ofUInt256 address
      let callMap :=
        evmCallTransfer evm.accountMap evm.executionEnv.codeOwner target value
      let callGas :=
        EvmYul.EVM.Ccallgas target target value gas evm.accountMap
          evm.toMachineState evm.substate
      let charged : EvmYul.EVM.State :=
        { evm with
          gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
      let accessedSubstate :=
        (EvmYul.State.addAccessedAccount charged.toState target).substate
      let childEnv :=
        EvmYul.EVM.thetaCallExecutionEnv blobVersionedHashes
          evm.executionEnv.codeOwner evm.executionEnv.sender target
          (.Precompiled precompiled)
          (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice)
          value
          (charged.memory.readWithPadding inOffset.toNat inSize.toNat)
          (evm.executionEnv.depth + 1) evm.executionEnv.header
          evm.executionEnv.perm
      let precompileResult :=
        runPrecompiledContract precompiled callMap
          (EvmYul.UInt256.ofNat callGas) accessedSubstate childEnv
      let targetGas :=
        (charged.toMachineState.finishExternalCall precompileResult.2.2.2.2
          inOffset inSize outOffset outSize).gasAvailable +
          precompileResult.2.2.1
      gasAvailableRel
        (yul.toMachineState.finishExternalCall ByteArray.empty
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    CALLPrimitiveRel
      (stateRelConfig varStackRel terminalCfgRel revertCfgRel
        gasAvailableRel gasValueRel totalGasRel)
      fuel.succ fuel.succ.succ gasCost blobVersionedHashes yul evm store
      gas address value inOffset inSize outOffset outSize := by
  let target := EvmYul.AccountAddress.ofUInt256 address
  let callMap :=
    evmCallTransfer evm.accountMap evm.executionEnv.codeOwner target value
  let callGas :=
    EvmYul.EVM.Ccallgas target target value gas evm.accountMap
      evm.toMachineState evm.substate
  let charged : EvmYul.EVM.State :=
    { evm with gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
  let accessedSubstate :=
    (EvmYul.State.addAccessedAccount charged.toState target).substate
  let evmEnv :=
    EvmYul.EVM.thetaCallExecutionEnv blobVersionedHashes
      evm.executionEnv.codeOwner evm.executionEnv.sender target
      (.Precompiled precompiled)
      (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice)
      value
      (charged.memory.readWithPadding inOffset.toNat inSize.toNat)
      (evm.executionEnv.depth + 1) evm.executionEnv.header
      evm.executionEnv.perm
  let precompileResult :=
    runPrecompiledContract precompiled callMap
      (EvmYul.UInt256.ofNat callGas) accessedSubstate evmEnv
  let targetGas :=
    (charged.toMachineState.finishExternalCall precompileResult.2.2.2.2
      inOffset inSize outOffset outSize).gasAvailable +
      precompileResult.2.2.1
  let evmAfter : EvmYul.EVM.State :=
    { charged with
      toMachineState :=
        { charged.toMachineState.finishExternalCall
            precompileResult.2.2.2.2 inOffset inSize outOffset outSize with
          gasAvailable := targetGas }
      accountMap :=
        if precompileResult.2.1.isEmpty then evm.accountMap
        else precompileResult.2.1
      substate :=
        if precompileResult.2.1.isEmpty then accessedSubstate
        else precompileResult.2.2.2.1 }
  rcases
      primCall_CALL_precompiled_failure_rel_stateRelConfig
        hShared store hStaticAllowed hEnough hDepth hPrecompile hFailure hGas
    with
    ⟨hEvm, yulAfter, hYul, hRel⟩
  refine ⟨⟨0⟩, evmAfter, yulAfter, ?_, ?_, ?_⟩
  · simpa [evmAfter, targetGas, precompileResult, evmEnv,
      accessedSubstate, charged, callGas, callMap, target] using hEvm
  · exact hYul
  · simpa [evmAfter, targetGas, precompileResult, evmEnv,
      accessedSubstate, charged, callGas, callMap, target] using hRel

theorem primCall_CALL_ordinary_yul_of_dispatcher_restore
    {fuel : Nat}
    {yul yulChild yulAfter : EvmYul.SharedState .Yul}
    (store childStore : EvmYul.Yul.VarStore)
    {gas address value inOffset inSize outOffset outSize : EvmYul.UInt256}
    {yulRecipient : EvmYul.Account .Yul}
    {yulCallMap : EvmYul.AccountMap .Yul}
    {rets : List EvmYul.UInt256}
    (hStaticAllowed :
      ¬ (¬ yul.executionEnv.perm ∧ value ≠ ⟨0⟩))
    (hDepth : yul.executionEnv.depth < 1024)
    (hNotPrecompile :
      EvmYul.PrecompiledContract.ofAddress?
        (EvmYul.AccountAddress.ofUInt256 address) = none)
    (hFindYul :
      yul.accountMap.find? (EvmYul.AccountAddress.ofUInt256 address) =
        some yulRecipient)
    (hTransfer :
      EvmYul.Yul.callTransferAccountMap? yul.accountMap
          yul.executionEnv.codeOwner
          (EvmYul.AccountAddress.ofUInt256 address) value =
        some yulCallMap)
    (hCall :
      let callee := EvmYul.AccountAddress.ofUInt256 address
      let calldata :=
        yul.toMachineState.memory.readWithPadding
          inOffset.toNat inSize.toNat
      let callGas :=
        EvmYul.EVM.Ccallgas callee callee value gas yul.accountMap
          yul.toMachineState yul.substate
      let yulAccessed : EvmYul.SharedState .Yul :=
        { yul with
          toState := EvmYul.State.addAccessedAccount yul.toState callee }
      let initialShared : EvmYul.SharedState .Yul :=
        { yulAccessed with
          executionEnv :=
            { yulAccessed.executionEnv with
              calldata := calldata
              code := yulRecipient.code
              codeBytes := yulRecipient.codeBytes
              codeOwner := callee
              source := yul.executionEnv.codeOwner
              weiValue := value
              depth := yul.executionEnv.depth + 1 }
          toMachineState :=
            EvmYul.MachineState.freshExternalCall
              (EvmYul.UInt256.ofNat callGas)
          accountMap := yulCallMap }
      EvmYul.Yul.callDispatcher fuel (some yulRecipient.code)
          (.Ok initialShared default) =
        .ok (.Ok yulChild childStore, rets))
    (hRestore :
      EvmYul.Yul.restoreSuccessfulContractCallState
          (EvmYul.Yul.addAccessedAccount
            (.Ok yul store) (EvmYul.AccountAddress.ofUInt256 address))
          (.Ok yulChild childStore)
          store ByteArray.empty inOffset inSize outOffset outSize =
        .ok (.Ok yulAfter store, [⟨1⟩])) :
    EvmYul.Yul.primCall fuel.succ (.Ok yul store) .CALL
        [gas, address, value, inOffset, inSize, outOffset, outSize] =
      .ok (.Ok yulAfter store, [⟨1⟩]) := by
  dsimp at hCall
  let callee := EvmYul.AccountAddress.ofUInt256 address
  let calldata :=
    yul.toMachineState.memory.readWithPadding inOffset.toNat inSize.toNat
  let callGas :=
    EvmYul.EVM.Ccallgas callee callee value gas yul.accountMap
      yul.toMachineState yul.substate
  let yulAccessed : EvmYul.SharedState .Yul :=
    { yul with
      toState := EvmYul.State.addAccessedAccount yul.toState callee }
  let initialShared : EvmYul.SharedState .Yul :=
    { yulAccessed with
      executionEnv :=
        { yulAccessed.executionEnv with
          calldata := calldata
          code := yulRecipient.code
          codeBytes := yulRecipient.codeBytes
          codeOwner := callee
          source := yul.executionEnv.codeOwner
          weiValue := value
          depth := yul.executionEnv.depth + 1 }
      toMachineState :=
        EvmYul.MachineState.freshExternalCall
          (EvmYul.UInt256.ofNat callGas)
      accountMap := yulCallMap }
  have hCall' :
      EvmYul.Yul.callDispatcher fuel (some yulRecipient.code)
          (.Ok initialShared default) =
        .ok (.Ok yulChild childStore, rets) := by
    simpa [initialShared, yulAccessed, calldata, callGas, callee] using hCall
  have hCallExpanded := hCall
  simp [EvmYul.State.addAccessedAccount] at hCallExpanded
  have hNotDepthLimit : ¬ yul.executionEnv.depth ≥ 1024 := by
    omega
  have hStaticAllowed' :
      ¬ (yul.executionEnv.perm = false ∧ ¬ value = ⟨0⟩) := by
    intro hStatic
    exact hStaticAllowed (by simpa using hStatic)
  have hToExecute :
      EvmYul.toExecute .Yul yul.accountMap callee =
        .Code yulRecipient.code := by
    rw [EvmYul.toExecute, hNotPrecompile, hFindYul]
    rfl
  simpa [EvmYul.Yul.primCall, hStaticAllowed', hTransfer,
    hNotDepthLimit, hToExecute, hFindYul, hCallExpanded,
    initialShared, yulAccessed, calldata, callGas, callee,
    EvmYul.Yul.addAccessedAccount,
    EvmYul.State.addAccessedAccount,
    EvmYul.Yul.State.sharedState,
    EvmYul.Yul.State.executionEnv,
    EvmYul.Yul.State.setState, EvmYul.Yul.State.toState,
      EvmYul.Yul.State.toSharedState,
      EvmYul.Yul.State.toMachineState] using hRestore

theorem primCall_CALL_ordinary_yul_of_dispatcher_restore_of_branchFacts
    {fuel : Nat}
    {yul yulChild yulAfter : EvmYul.SharedState .Yul}
    {evm : EvmYul.EVM.State}
    (store childStore : EvmYul.Yul.VarStore)
    {gas address value inOffset inSize outOffset outSize : EvmYul.UInt256}
    {yulRecipient : EvmYul.Account .Yul}
    {yulCallMap : EvmYul.AccountMap .Yul}
    {evmRecipient : EvmYul.Account .EVM}
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    {rets : List EvmYul.UInt256}
    (hFacts :
      OrdinaryCALLBranchFacts yul evm address value yulRecipient
        yulCallMap evmRecipient program asm target)
    (hStaticAllowed :
      ¬ (¬ yul.executionEnv.perm ∧ value ≠ ⟨0⟩))
    (hDepth : yul.executionEnv.depth < 1024)
    (hNotPrecompile :
      EvmYul.PrecompiledContract.ofAddress?
        (EvmYul.AccountAddress.ofUInt256 address) = none)
    (hCall :
      let callee := EvmYul.AccountAddress.ofUInt256 address
      let calldata :=
        yul.toMachineState.memory.readWithPadding
          inOffset.toNat inSize.toNat
      let callGas :=
        EvmYul.EVM.Ccallgas callee callee value gas yul.accountMap
          yul.toMachineState yul.substate
      let yulAccessed : EvmYul.SharedState .Yul :=
        { yul with
          toState := EvmYul.State.addAccessedAccount yul.toState callee }
      let initialShared : EvmYul.SharedState .Yul :=
        { yulAccessed with
          executionEnv :=
            { yulAccessed.executionEnv with
              calldata := calldata
              code := yulRecipient.code
              codeBytes := yulRecipient.codeBytes
              codeOwner := callee
              source := yul.executionEnv.codeOwner
              weiValue := value
              depth := yul.executionEnv.depth + 1 }
          toMachineState :=
            EvmYul.MachineState.freshExternalCall
              (EvmYul.UInt256.ofNat callGas)
          accountMap := yulCallMap }
      EvmYul.Yul.callDispatcher fuel (some yulRecipient.code)
          (.Ok initialShared default) =
        .ok (.Ok yulChild childStore, rets))
    (hRestore :
      EvmYul.Yul.restoreSuccessfulContractCallState
          (EvmYul.Yul.addAccessedAccount
            (.Ok yul store) (EvmYul.AccountAddress.ofUInt256 address))
          (.Ok yulChild childStore)
          store ByteArray.empty inOffset inSize outOffset outSize =
        .ok (.Ok yulAfter store, [⟨1⟩])) :
    EvmYul.Yul.primCall fuel.succ (.Ok yul store) .CALL
        [gas, address, value, inOffset, inSize, outOffset, outSize] =
      .ok (.Ok yulAfter store, [⟨1⟩]) :=
  primCall_CALL_ordinary_yul_of_dispatcher_restore
    (fuel := fuel) store childStore hStaticAllowed hDepth hNotPrecompile
    hFacts.findYul hFacts.transfer hCall hRestore

theorem primCall_CALL_defaultCode_yul_of_restore
    {fuel : Nat}
    {yul yulAfter : EvmYul.SharedState .Yul}
    (store : EvmYul.Yul.VarStore)
    {gas address value inOffset inSize outOffset outSize : EvmYul.UInt256}
    {yulRecipient : EvmYul.Account .Yul}
    {yulCallMap : EvmYul.AccountMap .Yul}
    (hStaticAllowed :
      ¬ (¬ yul.executionEnv.perm ∧ value ≠ ⟨0⟩))
    (hDepth : yul.executionEnv.depth < 1024)
    (hNotPrecompile :
      EvmYul.PrecompiledContract.ofAddress?
        (EvmYul.AccountAddress.ofUInt256 address) = none)
    (hFindYul :
      yul.accountMap.find? (EvmYul.AccountAddress.ofUInt256 address) =
        some yulRecipient)
    (hCodeDefault : yulRecipient.code = default)
    (hTransfer :
      EvmYul.Yul.callTransferAccountMap? yul.accountMap
          yul.executionEnv.codeOwner
          (EvmYul.AccountAddress.ofUInt256 address) value =
        some yulCallMap)
    (hRestore :
      let callee := EvmYul.AccountAddress.ofUInt256 address
      let calldata :=
        yul.toMachineState.memory.readWithPadding
          inOffset.toNat inSize.toNat
      let callGas :=
        EvmYul.EVM.Ccallgas callee callee value gas yul.accountMap
          yul.toMachineState yul.substate
      let yulAccessed : EvmYul.SharedState .Yul :=
        { yul with
          toState := EvmYul.State.addAccessedAccount yul.toState callee }
      let initialShared : EvmYul.SharedState .Yul :=
        { yulAccessed with
          executionEnv :=
            { yulAccessed.executionEnv with
              calldata := calldata
              code := yulRecipient.code
              codeBytes := yulRecipient.codeBytes
              codeOwner := callee
              source := yul.executionEnv.codeOwner
              weiValue := value
              depth := yul.executionEnv.depth + 1 }
          toMachineState :=
            EvmYul.MachineState.freshExternalCall
              (EvmYul.UInt256.ofNat callGas)
          accountMap := yulCallMap }
      EvmYul.Yul.restoreSuccessfulContractCallState
          (EvmYul.Yul.addAccessedAccount (.Ok yul store) callee)
          (.Ok initialShared default)
          store ByteArray.empty inOffset inSize outOffset outSize =
        .ok (.Ok yulAfter store, [⟨1⟩])) :
    EvmYul.Yul.primCall fuel.succ.succ.succ.succ.succ.succ
        (.Ok yul store) .CALL
        [gas, address, value, inOffset, inSize, outOffset, outSize] =
      .ok (.Ok yulAfter store, [⟨1⟩]) := by
  let callee := EvmYul.AccountAddress.ofUInt256 address
  let calldata :=
    yul.toMachineState.memory.readWithPadding inOffset.toNat inSize.toNat
  let callGas :=
    EvmYul.EVM.Ccallgas callee callee value gas yul.accountMap
      yul.toMachineState yul.substate
  let yulAccessed : EvmYul.SharedState .Yul :=
    { yul with
      toState := EvmYul.State.addAccessedAccount yul.toState callee }
  let initialShared : EvmYul.SharedState .Yul :=
    { yulAccessed with
      executionEnv :=
        { yulAccessed.executionEnv with
          calldata := calldata
          code := yulRecipient.code
          codeBytes := yulRecipient.codeBytes
          codeOwner := callee
          source := yul.executionEnv.codeOwner
          weiValue := value
          depth := yul.executionEnv.depth + 1 }
      toMachineState :=
        EvmYul.MachineState.freshExternalCall
          (EvmYul.UInt256.ofNat callGas)
      accountMap := yulCallMap }
  have hCall :
      EvmYul.Yul.callDispatcher fuel.succ.succ.succ.succ.succ
          (some yulRecipient.code) (.Ok initialShared default) =
        .ok (.Ok initialShared default, []) := by
    have hInitialCode :
        initialShared.executionEnv.code = (default : AstContract) := by
      simp [initialShared, hCodeDefault]
    simpa [hCodeDefault] using
      callDispatcher_defaultCode_ok
        (fuel := fuel) (shared := initialShared)
        (store := default) hInitialCode
  exact
    primCall_CALL_ordinary_yul_of_dispatcher_restore
      (fuel := fuel.succ.succ.succ.succ.succ)
      store default hStaticAllowed hDepth hNotPrecompile hFindYul
      hTransfer
      (by
        dsimp [callee, calldata, callGas, yulAccessed, initialShared]
          at hCall ⊢
        simpa using hCall)
      (by
        dsimp [callee, calldata, callGas, yulAccessed, initialShared]
          at hRestore ⊢
        simpa using hRestore)

theorem primCall_CALL_existingDefaultCode_emptyReturn_rel_stateRelConfig
    {varStackRel : Reference.VarStackRel}
    {terminalCfgRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop}
    {revertCfgRel : Reference.State → EVMState → Prop}
    {gasAvailableRel : Word → Word → Prop}
    {gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm}
    {totalGasRel : Nat → Nat → Prop}
    {fuel gasCost : Nat}
    {blobVersionedHashes : List ByteArray}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.EVM.State}
    (hShared :
      Reference.SharedStateRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        yul evm.toSharedState)
    (store : EvmYul.Yul.VarStore)
    {gas address value inOffset inSize outOffset outSize : EvmYul.UInt256}
    {yulRecipient : EvmYul.Account .Yul}
    {evmRecipient : EvmYul.Account .EVM}
    (hStaticAllowed :
      ¬ (¬ yul.executionEnv.perm ∧ value ≠ ⟨0⟩))
    (hEnough :
      value ≤
        (evm.accountMap.find? evm.executionEnv.codeOwner |>.option ⟨0⟩
          (·.balance)))
    (hDepth : evm.executionEnv.depth < 1024)
    (hNotPrecompile :
      EvmYul.PrecompiledContract.ofAddress?
        (EvmYul.AccountAddress.ofUInt256 address) = none)
    (hFindYul :
      yul.accountMap.find? (EvmYul.AccountAddress.ofUInt256 address) =
        some yulRecipient)
    (hCodeDefault : yulRecipient.code = default)
    (hFindEvm :
      evm.accountMap.find? (EvmYul.AccountAddress.ofUInt256 address) =
        some evmRecipient)
    (hEvmCodeDefault : evmRecipient.code = default)
    (hGas :
      let target := EvmYul.AccountAddress.ofUInt256 address
      let callGas :=
        EvmYul.EVM.Ccallgas target target value gas evm.accountMap
          evm.toMachineState evm.substate
      let charged : EvmYul.EVM.State :=
        { evm with
          gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
      let targetGas :=
        (charged.toMachineState.finishExternalCall ByteArray.empty
          inOffset inSize outOffset outSize).gasAvailable +
          EvmYul.UInt256.ofNat callGas
      gasAvailableRel
        (yul.toMachineState.finishExternalCall ByteArray.empty
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    let target := EvmYul.AccountAddress.ofUInt256 address
    let callMap :=
      evmCallTransfer evm.accountMap evm.executionEnv.codeOwner target value
    let callGas :=
      EvmYul.EVM.Ccallgas target target value gas evm.accountMap
        evm.toMachineState evm.substate
    let charged : EvmYul.EVM.State :=
      { evm with gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
    let targetGas :=
      (charged.toMachineState.finishExternalCall ByteArray.empty
        inOffset inSize outOffset outSize).gasAvailable +
        EvmYul.UInt256.ofNat callGas
    let evmAfter : EvmYul.EVM.State :=
      { charged with
        toMachineState :=
          { charged.toMachineState.finishExternalCall ByteArray.empty
              inOffset inSize outOffset outSize with
            gasAvailable := targetGas }
        accountMap :=
          if callMap.isEmpty then evm.accountMap else callMap
        substate :=
          (EvmYul.State.addAccessedAccount charged.toState target).substate }
    EvmYul.EVM.call fuel.succ.succ.succ.succ.succ.succ gasCost
        blobVersionedHashes gas
        (EvmYul.UInt256.ofNat evm.executionEnv.codeOwner) address address
        value value inOffset inSize outOffset outSize evm.executionEnv.perm
        evm =
      .ok (⟨1⟩, evmAfter) ∧
      ∃ yulAfter,
        EvmYul.Yul.primCall fuel.succ.succ.succ.succ.succ.succ
            (.Ok yul store) .CALL
            [gas, address, value, inOffset, inSize, outOffset, outSize] =
          .ok (.Ok yulAfter store, [⟨1⟩]) ∧
        Reference.SharedStateRel
          (stateRelConfig varStackRel terminalCfgRel revertCfgRel
            gasAvailableRel gasValueRel totalGasRel)
          yulAfter evmAfter.toSharedState := by
  dsimp at hGas ⊢
  let cfg :=
    stateRelConfig varStackRel terminalCfgRel revertCfgRel
      gasAvailableRel gasValueRel totalGasRel
  let target := EvmYul.AccountAddress.ofUInt256 address
  let callMap :=
    evmCallTransfer evm.accountMap evm.executionEnv.codeOwner target value
  let callGas :=
    EvmYul.EVM.Ccallgas target target value gas evm.accountMap
      evm.toMachineState evm.substate
  let charged : EvmYul.EVM.State :=
    { evm with gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
  let targetGas :=
    (charged.toMachineState.finishExternalCall ByteArray.empty
      inOffset inSize outOffset outSize).gasAvailable +
      EvmYul.UInt256.ofNat callGas
  let yulAccessed : EvmYul.SharedState .Yul :=
    { yul with
      toState := EvmYul.State.addAccessedAccount yul.toState target }
  let evmAccessed : EvmYul.SharedState .EVM :=
    { evm.toSharedState with
      toState := EvmYul.State.addAccessedAccount evm.toState target }
  have hWorld :
      CompiledAccountMapRel yul.accountMap evm.accountMap :=
    compiledAccountMapRel_of_sharedStateRel_stateRelConfig hShared
  have hOwner :
      yul.executionEnv.codeOwner = evm.executionEnv.codeOwner := by
    rcases hShared with ⟨hChain, _hMachine⟩
    simpa using hChain.executionEnv.codeOwner
  rcases
      hWorld.callTransferAccountMap?_of_evm_enough_find_yul_nonempty
        (source := yul.executionEnv.codeOwner)
        (recipient := target)
        (value := value)
        hFindYul (by simpa [hOwner] using hEnough) with
    ⟨yulCallMap, hTransfer, hYulNonempty, hEvmNonempty, hTransferRel⟩
  let calldata :=
    yul.toMachineState.memory.readWithPadding inOffset.toNat inSize.toNat
  let yulCallGas :=
    EvmYul.EVM.Ccallgas target target value gas yul.accountMap
      yul.toMachineState yul.substate
  let initialShared : EvmYul.SharedState .Yul :=
    { yulAccessed with
      executionEnv :=
        { yulAccessed.executionEnv with
          calldata := calldata
          code := yulRecipient.code
          codeBytes := yulRecipient.codeBytes
          codeOwner := target
          source := yul.executionEnv.codeOwner
          weiValue := value
          depth := yul.executionEnv.depth + 1 }
      toMachineState :=
        EvmYul.MachineState.freshExternalCall
          (EvmYul.UInt256.ofNat yulCallGas)
      accountMap := yulCallMap }
  have hEvmNonempty' : callMap.isEmpty = false := by
    simpa [callMap, hOwner] using hEvmNonempty
  have hTransferRel' : CompiledAccountMapRel yulCallMap callMap := by
    simpa [callMap, target, hOwner] using hTransferRel
  have hEvm :
      EvmYul.EVM.call fuel.succ.succ.succ.succ.succ.succ gasCost
          blobVersionedHashes gas
          (EvmYul.UInt256.ofNat evm.executionEnv.codeOwner) address address
          value value inOffset inSize outOffset outSize evm.executionEnv.perm
          evm =
        .ok (⟨1⟩,
          { charged with
            toMachineState :=
              { charged.toMachineState.finishExternalCall ByteArray.empty
                  inOffset inSize outOffset outSize with
                gasAvailable := targetGas }
            accountMap :=
              if callMap.isEmpty then evm.accountMap else callMap
            substate :=
              (EvmYul.State.addAccessedAccount charged.toState target).substate }) := by
    simpa [target, callMap, callGas, charged, targetGas] using
      EVM_call_existingDefaultCode_success_eq
        (fuel := fuel.succ) (gasCost := gasCost)
        (blobVersionedHashes := blobVersionedHashes)
        (evm := evm) (gas := gas) (address := address)
        (value := value) (inOffset := inOffset) (inSize := inSize)
        (outOffset := outOffset) (outSize := outSize)
        hEnough hDepth hNotPrecompile hFindEvm hEvmCodeDefault
  have hParentRel :
      Reference.SharedStateRel cfg yulAccessed evmAccessed := by
    simpa [cfg, yulAccessed, evmAccessed, target] using
      sharedStateRel_addAccessedAccount hShared target
  have hAccountMap :
      cfg.accountMapRel
        (if initialShared.accountMap.isEmpty then yulAccessed.accountMap
          else initialShared.accountMap)
        (if callMap.isEmpty then evmAccessed.accountMap else callMap) := by
    have hCfgTransfer :
        cfg.accountMapRel yulCallMap callMap :=
      stateRelConfig_accountMapRel_of_compiledAccountMapRel hTransferRel'
    simpa [cfg, initialShared, yulAccessed, evmAccessed, hYulNonempty,
      hEvmNonempty'] using hCfgTransfer
  have hSubstate :
      (if initialShared.accountMap.isEmpty then yulAccessed.substate
        else initialShared.substate) =
        if callMap.isEmpty then evmAccessed.substate
        else evmAccessed.substate := by
    rcases hShared with ⟨hChain, _hMachine⟩
    simp [initialShared, yulAccessed, evmAccessed, callMap, target,
      hYulNonempty, hEvmNonempty', EvmYul.State.addAccessedAccount,
      EvmYul.Substate.addAccessedAccount, hChain.substate]
  have hCreated :
      initialShared.createdAccounts = evm.createdAccounts := by
    rcases hShared with ⟨hChain, _hMachine⟩
    simpa [initialShared, yulAccessed] using hChain.createdAccounts
  have hGas' :
      cfg.gasAvailableRel
        (yulAccessed.toMachineState.finishExternalCall ByteArray.empty
          inOffset inSize outOffset outSize).gasAvailable
        targetGas := by
    simpa [cfg, yulAccessed, targetGas, charged, callGas, callMap,
      target] using hGas
  rcases
      restoreSuccessfulContractCallState_ok_rel
        hParentRel store default store
        (yulChild := initialShared)
        (evmChildAccountMap := callMap)
        (evmChildSubstate := evmAccessed.substate)
        (evmChildCreated := evm.createdAccounts)
        (targetGas := targetGas)
        hAccountMap hSubstate hCreated ByteArray.empty
        inOffset inSize outOffset outSize hGas' with
    ⟨yulAfter, hRestore, hRel⟩
  have hPrim :
      EvmYul.Yul.primCall fuel.succ.succ.succ.succ.succ.succ
          (.Ok yul store) .CALL
          [gas, address, value, inOffset, inSize, outOffset, outSize] =
        .ok (.Ok yulAfter store, [⟨1⟩]) := by
    exact
      primCall_CALL_defaultCode_yul_of_restore
        (fuel := fuel) store hStaticAllowed (by
          have hDepthEq :
              yul.executionEnv.depth = evm.executionEnv.depth := by
            rcases hShared with ⟨hChain, _hMachine⟩
            simpa using hChain.executionEnv.depth
          omega)
        hNotPrecompile hFindYul hCodeDefault hTransfer
        (by
          dsimp [target, calldata, yulCallGas, yulAccessed, initialShared]
            at hRestore ⊢
          simpa using hRestore)
  refine ⟨hEvm, yulAfter, hPrim, ?_⟩
  simpa [cfg, target, callMap, charged, targetGas, evmAccessed,
    EvmYul.State.addAccessedAccount, hEvmNonempty'] using hRel

theorem CALLPrimitiveRel.existingDefaultCode_stateRelConfig
    {varStackRel : Reference.VarStackRel}
    {terminalCfgRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop}
    {revertCfgRel : Reference.State → EVMState → Prop}
    {gasAvailableRel : Word → Word → Prop}
    {gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm}
    {totalGasRel : Nat → Nat → Prop}
    {fuel gasCost : Nat}
    {blobVersionedHashes : List ByteArray}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.EVM.State}
    (hShared :
      Reference.SharedStateRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        yul evm.toSharedState)
    (store : EvmYul.Yul.VarStore)
    {gas address value inOffset inSize outOffset outSize : EvmYul.UInt256}
    {yulRecipient : EvmYul.Account .Yul}
    {evmRecipient : EvmYul.Account .EVM}
    (hStaticAllowed :
      ¬ (¬ yul.executionEnv.perm ∧ value ≠ ⟨0⟩))
    (hEnough :
      value ≤
        (evm.accountMap.find? evm.executionEnv.codeOwner |>.option ⟨0⟩
          (·.balance)))
    (hDepth : evm.executionEnv.depth < 1024)
    (hNotPrecompile :
      EvmYul.PrecompiledContract.ofAddress?
        (EvmYul.AccountAddress.ofUInt256 address) = none)
    (hFindYul :
      yul.accountMap.find? (EvmYul.AccountAddress.ofUInt256 address) =
        some yulRecipient)
    (hCodeDefault : yulRecipient.code = default)
    (hFindEvm :
      evm.accountMap.find? (EvmYul.AccountAddress.ofUInt256 address) =
        some evmRecipient)
    (hEvmCodeDefault : evmRecipient.code = default)
    (hGas :
      let target := EvmYul.AccountAddress.ofUInt256 address
      let callGas :=
        EvmYul.EVM.Ccallgas target target value gas evm.accountMap
          evm.toMachineState evm.substate
      let charged : EvmYul.EVM.State :=
        { evm with
          gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
      let targetGas :=
        (charged.toMachineState.finishExternalCall ByteArray.empty
          inOffset inSize outOffset outSize).gasAvailable +
          EvmYul.UInt256.ofNat callGas
      gasAvailableRel
        (yul.toMachineState.finishExternalCall ByteArray.empty
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    CALLPrimitiveRel
      (stateRelConfig varStackRel terminalCfgRel revertCfgRel
        gasAvailableRel gasValueRel totalGasRel)
      fuel.succ.succ.succ.succ.succ.succ
      fuel.succ.succ.succ.succ.succ.succ
      gasCost blobVersionedHashes yul evm store
      gas address value inOffset inSize outOffset outSize := by
  let target := EvmYul.AccountAddress.ofUInt256 address
  let callMap :=
    evmCallTransfer evm.accountMap evm.executionEnv.codeOwner target value
  let callGas :=
    EvmYul.EVM.Ccallgas target target value gas evm.accountMap
      evm.toMachineState evm.substate
  let charged : EvmYul.EVM.State :=
    { evm with gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
  let targetGas :=
    (charged.toMachineState.finishExternalCall ByteArray.empty
      inOffset inSize outOffset outSize).gasAvailable +
      EvmYul.UInt256.ofNat callGas
  let evmAfter : EvmYul.EVM.State :=
    { charged with
      toMachineState :=
        { charged.toMachineState.finishExternalCall ByteArray.empty
            inOffset inSize outOffset outSize with
          gasAvailable := targetGas }
      accountMap :=
        if callMap.isEmpty then evm.accountMap else callMap
      substate :=
        (EvmYul.State.addAccessedAccount charged.toState target).substate }
  rcases
      primCall_CALL_existingDefaultCode_emptyReturn_rel_stateRelConfig
        hShared store hStaticAllowed hEnough hDepth hNotPrecompile hFindYul
        hCodeDefault hFindEvm hEvmCodeDefault hGas with
    ⟨hEvm, yulAfter, hYul, hRel⟩
  refine ⟨⟨1⟩, evmAfter, yulAfter, ?_, ?_, ?_⟩
  · simpa [evmAfter, targetGas, charged, callGas, callMap, target] using hEvm
  · exact hYul
  · simpa [evmAfter, targetGas, charged, callGas, callMap, target] using hRel

theorem primCall_CALL_ordinary_yul_of_dispatcher_yulHalt_restore
    {fuel : Nat}
    {yul yulChild yulAfter : EvmYul.SharedState .Yul}
    (store childStore : EvmYul.Yul.VarStore)
    {gas address value inOffset inSize outOffset outSize : EvmYul.UInt256}
    {yulRecipient : EvmYul.Account .Yul}
    {yulCallMap : EvmYul.AccountMap .Yul}
    {haltValue : EvmYul.UInt256}
    (hStaticAllowed :
      ¬ (¬ yul.executionEnv.perm ∧ value ≠ ⟨0⟩))
    (hDepth : yul.executionEnv.depth < 1024)
    (hNotPrecompile :
      EvmYul.PrecompiledContract.ofAddress?
        (EvmYul.AccountAddress.ofUInt256 address) = none)
    (hFindYul :
      yul.accountMap.find? (EvmYul.AccountAddress.ofUInt256 address) =
        some yulRecipient)
    (hTransfer :
      EvmYul.Yul.callTransferAccountMap? yul.accountMap
          yul.executionEnv.codeOwner
          (EvmYul.AccountAddress.ofUInt256 address) value =
        some yulCallMap)
    (hCall :
      let callee := EvmYul.AccountAddress.ofUInt256 address
      let calldata :=
        yul.toMachineState.memory.readWithPadding
          inOffset.toNat inSize.toNat
      let callGas :=
        EvmYul.EVM.Ccallgas callee callee value gas yul.accountMap
          yul.toMachineState yul.substate
      let yulAccessed : EvmYul.SharedState .Yul :=
        { yul with
          toState := EvmYul.State.addAccessedAccount yul.toState callee }
      let initialShared : EvmYul.SharedState .Yul :=
        { yulAccessed with
          executionEnv :=
            { yulAccessed.executionEnv with
              calldata := calldata
              code := yulRecipient.code
              codeBytes := yulRecipient.codeBytes
              codeOwner := callee
              source := yul.executionEnv.codeOwner
              weiValue := value
              depth := yul.executionEnv.depth + 1 }
          toMachineState :=
            EvmYul.MachineState.freshExternalCall
              (EvmYul.UInt256.ofNat callGas)
          accountMap := yulCallMap }
      EvmYul.Yul.callDispatcher fuel (some yulRecipient.code)
          (.Ok initialShared default) =
        .error (.YulHalt (.Ok yulChild childStore) haltValue))
    (hRestore :
      EvmYul.Yul.restoreSuccessfulContractCallState
          (EvmYul.Yul.addAccessedAccount
            (.Ok yul store) (EvmYul.AccountAddress.ofUInt256 address))
          (.Ok yulChild childStore)
          store yulChild.toMachineState.H_return
          inOffset inSize outOffset outSize =
        .ok (.Ok yulAfter store, [⟨1⟩])) :
    EvmYul.Yul.primCall fuel.succ (.Ok yul store) .CALL
        [gas, address, value, inOffset, inSize, outOffset, outSize] =
      .ok (.Ok yulAfter store, [⟨1⟩]) := by
  dsimp at hCall
  let callee := EvmYul.AccountAddress.ofUInt256 address
  let calldata :=
    yul.toMachineState.memory.readWithPadding inOffset.toNat inSize.toNat
  let callGas :=
    EvmYul.EVM.Ccallgas callee callee value gas yul.accountMap
      yul.toMachineState yul.substate
  let yulAccessed : EvmYul.SharedState .Yul :=
    { yul with
      toState := EvmYul.State.addAccessedAccount yul.toState callee }
  let initialShared : EvmYul.SharedState .Yul :=
    { yulAccessed with
      executionEnv :=
        { yulAccessed.executionEnv with
          calldata := calldata
          code := yulRecipient.code
          codeBytes := yulRecipient.codeBytes
          codeOwner := callee
          source := yul.executionEnv.codeOwner
          weiValue := value
          depth := yul.executionEnv.depth + 1 }
      toMachineState :=
        EvmYul.MachineState.freshExternalCall
          (EvmYul.UInt256.ofNat callGas)
      accountMap := yulCallMap }
  have hCallExpanded := hCall
  simp [EvmYul.State.addAccessedAccount] at hCallExpanded
  have hNotDepthLimit : ¬ yul.executionEnv.depth ≥ 1024 := by
    omega
  have hStaticAllowed' :
      ¬ (yul.executionEnv.perm = false ∧ ¬ value = ⟨0⟩) := by
    intro hStatic
    exact hStaticAllowed (by simpa using hStatic)
  have hToExecute :
      EvmYul.toExecute .Yul yul.accountMap callee =
        .Code yulRecipient.code := by
    rw [EvmYul.toExecute, hNotPrecompile, hFindYul]
    rfl
  simpa [EvmYul.Yul.primCall, hStaticAllowed', hTransfer,
    hNotDepthLimit, hToExecute, hFindYul, hCallExpanded,
    initialShared, yulAccessed, calldata, callGas, callee,
    EvmYul.Yul.addAccessedAccount,
    EvmYul.State.addAccessedAccount,
    EvmYul.Yul.State.sharedState,
    EvmYul.Yul.State.executionEnv,
    EvmYul.Yul.State.setState, EvmYul.Yul.State.toState,
    EvmYul.Yul.State.toSharedState,
    EvmYul.Yul.State.toMachineState] using hRestore

theorem primCall_CALL_ordinary_yul_of_dispatcher_yulHalt_restore_of_branchFacts
    {fuel : Nat}
    {yul yulChild yulAfter : EvmYul.SharedState .Yul}
    {evm : EvmYul.EVM.State}
    (store childStore : EvmYul.Yul.VarStore)
    {gas address value inOffset inSize outOffset outSize : EvmYul.UInt256}
    {yulRecipient : EvmYul.Account .Yul}
    {yulCallMap : EvmYul.AccountMap .Yul}
    {evmRecipient : EvmYul.Account .EVM}
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    {haltValue : EvmYul.UInt256}
    (hFacts :
      OrdinaryCALLBranchFacts yul evm address value yulRecipient
        yulCallMap evmRecipient program asm target)
    (hStaticAllowed :
      ¬ (¬ yul.executionEnv.perm ∧ value ≠ ⟨0⟩))
    (hDepth : yul.executionEnv.depth < 1024)
    (hNotPrecompile :
      EvmYul.PrecompiledContract.ofAddress?
        (EvmYul.AccountAddress.ofUInt256 address) = none)
    (hCall :
      let callee := EvmYul.AccountAddress.ofUInt256 address
      let calldata :=
        yul.toMachineState.memory.readWithPadding
          inOffset.toNat inSize.toNat
      let callGas :=
        EvmYul.EVM.Ccallgas callee callee value gas yul.accountMap
          yul.toMachineState yul.substate
      let yulAccessed : EvmYul.SharedState .Yul :=
        { yul with
          toState := EvmYul.State.addAccessedAccount yul.toState callee }
      let initialShared : EvmYul.SharedState .Yul :=
        { yulAccessed with
          executionEnv :=
            { yulAccessed.executionEnv with
              calldata := calldata
              code := yulRecipient.code
              codeBytes := yulRecipient.codeBytes
              codeOwner := callee
              source := yul.executionEnv.codeOwner
              weiValue := value
              depth := yul.executionEnv.depth + 1 }
          toMachineState :=
            EvmYul.MachineState.freshExternalCall
              (EvmYul.UInt256.ofNat callGas)
          accountMap := yulCallMap }
      EvmYul.Yul.callDispatcher fuel (some yulRecipient.code)
          (.Ok initialShared default) =
        .error (.YulHalt (.Ok yulChild childStore) haltValue))
    (hRestore :
      EvmYul.Yul.restoreSuccessfulContractCallState
          (EvmYul.Yul.addAccessedAccount
            (.Ok yul store) (EvmYul.AccountAddress.ofUInt256 address))
          (.Ok yulChild childStore)
          store yulChild.toMachineState.H_return
          inOffset inSize outOffset outSize =
        .ok (.Ok yulAfter store, [⟨1⟩])) :
    EvmYul.Yul.primCall fuel.succ (.Ok yul store) .CALL
        [gas, address, value, inOffset, inSize, outOffset, outSize] =
      .ok (.Ok yulAfter store, [⟨1⟩]) :=
  primCall_CALL_ordinary_yul_of_dispatcher_yulHalt_restore
    (fuel := fuel) store childStore hStaticAllowed hDepth hNotPrecompile
    hFacts.findYul hFacts.transfer hCall hRestore

theorem primCall_CALL_ordinary_yul_of_dispatcher_revert
    {fuel : Nat}
    {yul yulChild yulAfter : EvmYul.SharedState .Yul}
    (store childStore : EvmYul.Yul.VarStore)
    {gas address value inOffset inSize outOffset outSize : EvmYul.UInt256}
    {yulRecipient : EvmYul.Account .Yul}
    {yulCallMap : EvmYul.AccountMap .Yul}
    (hStaticAllowed :
      ¬ (¬ yul.executionEnv.perm ∧ value ≠ ⟨0⟩))
    (hDepth : yul.executionEnv.depth < 1024)
    (hNotPrecompile :
      EvmYul.PrecompiledContract.ofAddress?
        (EvmYul.AccountAddress.ofUInt256 address) = none)
    (hFindYul :
      yul.accountMap.find? (EvmYul.AccountAddress.ofUInt256 address) =
        some yulRecipient)
    (hTransfer :
      EvmYul.Yul.callTransferAccountMap? yul.accountMap
          yul.executionEnv.codeOwner
          (EvmYul.AccountAddress.ofUInt256 address) value =
        some yulCallMap)
    (hCall :
      let callee := EvmYul.AccountAddress.ofUInt256 address
      let calldata :=
        yul.toMachineState.memory.readWithPadding
          inOffset.toNat inSize.toNat
      let callGas :=
        EvmYul.EVM.Ccallgas callee callee value gas yul.accountMap
          yul.toMachineState yul.substate
      let yulAccessed : EvmYul.SharedState .Yul :=
        { yul with
          toState := EvmYul.State.addAccessedAccount yul.toState callee }
      let initialShared : EvmYul.SharedState .Yul :=
        { yulAccessed with
          executionEnv :=
            { yulAccessed.executionEnv with
              calldata := calldata
              code := yulRecipient.code
              codeBytes := yulRecipient.codeBytes
              codeOwner := callee
              source := yul.executionEnv.codeOwner
              weiValue := value
              depth := yul.executionEnv.depth + 1 }
          toMachineState :=
            EvmYul.MachineState.freshExternalCall
              (EvmYul.UInt256.ofNat callGas)
          accountMap := yulCallMap }
      EvmYul.Yul.callDispatcher fuel (some yulRecipient.code)
          (.Ok initialShared default) =
        .error (.Revert (.Ok yulChild childStore)))
    (hRestore :
      EvmYul.Yul.restoreRevertedContractCallState
          (EvmYul.Yul.addAccessedAccount
            (.Ok yul store) (EvmYul.AccountAddress.ofUInt256 address))
          (.Ok yulChild childStore)
          inOffset inSize outOffset outSize =
        .ok (.Ok yulAfter store, [⟨0⟩])) :
    EvmYul.Yul.primCall fuel.succ (.Ok yul store) .CALL
        [gas, address, value, inOffset, inSize, outOffset, outSize] =
      .ok (.Ok yulAfter store, [⟨0⟩]) := by
  dsimp at hCall
  let callee := EvmYul.AccountAddress.ofUInt256 address
  let calldata :=
    yul.toMachineState.memory.readWithPadding inOffset.toNat inSize.toNat
  let callGas :=
    EvmYul.EVM.Ccallgas callee callee value gas yul.accountMap
      yul.toMachineState yul.substate
  let yulAccessed : EvmYul.SharedState .Yul :=
    { yul with
      toState := EvmYul.State.addAccessedAccount yul.toState callee }
  let initialShared : EvmYul.SharedState .Yul :=
    { yulAccessed with
      executionEnv :=
        { yulAccessed.executionEnv with
          calldata := calldata
          code := yulRecipient.code
          codeBytes := yulRecipient.codeBytes
          codeOwner := callee
          source := yul.executionEnv.codeOwner
          weiValue := value
          depth := yul.executionEnv.depth + 1 }
      toMachineState :=
        EvmYul.MachineState.freshExternalCall
          (EvmYul.UInt256.ofNat callGas)
      accountMap := yulCallMap }
  have hCallExpanded := hCall
  simp [EvmYul.State.addAccessedAccount] at hCallExpanded
  have hNotDepthLimit : ¬ yul.executionEnv.depth ≥ 1024 := by
    omega
  have hStaticAllowed' :
      ¬ (yul.executionEnv.perm = false ∧ ¬ value = ⟨0⟩) := by
    intro hStatic
    exact hStaticAllowed (by simpa using hStatic)
  have hToExecute :
      EvmYul.toExecute .Yul yul.accountMap callee =
        .Code yulRecipient.code := by
    rw [EvmYul.toExecute, hNotPrecompile, hFindYul]
    rfl
  simpa [EvmYul.Yul.primCall, hStaticAllowed', hTransfer,
    hNotDepthLimit, hToExecute, hFindYul, hCallExpanded,
    initialShared, yulAccessed, calldata, callGas, callee,
    EvmYul.Yul.addAccessedAccount,
    EvmYul.State.addAccessedAccount,
    EvmYul.Yul.State.sharedState,
    EvmYul.Yul.State.executionEnv,
    EvmYul.Yul.State.setState, EvmYul.Yul.State.toState,
    EvmYul.Yul.State.toSharedState,
    EvmYul.Yul.State.toMachineState] using hRestore

theorem primCall_CALL_ordinary_yul_of_dispatcher_revert_of_branchFacts
    {fuel : Nat}
    {yul yulChild yulAfter : EvmYul.SharedState .Yul}
    {evm : EvmYul.EVM.State}
    (store childStore : EvmYul.Yul.VarStore)
    {gas address value inOffset inSize outOffset outSize : EvmYul.UInt256}
    {yulRecipient : EvmYul.Account .Yul}
    {yulCallMap : EvmYul.AccountMap .Yul}
    {evmRecipient : EvmYul.Account .EVM}
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    (hFacts :
      OrdinaryCALLBranchFacts yul evm address value yulRecipient
        yulCallMap evmRecipient program asm target)
    (hStaticAllowed :
      ¬ (¬ yul.executionEnv.perm ∧ value ≠ ⟨0⟩))
    (hDepth : yul.executionEnv.depth < 1024)
    (hNotPrecompile :
      EvmYul.PrecompiledContract.ofAddress?
        (EvmYul.AccountAddress.ofUInt256 address) = none)
    (hCall :
      let callee := EvmYul.AccountAddress.ofUInt256 address
      let calldata :=
        yul.toMachineState.memory.readWithPadding
          inOffset.toNat inSize.toNat
      let callGas :=
        EvmYul.EVM.Ccallgas callee callee value gas yul.accountMap
          yul.toMachineState yul.substate
      let yulAccessed : EvmYul.SharedState .Yul :=
        { yul with
          toState := EvmYul.State.addAccessedAccount yul.toState callee }
      let initialShared : EvmYul.SharedState .Yul :=
        { yulAccessed with
          executionEnv :=
            { yulAccessed.executionEnv with
              calldata := calldata
              code := yulRecipient.code
              codeBytes := yulRecipient.codeBytes
              codeOwner := callee
              source := yul.executionEnv.codeOwner
              weiValue := value
              depth := yul.executionEnv.depth + 1 }
          toMachineState :=
            EvmYul.MachineState.freshExternalCall
              (EvmYul.UInt256.ofNat callGas)
          accountMap := yulCallMap }
      EvmYul.Yul.callDispatcher fuel (some yulRecipient.code)
          (.Ok initialShared default) =
        .error (.Revert (.Ok yulChild childStore)))
    (hRestore :
      EvmYul.Yul.restoreRevertedContractCallState
          (EvmYul.Yul.addAccessedAccount
            (.Ok yul store) (EvmYul.AccountAddress.ofUInt256 address))
          (.Ok yulChild childStore)
          inOffset inSize outOffset outSize =
        .ok (.Ok yulAfter store, [⟨0⟩])) :
    EvmYul.Yul.primCall fuel.succ (.Ok yul store) .CALL
        [gas, address, value, inOffset, inSize, outOffset, outSize] =
      .ok (.Ok yulAfter store, [⟨0⟩]) :=
  primCall_CALL_ordinary_yul_of_dispatcher_revert
    (fuel := fuel) store childStore hStaticAllowed hDepth hNotPrecompile
    hFacts.findYul hFacts.transfer hCall hRestore

theorem primCall_CALL_ordinary_runningSuccess_of_theta_restore
    {cfg : Reference.StateRelConfig}
    {referenceFuel evmThetaFuel gasCost : Nat}
    {blobVersionedHashes : List ByteArray}
    {yul yulChild yulAfter : EvmYul.SharedState .Yul}
    {evm evmChild : EvmYul.EVM.State}
    (store childStore : EvmYul.Yul.VarStore)
    {gas address value inOffset inSize outOffset outSize : EvmYul.UInt256}
    {yulRecipient : EvmYul.Account .Yul}
    {yulCallMap : EvmYul.AccountMap .Yul}
    {evmRecipient : EvmYul.Account .EVM}
    {target : Assembly.TargetProgram}
    {rets : List EvmYul.UInt256}
    {output : ByteArray}
    (hShared : Reference.SharedStateRel cfg yul evm.toSharedState)
    (hStaticAllowed :
      ¬ (¬ yul.executionEnv.perm ∧ value ≠ ⟨0⟩))
    (hEnough :
      value ≤
        (evm.accountMap.find? evm.executionEnv.codeOwner |>.option ⟨0⟩
          (·.balance)))
    (hDepth : evm.executionEnv.depth < 1024)
    (hNotPrecompile :
      EvmYul.PrecompiledContract.ofAddress?
        (EvmYul.AccountAddress.ofUInt256 address) = none)
    (hFindYul :
      yul.accountMap.find? (EvmYul.AccountAddress.ofUInt256 address) =
        some yulRecipient)
    (hTransfer :
      EvmYul.Yul.callTransferAccountMap? yul.accountMap
          yul.executionEnv.codeOwner
          (EvmYul.AccountAddress.ofUInt256 address) value =
        some yulCallMap)
    (hFindEvm :
      evm.accountMap.find? (EvmYul.AccountAddress.ofUInt256 address) =
        some evmRecipient)
    (hCode :
      evmRecipient.code = Assembly.Bytecode.encodeTarget target)
    (hCall :
      let callee := EvmYul.AccountAddress.ofUInt256 address
      let calldata :=
        yul.toMachineState.memory.readWithPadding
          inOffset.toNat inSize.toNat
      let callGas :=
        EvmYul.EVM.Ccallgas callee callee value gas yul.accountMap
          yul.toMachineState yul.substate
      let yulAccessed : EvmYul.SharedState .Yul :=
        { yul with
          toState := EvmYul.State.addAccessedAccount yul.toState callee }
      let initialShared : EvmYul.SharedState .Yul :=
        { yulAccessed with
          executionEnv :=
            { yulAccessed.executionEnv with
              calldata := calldata
              code := yulRecipient.code
              codeBytes := yulRecipient.codeBytes
              codeOwner := callee
              source := yul.executionEnv.codeOwner
              weiValue := value
              depth := yul.executionEnv.depth + 1 }
          toMachineState :=
            EvmYul.MachineState.freshExternalCall
              (EvmYul.UInt256.ofNat callGas)
          accountMap := yulCallMap }
      EvmYul.Yul.callDispatcher referenceFuel (some yulRecipient.code)
          (.Ok initialShared default) =
        .ok (.Ok yulChild childStore, rets))
    (hTheta :
      let callee := EvmYul.AccountAddress.ofUInt256 address
      let callGas :=
        EvmYul.EVM.Ccallgas callee callee value gas evm.accountMap
          evm.toMachineState evm.substate
      EvmYul.EVM.Θ evmThetaFuel blobVersionedHashes
          evm.createdAccounts evm.genesisBlockHeader evm.blocks
          evm.accountMap evm.σ₀
          { totalGasUsedInBlock := evm.totalGasUsedInBlock
            transactionReceipts := evm.transactionReceipts }
          (EvmYul.State.addAccessedAccount evm.toState callee).substate
          evm.executionEnv.codeOwner evm.executionEnv.sender callee
          (.Code (Assembly.Bytecode.encodeTarget target))
          (EvmYul.UInt256.ofNat callGas)
          (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice)
          value value
          (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
          (evm.executionEnv.depth + 1) evm.executionEnv.header
          evm.executionEnv.perm =
        .ok (evmChild.createdAccounts,
          if evmChild.accountMap.isEmpty then evm.accountMap
          else evmChild.accountMap,
          evmChild.gasAvailable,
          if evmChild.accountMap.isEmpty then
            (EvmYul.State.addAccessedAccount evm.toState callee).substate
          else evmChild.substate,
          true, output))
    (hRestore :
      EvmYul.Yul.restoreSuccessfulContractCallState
          (EvmYul.Yul.addAccessedAccount
            (.Ok yul store) (EvmYul.AccountAddress.ofUInt256 address))
          (.Ok yulChild childStore)
          store ByteArray.empty inOffset inSize outOffset outSize =
        .ok (.Ok yulAfter store, [⟨1⟩]))
    (hRel :
      let callee := EvmYul.AccountAddress.ofUInt256 address
      let charged : EvmYul.EVM.State :=
        { evm with
          gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
      let targetGas :=
        (charged.toMachineState.finishExternalCall output
          inOffset inSize outOffset outSize).gasAvailable +
          evmChild.gasAvailable
      Reference.SharedStateRel cfg yulAfter
        ({ charged with
          toMachineState :=
            { charged.toMachineState.finishExternalCall output
                inOffset inSize outOffset outSize with
              gasAvailable := targetGas }
          accountMap :=
            if evmChild.accountMap.isEmpty then evm.accountMap
            else evmChild.accountMap
          substate :=
            if evmChild.accountMap.isEmpty then
              (EvmYul.State.addAccessedAccount evm.toState callee).substate
            else evmChild.substate
          createdAccounts := evmChild.createdAccounts } :
          EvmYul.EVM.State).toSharedState) :
    let callee := EvmYul.AccountAddress.ofUInt256 address
    let charged : EvmYul.EVM.State :=
      { evm with
        gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
    let targetGas :=
      (charged.toMachineState.finishExternalCall output
        inOffset inSize outOffset outSize).gasAvailable +
        evmChild.gasAvailable
    let evmAfter : EvmYul.EVM.State :=
      { charged with
        toMachineState :=
          { charged.toMachineState.finishExternalCall output
              inOffset inSize outOffset outSize with
            gasAvailable := targetGas }
        accountMap :=
          if evmChild.accountMap.isEmpty then evm.accountMap
          else evmChild.accountMap
        substate :=
          if evmChild.accountMap.isEmpty then
            (EvmYul.State.addAccessedAccount evm.toState callee).substate
          else evmChild.substate
        createdAccounts := evmChild.createdAccounts }
    EvmYul.EVM.call evmThetaFuel.succ gasCost blobVersionedHashes gas
        (EvmYul.UInt256.ofNat evm.executionEnv.codeOwner) address address
        value value inOffset inSize outOffset outSize evm.executionEnv.perm
        evm =
      .ok (⟨1⟩, evmAfter) ∧
    EvmYul.Yul.primCall referenceFuel.succ (.Ok yul store) .CALL
        [gas, address, value, inOffset, inSize, outOffset, outSize] =
      .ok (.Ok yulAfter store, [⟨1⟩]) ∧
    Reference.SharedStateRel cfg yulAfter evmAfter.toSharedState := by
  dsimp at hTheta hRel ⊢
  let callee := EvmYul.AccountAddress.ofUInt256 address
  let charged : EvmYul.EVM.State :=
    { evm with
      gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
  let targetGas :=
    (charged.toMachineState.finishExternalCall output
      inOffset inSize outOffset outSize).gasAvailable +
      evmChild.gasAvailable
  let evmAfter : EvmYul.EVM.State :=
    { charged with
      toMachineState :=
        { charged.toMachineState.finishExternalCall output
            inOffset inSize outOffset outSize with
          gasAvailable := targetGas }
      accountMap :=
        if evmChild.accountMap.isEmpty then evm.accountMap
        else evmChild.accountMap
      substate :=
        if evmChild.accountMap.isEmpty then
          (EvmYul.State.addAccessedAccount evm.toState callee).substate
        else evmChild.substate
      createdAccounts := evmChild.createdAccounts }
  have hYulDepth : yul.executionEnv.depth < 1024 := by
    have hDepthEq :
        yul.executionEnv.depth = evm.executionEnv.depth := by
      rcases hShared with ⟨hChain, _hMachine⟩
      simpa using hChain.executionEnv.depth
    omega
  have hYulCall :
      EvmYul.Yul.primCall referenceFuel.succ (.Ok yul store) .CALL
          [gas, address, value, inOffset, inSize, outOffset, outSize] =
        .ok (.Ok yulAfter store, [⟨1⟩]) :=
    primCall_CALL_ordinary_yul_of_dispatcher_restore
      (fuel := referenceFuel) store childStore
      hStaticAllowed hYulDepth hNotPrecompile hFindYul hTransfer hCall
      hRestore
  have hEvmCall :=
    EVM_call_ordinaryCode_of_theta_eq
      (fuel := evmThetaFuel)
      (gasCost := gasCost)
      (blobVersionedHashes := blobVersionedHashes)
      (evm := evm)
      (gas := gas) (address := address) (value := value)
      (inOffset := inOffset) (inSize := inSize)
      (outOffset := outOffset) (outSize := outSize)
      (calleeAccount := evmRecipient) (target := target)
      hEnough hDepth hNotPrecompile hFindEvm hCode hTheta
  refine ⟨?_, hYulCall, ?_⟩
  · simpa [callee, charged, targetGas, evmAfter] using hEvmCall
  · simpa [callee, charged, targetGas, evmAfter] using hRel

theorem primCall_CALL_ordinary_haltedSuccess_of_theta_restore
    {cfg : Reference.StateRelConfig}
    {referenceFuel evmThetaFuel gasCost : Nat}
    {blobVersionedHashes : List ByteArray}
    {yul yulChild yulAfter : EvmYul.SharedState .Yul}
    {evm evmChild : EvmYul.EVM.State}
    (store childStore : EvmYul.Yul.VarStore)
    {gas address value inOffset inSize outOffset outSize : EvmYul.UInt256}
    {yulRecipient : EvmYul.Account .Yul}
    {yulCallMap : EvmYul.AccountMap .Yul}
    {evmRecipient : EvmYul.Account .EVM}
    {target : Assembly.TargetProgram}
    {haltValue : EvmYul.UInt256}
    {output : ByteArray}
    (hShared : Reference.SharedStateRel cfg yul evm.toSharedState)
    (hStaticAllowed :
      ¬ (¬ yul.executionEnv.perm ∧ value ≠ ⟨0⟩))
    (hEnough :
      value ≤
        (evm.accountMap.find? evm.executionEnv.codeOwner |>.option ⟨0⟩
          (·.balance)))
    (hDepth : evm.executionEnv.depth < 1024)
    (hNotPrecompile :
      EvmYul.PrecompiledContract.ofAddress?
        (EvmYul.AccountAddress.ofUInt256 address) = none)
    (hFindYul :
      yul.accountMap.find? (EvmYul.AccountAddress.ofUInt256 address) =
        some yulRecipient)
    (hTransfer :
      EvmYul.Yul.callTransferAccountMap? yul.accountMap
          yul.executionEnv.codeOwner
          (EvmYul.AccountAddress.ofUInt256 address) value =
        some yulCallMap)
    (hFindEvm :
      evm.accountMap.find? (EvmYul.AccountAddress.ofUInt256 address) =
        some evmRecipient)
    (hCode :
      evmRecipient.code = Assembly.Bytecode.encodeTarget target)
    (hCall :
      let callee := EvmYul.AccountAddress.ofUInt256 address
      let calldata :=
        yul.toMachineState.memory.readWithPadding
          inOffset.toNat inSize.toNat
      let callGas :=
        EvmYul.EVM.Ccallgas callee callee value gas yul.accountMap
          yul.toMachineState yul.substate
      let yulAccessed : EvmYul.SharedState .Yul :=
        { yul with
          toState := EvmYul.State.addAccessedAccount yul.toState callee }
      let initialShared : EvmYul.SharedState .Yul :=
        { yulAccessed with
          executionEnv :=
            { yulAccessed.executionEnv with
              calldata := calldata
              code := yulRecipient.code
              codeBytes := yulRecipient.codeBytes
              codeOwner := callee
              source := yul.executionEnv.codeOwner
              weiValue := value
              depth := yul.executionEnv.depth + 1 }
          toMachineState :=
            EvmYul.MachineState.freshExternalCall
              (EvmYul.UInt256.ofNat callGas)
          accountMap := yulCallMap }
      EvmYul.Yul.callDispatcher referenceFuel (some yulRecipient.code)
          (.Ok initialShared default) =
        .error (.YulHalt (.Ok yulChild childStore) haltValue))
    (hTheta :
      let callee := EvmYul.AccountAddress.ofUInt256 address
      let callGas :=
        EvmYul.EVM.Ccallgas callee callee value gas evm.accountMap
          evm.toMachineState evm.substate
      EvmYul.EVM.Θ evmThetaFuel blobVersionedHashes
          evm.createdAccounts evm.genesisBlockHeader evm.blocks
          evm.accountMap evm.σ₀
          { totalGasUsedInBlock := evm.totalGasUsedInBlock
            transactionReceipts := evm.transactionReceipts }
          (EvmYul.State.addAccessedAccount evm.toState callee).substate
          evm.executionEnv.codeOwner evm.executionEnv.sender callee
          (.Code (Assembly.Bytecode.encodeTarget target))
          (EvmYul.UInt256.ofNat callGas)
          (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice)
          value value
          (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
          (evm.executionEnv.depth + 1) evm.executionEnv.header
          evm.executionEnv.perm =
        .ok (evmChild.createdAccounts,
          if evmChild.accountMap.isEmpty then evm.accountMap
          else evmChild.accountMap,
          evmChild.gasAvailable,
          if evmChild.accountMap.isEmpty then
            (EvmYul.State.addAccessedAccount evm.toState callee).substate
          else evmChild.substate,
          true, output))
    (hRestore :
      EvmYul.Yul.restoreSuccessfulContractCallState
          (EvmYul.Yul.addAccessedAccount
            (.Ok yul store) (EvmYul.AccountAddress.ofUInt256 address))
          (.Ok yulChild childStore)
          store yulChild.toMachineState.H_return
          inOffset inSize outOffset outSize =
        .ok (.Ok yulAfter store, [⟨1⟩]))
    (hRel :
      let callee := EvmYul.AccountAddress.ofUInt256 address
      let charged : EvmYul.EVM.State :=
        { evm with
          gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
      let targetGas :=
        (charged.toMachineState.finishExternalCall output
          inOffset inSize outOffset outSize).gasAvailable +
          evmChild.gasAvailable
      Reference.SharedStateRel cfg yulAfter
        ({ charged with
          toMachineState :=
            { charged.toMachineState.finishExternalCall output
                inOffset inSize outOffset outSize with
              gasAvailable := targetGas }
          accountMap :=
            if evmChild.accountMap.isEmpty then evm.accountMap
            else evmChild.accountMap
          substate :=
            if evmChild.accountMap.isEmpty then
              (EvmYul.State.addAccessedAccount evm.toState callee).substate
            else evmChild.substate
          createdAccounts := evmChild.createdAccounts } :
          EvmYul.EVM.State).toSharedState) :
    let callee := EvmYul.AccountAddress.ofUInt256 address
    let charged : EvmYul.EVM.State :=
      { evm with
        gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
    let targetGas :=
      (charged.toMachineState.finishExternalCall output
        inOffset inSize outOffset outSize).gasAvailable +
        evmChild.gasAvailable
    let evmAfter : EvmYul.EVM.State :=
      { charged with
        toMachineState :=
          { charged.toMachineState.finishExternalCall output
              inOffset inSize outOffset outSize with
            gasAvailable := targetGas }
        accountMap :=
          if evmChild.accountMap.isEmpty then evm.accountMap
          else evmChild.accountMap
        substate :=
          if evmChild.accountMap.isEmpty then
            (EvmYul.State.addAccessedAccount evm.toState callee).substate
          else evmChild.substate
        createdAccounts := evmChild.createdAccounts }
    EvmYul.EVM.call evmThetaFuel.succ gasCost blobVersionedHashes gas
        (EvmYul.UInt256.ofNat evm.executionEnv.codeOwner) address address
        value value inOffset inSize outOffset outSize evm.executionEnv.perm
        evm =
      .ok (⟨1⟩, evmAfter) ∧
    EvmYul.Yul.primCall referenceFuel.succ (.Ok yul store) .CALL
        [gas, address, value, inOffset, inSize, outOffset, outSize] =
      .ok (.Ok yulAfter store, [⟨1⟩]) ∧
    Reference.SharedStateRel cfg yulAfter evmAfter.toSharedState := by
  dsimp at hTheta hRel ⊢
  let callee := EvmYul.AccountAddress.ofUInt256 address
  let charged : EvmYul.EVM.State :=
    { evm with
      gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
  let targetGas :=
    (charged.toMachineState.finishExternalCall output
      inOffset inSize outOffset outSize).gasAvailable +
      evmChild.gasAvailable
  let evmAfter : EvmYul.EVM.State :=
    { charged with
      toMachineState :=
        { charged.toMachineState.finishExternalCall output
            inOffset inSize outOffset outSize with
          gasAvailable := targetGas }
      accountMap :=
        if evmChild.accountMap.isEmpty then evm.accountMap
        else evmChild.accountMap
      substate :=
        if evmChild.accountMap.isEmpty then
          (EvmYul.State.addAccessedAccount evm.toState callee).substate
        else evmChild.substate
      createdAccounts := evmChild.createdAccounts }
  have hYulDepth : yul.executionEnv.depth < 1024 := by
    have hDepthEq :
        yul.executionEnv.depth = evm.executionEnv.depth := by
      rcases hShared with ⟨hChain, _hMachine⟩
      simpa using hChain.executionEnv.depth
    omega
  have hYulCall :
      EvmYul.Yul.primCall referenceFuel.succ (.Ok yul store) .CALL
          [gas, address, value, inOffset, inSize, outOffset, outSize] =
        .ok (.Ok yulAfter store, [⟨1⟩]) :=
    primCall_CALL_ordinary_yul_of_dispatcher_yulHalt_restore
      (fuel := referenceFuel) store childStore
      hStaticAllowed hYulDepth hNotPrecompile hFindYul hTransfer hCall
      hRestore
  have hEvmCall :=
    EVM_call_ordinaryCode_of_theta_eq
      (fuel := evmThetaFuel)
      (gasCost := gasCost)
      (blobVersionedHashes := blobVersionedHashes)
      (evm := evm)
      (gas := gas) (address := address) (value := value)
      (inOffset := inOffset) (inSize := inSize)
      (outOffset := outOffset) (outSize := outSize)
      (calleeAccount := evmRecipient) (target := target)
      hEnough hDepth hNotPrecompile hFindEvm hCode hTheta
  refine ⟨?_, hYulCall, ?_⟩
  · simpa [callee, charged, targetGas, evmAfter] using hEvmCall
  · simpa [callee, charged, targetGas, evmAfter] using hRel

theorem primCall_CALL_ordinary_revert_of_theta_restore
    {cfg : Reference.StateRelConfig}
    {referenceFuel evmThetaFuel gasCost : Nat}
    {blobVersionedHashes : List ByteArray}
    {yul yulChild yulAfter : EvmYul.SharedState .Yul}
    {evm : EvmYul.EVM.State}
    (store childStore : EvmYul.Yul.VarStore)
    {gas address value inOffset inSize outOffset outSize : EvmYul.UInt256}
    {yulRecipient : EvmYul.Account .Yul}
    {yulCallMap : EvmYul.AccountMap .Yul}
    {evmRecipient : EvmYul.Account .EVM}
    {target : Assembly.TargetProgram}
    {returnedGas : EvmYul.UInt256}
    {output : ByteArray}
    (hShared : Reference.SharedStateRel cfg yul evm.toSharedState)
    (hStaticAllowed :
      ¬ (¬ yul.executionEnv.perm ∧ value ≠ ⟨0⟩))
    (hEnough :
      value ≤
        (evm.accountMap.find? evm.executionEnv.codeOwner |>.option ⟨0⟩
          (·.balance)))
    (hDepth : evm.executionEnv.depth < 1024)
    (hNotPrecompile :
      EvmYul.PrecompiledContract.ofAddress?
        (EvmYul.AccountAddress.ofUInt256 address) = none)
    (hFindYul :
      yul.accountMap.find? (EvmYul.AccountAddress.ofUInt256 address) =
        some yulRecipient)
    (hTransfer :
      EvmYul.Yul.callTransferAccountMap? yul.accountMap
          yul.executionEnv.codeOwner
          (EvmYul.AccountAddress.ofUInt256 address) value =
        some yulCallMap)
    (hFindEvm :
      evm.accountMap.find? (EvmYul.AccountAddress.ofUInt256 address) =
        some evmRecipient)
    (hCode :
      evmRecipient.code = Assembly.Bytecode.encodeTarget target)
    (hCall :
      let callee := EvmYul.AccountAddress.ofUInt256 address
      let calldata :=
        yul.toMachineState.memory.readWithPadding
          inOffset.toNat inSize.toNat
      let callGas :=
        EvmYul.EVM.Ccallgas callee callee value gas yul.accountMap
          yul.toMachineState yul.substate
      let yulAccessed : EvmYul.SharedState .Yul :=
        { yul with
          toState := EvmYul.State.addAccessedAccount yul.toState callee }
      let initialShared : EvmYul.SharedState .Yul :=
        { yulAccessed with
          executionEnv :=
            { yulAccessed.executionEnv with
              calldata := calldata
              code := yulRecipient.code
              codeBytes := yulRecipient.codeBytes
              codeOwner := callee
              source := yul.executionEnv.codeOwner
              weiValue := value
              depth := yul.executionEnv.depth + 1 }
          toMachineState :=
            EvmYul.MachineState.freshExternalCall
              (EvmYul.UInt256.ofNat callGas)
          accountMap := yulCallMap }
      EvmYul.Yul.callDispatcher referenceFuel (some yulRecipient.code)
          (.Ok initialShared default) =
        .error (.Revert (.Ok yulChild childStore)))
    (hTheta :
      let callee := EvmYul.AccountAddress.ofUInt256 address
      let callGas :=
        EvmYul.EVM.Ccallgas callee callee value gas evm.accountMap
          evm.toMachineState evm.substate
      EvmYul.EVM.Θ evmThetaFuel blobVersionedHashes
          evm.createdAccounts evm.genesisBlockHeader evm.blocks
          evm.accountMap evm.σ₀
          { totalGasUsedInBlock := evm.totalGasUsedInBlock
            transactionReceipts := evm.transactionReceipts }
          (EvmYul.State.addAccessedAccount evm.toState callee).substate
          evm.executionEnv.codeOwner evm.executionEnv.sender callee
          (.Code (Assembly.Bytecode.encodeTarget target))
          (EvmYul.UInt256.ofNat callGas)
          (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice)
          value value
          (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
          (evm.executionEnv.depth + 1) evm.executionEnv.header
          evm.executionEnv.perm =
        .ok (evm.createdAccounts, evm.accountMap, returnedGas,
          (EvmYul.State.addAccessedAccount evm.toState callee).substate,
          false, output))
    (hRestore :
      EvmYul.Yul.restoreRevertedContractCallState
          (EvmYul.Yul.addAccessedAccount
            (.Ok yul store) (EvmYul.AccountAddress.ofUInt256 address))
          (.Ok yulChild childStore)
          inOffset inSize outOffset outSize =
        .ok (.Ok yulAfter store, [⟨0⟩]))
    (hRel :
      let callee := EvmYul.AccountAddress.ofUInt256 address
      let charged : EvmYul.EVM.State :=
        { evm with
          gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
      let targetGas :=
        (charged.toMachineState.finishExternalCall output
          inOffset inSize outOffset outSize).gasAvailable +
          returnedGas
      Reference.SharedStateRel cfg yulAfter
        ({ charged with
          toMachineState :=
            { charged.toMachineState.finishExternalCall output
                inOffset inSize outOffset outSize with
              gasAvailable := targetGas }
          accountMap := evm.accountMap
          substate :=
            (EvmYul.State.addAccessedAccount evm.toState callee).substate
          createdAccounts := evm.createdAccounts } :
          EvmYul.EVM.State).toSharedState) :
    let callee := EvmYul.AccountAddress.ofUInt256 address
    let charged : EvmYul.EVM.State :=
      { evm with
        gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
    let targetGas :=
      (charged.toMachineState.finishExternalCall output
        inOffset inSize outOffset outSize).gasAvailable +
        returnedGas
    let evmAfter : EvmYul.EVM.State :=
      { charged with
        toMachineState :=
          { charged.toMachineState.finishExternalCall output
              inOffset inSize outOffset outSize with
            gasAvailable := targetGas }
        accountMap := evm.accountMap
        substate :=
          (EvmYul.State.addAccessedAccount evm.toState callee).substate
        createdAccounts := evm.createdAccounts }
    EvmYul.EVM.call evmThetaFuel.succ gasCost blobVersionedHashes gas
        (EvmYul.UInt256.ofNat evm.executionEnv.codeOwner) address address
        value value inOffset inSize outOffset outSize evm.executionEnv.perm
        evm =
      .ok (⟨0⟩, evmAfter) ∧
    EvmYul.Yul.primCall referenceFuel.succ (.Ok yul store) .CALL
        [gas, address, value, inOffset, inSize, outOffset, outSize] =
      .ok (.Ok yulAfter store, [⟨0⟩]) ∧
    Reference.SharedStateRel cfg yulAfter evmAfter.toSharedState := by
  dsimp at hTheta hRel ⊢
  let callee := EvmYul.AccountAddress.ofUInt256 address
  let charged : EvmYul.EVM.State :=
    { evm with
      gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
  let targetGas :=
    (charged.toMachineState.finishExternalCall output
      inOffset inSize outOffset outSize).gasAvailable +
      returnedGas
  let evmAfter : EvmYul.EVM.State :=
    { charged with
      toMachineState :=
        { charged.toMachineState.finishExternalCall output
            inOffset inSize outOffset outSize with
          gasAvailable := targetGas }
      accountMap := evm.accountMap
      substate :=
        (EvmYul.State.addAccessedAccount evm.toState callee).substate
      createdAccounts := evm.createdAccounts }
  have hYulDepth : yul.executionEnv.depth < 1024 := by
    have hDepthEq :
        yul.executionEnv.depth = evm.executionEnv.depth := by
      rcases hShared with ⟨hChain, _hMachine⟩
      simpa using hChain.executionEnv.depth
    omega
  have hYulCall :
      EvmYul.Yul.primCall referenceFuel.succ (.Ok yul store) .CALL
          [gas, address, value, inOffset, inSize, outOffset, outSize] =
        .ok (.Ok yulAfter store, [⟨0⟩]) :=
    primCall_CALL_ordinary_yul_of_dispatcher_revert
      (fuel := referenceFuel) store childStore
      hStaticAllowed hYulDepth hNotPrecompile hFindYul hTransfer hCall
      hRestore
  have hEvmCall :=
    EVM_call_ordinaryCode_of_theta_eq
      (fuel := evmThetaFuel)
      (gasCost := gasCost)
      (blobVersionedHashes := blobVersionedHashes)
      (evm := evm)
      (gas := gas) (address := address) (value := value)
      (inOffset := inOffset) (inSize := inSize)
      (outOffset := outOffset) (outSize := outSize)
      (calleeAccount := evmRecipient) (target := target)
      hEnough hDepth hNotPrecompile hFindEvm hCode hTheta
  refine ⟨?_, hYulCall, ?_⟩
  · simpa [callee, charged, targetGas, evmAfter] using hEvmCall
  · simpa [callee, charged, targetGas, evmAfter] using hRel

theorem primCall_CALL_ordinary_runningSuccess_rel_of_installed_childDispatcher_afterAccess_withTargetGas
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {varStackRel : Reference.VarStackRel}
    {terminalCfgRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop}
    {revertCfgRel : Reference.State → EVMState → Prop}
    {gasAvailableRel : Word → Word → Prop}
    {gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm}
    {totalGasRel : Nat → Nat → Prop}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {referenceFuel sourceFuel gasCost : Nat}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.EVM.State}
    (hShared :
      Reference.SharedStateRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        yul evm.toSharedState)
    (store childStore : EvmYul.Yul.VarStore)
    {gas address value inOffset inSize outOffset outSize : EvmYul.UInt256}
    {yulRecipient : EvmYul.Account .Yul}
    {yulCallMap : EvmYul.AccountMap .Yul}
    {evmRecipient : EvmYul.Account .EVM}
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    {yulChild : EvmYul.SharedState .Yul}
    {rets : List EvmYul.UInt256}
    {sourceOutcome : Objects.Source.Outcome}
    (hStaticAllowed :
      ¬ (¬ yul.executionEnv.perm ∧ value ≠ ⟨0⟩))
    (hEnough :
      value ≤
        (evm.accountMap.find? evm.executionEnv.codeOwner |>.option ⟨0⟩
          (·.balance)))
    (hDepth : evm.executionEnv.depth < 1024)
    (hNotPrecompile :
      EvmYul.PrecompiledContract.ofAddress?
        (EvmYul.AccountAddress.ofUInt256 address) = none)
    (hFacts :
      OrdinaryCALLBranchFacts yul evm address value yulRecipient
        yulCallMap evmRecipient program asm target)
    (hCall :
      let callee := EvmYul.AccountAddress.ofUInt256 address
      let calldata :=
        yul.toMachineState.memory.readWithPadding
          inOffset.toNat inSize.toNat
      let callGas :=
        EvmYul.EVM.Ccallgas callee callee value gas yul.accountMap
          yul.toMachineState yul.substate
      let yulAccessed : EvmYul.SharedState .Yul :=
        { yul with
          toState := EvmYul.State.addAccessedAccount yul.toState callee }
      let initialShared : EvmYul.SharedState .Yul :=
        { yulAccessed with
          executionEnv :=
            { yulAccessed.executionEnv with
              calldata := calldata
              code := program.contract
              codeBytes := yulRecipient.codeBytes
              codeOwner := callee
              source := yul.executionEnv.codeOwner
              weiValue := value
              depth := yul.executionEnv.depth + 1 }
          toMachineState :=
            EvmYul.MachineState.freshExternalCall
              (EvmYul.UInt256.ofNat callGas)
          accountMap := yulCallMap }
      EvmYul.Yul.callDispatcher referenceFuel (some program.contract)
          (.Ok initialShared default) =
        .ok (.Ok yulChild childStore, rets))
    (hSourceRun :
      let callee := EvmYul.AccountAddress.ofUInt256 address
      let callGas :=
        EvmYul.EVM.Ccallgas callee callee value gas evm.accountMap
          evm.toMachineState evm.substate
      SourceLowered.run prim sourceFuel program
          (Assembly.GasAware.installCodeAndGas target callGas
            (thetaCodeRawInitialState target callGas
              yul.executionEnv.blobVersionedHashes evm.createdAccounts
              evm.genesisBlockHeader evm.blocks evm.accountMap evm.σ₀
              { totalGasUsedInBlock := evm.totalGasUsedInBlock
                transactionReceipts := evm.transactionReceipts }
              (EvmYul.State.addAccessedAccount evm.toState callee).substate
              evm.executionEnv.codeOwner evm.executionEnv.sender callee
              (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice) value value
              (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
              (evm.executionEnv.depth + 1) evm.executionEnv.header
              evm.executionEnv.perm)) =
        .ok sourceOutcome)
    (hOutcomeRel :
      let callee := EvmYul.AccountAddress.ofUInt256 address
      let calldata :=
        yul.toMachineState.memory.readWithPadding
          inOffset.toNat inSize.toNat
      let callGas :=
        EvmYul.EVM.Ccallgas callee callee value gas yul.accountMap
          yul.toMachineState yul.substate
      let yulAccessed : EvmYul.SharedState .Yul :=
        { yul with
          toState := EvmYul.State.addAccessedAccount yul.toState callee }
      let initialShared : EvmYul.SharedState .Yul :=
        { yulAccessed with
          executionEnv :=
            { yulAccessed.executionEnv with
              calldata := calldata
              code := program.contract
              codeBytes := yulRecipient.codeBytes
              codeOwner := callee
              source := yul.executionEnv.codeOwner
              weiValue := value
              depth := yul.executionEnv.depth + 1 }
          toMachineState :=
            EvmYul.MachineState.freshExternalCall
              (EvmYul.UInt256.ofNat callGas)
          accountMap := yulCallMap }
      Program.RecursiveBridgeSemanticContracts.dispatcherOutcomeRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        terminalRel revertRel program (.Ok initialShared default)
        (.regular (.Ok yulChild childStore)) sourceOutcome)
    (hTargetGasForX :
      let callee := EvmYul.AccountAddress.ofUInt256 address
      let callGas :=
        EvmYul.EVM.Ccallgas callee callee value gas evm.accountMap
          evm.toMachineState evm.substate
      ∀ {targetFuel targetOutcome},
        Assembly.Preservation.BlockTraceResult asm target targetFuel
          (Assembly.GasAware.installCodeAndGas target callGas
            (thetaCodeRawInitialState target callGas
              yul.executionEnv.blobVersionedHashes evm.createdAccounts
              evm.genesisBlockHeader evm.blocks evm.accountMap evm.σ₀
              { totalGasUsedInBlock := evm.totalGasUsedInBlock
                transactionReceipts := evm.transactionReceipts }
              (EvmYul.State.addAccessedAccount evm.toState callee).substate
              evm.executionEnv.codeOwner evm.executionEnv.sender callee
              (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice) value value
              (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
              (evm.executionEnv.depth + 1) evm.executionEnv.header
              evm.executionEnv.perm))
          targetOutcome →
        Assembly.GasAware.XResultPreconditionAssumptions target
          (Assembly.GasAware.installCodeAndGas target callGas
            (thetaCodeRawInitialState target callGas
              yul.executionEnv.blobVersionedHashes evm.createdAccounts
              evm.genesisBlockHeader evm.blocks evm.accountMap evm.σ₀
              { totalGasUsedInBlock := evm.totalGasUsedInBlock
                transactionReceipts := evm.transactionReceipts }
              (EvmYul.State.addAccessedAccount evm.toState callee).substate
              evm.executionEnv.codeOwner evm.executionEnv.sender callee
              (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice) value value
              (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
              (evm.executionEnv.depth + 1) evm.executionEnv.header
              evm.executionEnv.perm))
          targetOutcome)
    (hGasBound :
      let callee := EvmYul.AccountAddress.ofUInt256 address
      let callGas :=
        EvmYul.EVM.Ccallgas callee callee value gas evm.accountMap
          evm.toMachineState evm.substate
      ∀ {targetFuel targetOutcome}
        (hTrace :
          Assembly.Preservation.BlockTraceResult asm target targetFuel
            (Assembly.GasAware.installCodeAndGas target callGas
              (thetaCodeRawInitialState target callGas
                yul.executionEnv.blobVersionedHashes evm.createdAccounts
                evm.genesisBlockHeader evm.blocks evm.accountMap evm.σ₀
                { totalGasUsedInBlock := evm.totalGasUsedInBlock
                  transactionReceipts := evm.transactionReceipts }
                (EvmYul.State.addAccessedAccount evm.toState callee).substate
                evm.executionEnv.codeOwner evm.executionEnv.sender callee
                (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice) value value
                (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
                (evm.executionEnv.depth + 1) evm.executionEnv.header
                evm.executionEnv.perm))
            targetOutcome),
        (hTargetGasForX hTrace).gasBound ≤ callGas)
    (hUInt256 :
      EvmYul.EVM.Ccallgas (EvmYul.AccountAddress.ofUInt256 address)
          (EvmYul.AccountAddress.ofUInt256 address) value gas
          evm.accountMap evm.toMachineState evm.substate <
        EvmYul.UInt256.size)
    (hTargetChildGas :
      ∀ {targetChild}, SourceLowered.WholeProgramOutcomeRel sourceOutcome
          (.running targetChild) →
        gasAvailableRel yulChild.toMachineState.gasAvailable
          targetChild.gasAvailable)
    (hEvmChildGas :
      ∀ {targetOutcome evmChild output},
        SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome →
          Assembly.GasAware.XResultAgrees targetOutcome
            (.success evmChild output) →
          gasAvailableRel yulChild.toMachineState.gasAvailable
            evmChild.gasAvailable)
    (hReturnedGas :
      ∀ {targetOutcome evmChild output},
        SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome →
          Assembly.GasAware.XResultAgrees targetOutcome
            (.success evmChild output) →
          let charged : EvmYul.EVM.State :=
            { evm with
              gasAvailable :=
                evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
          gasAvailableRel
            (yul.toMachineState.finishExternalCall ByteArray.empty
              inOffset inSize outOffset outSize).gasAvailable
            ((charged.toMachineState.finishExternalCall output
                inOffset inSize outOffset outSize).gasAvailable +
              evmChild.gasAvailable)) :
    ∃ (evmFuel : Nat) (targetChild evmChild : EVMState)
      (output : ByteArray) (yulAfter : EvmYul.SharedState .Yul),
      let callee := EvmYul.AccountAddress.ofUInt256 address
      let charged : EvmYul.EVM.State :=
        { evm with
          gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
      let targetGas :=
        (charged.toMachineState.finishExternalCall output
          inOffset inSize outOffset outSize).gasAvailable +
          evmChild.gasAvailable
      let evmAfter : EvmYul.EVM.State :=
        { charged with
          toMachineState :=
            { charged.toMachineState.finishExternalCall output
                inOffset inSize outOffset outSize with
              gasAvailable := targetGas }
          accountMap :=
            if evmChild.accountMap.isEmpty then evm.accountMap
            else evmChild.accountMap
          substate :=
            if evmChild.accountMap.isEmpty then
              (EvmYul.State.addAccessedAccount evm.toState callee).substate
            else evmChild.substate
          createdAccounts := evmChild.createdAccounts }
      SourceLowered.WholeProgramOutcomeRel sourceOutcome
        (.running targetChild) ∧
      EvmYul.EVM.call evmFuel.succ.succ.succ gasCost
          yul.executionEnv.blobVersionedHashes gas
          (EvmYul.UInt256.ofNat evm.executionEnv.codeOwner) address address
          value value inOffset inSize outOffset outSize
          evm.executionEnv.perm evm =
        .ok (⟨1⟩, evmAfter) ∧
      EvmYul.Yul.primCall referenceFuel.succ (.Ok yul store) .CALL
          [gas, address, value, inOffset, inSize, outOffset, outSize] =
        .ok (.Ok yulAfter store, [⟨1⟩]) ∧
      Reference.SharedStateRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        yulAfter evmAfter.toSharedState := by
  dsimp at hCall hSourceRun hOutcomeRel hTargetGasForX hGasBound hReturnedGas ⊢
  let callee := EvmYul.AccountAddress.ofUInt256 address
  let callGasYul :=
    EvmYul.EVM.Ccallgas callee callee value gas yul.accountMap
      yul.toMachineState yul.substate
  let callGasEvm :=
    EvmYul.EVM.Ccallgas callee callee value gas evm.accountMap
      evm.toMachineState evm.substate
  let yulAccessed : EvmYul.SharedState .Yul :=
    { yul with
      toState := EvmYul.State.addAccessedAccount yul.toState callee }
  let initialShared : EvmYul.SharedState .Yul :=
    { yulAccessed with
      executionEnv :=
        { yulAccessed.executionEnv with
          calldata :=
            yul.toMachineState.memory.readWithPadding
              inOffset.toNat inSize.toNat
          code := program.contract
          codeBytes := yulRecipient.codeBytes
          codeOwner := callee
          source := yul.executionEnv.codeOwner
          weiValue := value
          depth := yul.executionEnv.depth + 1 }
      toMachineState :=
        EvmYul.MachineState.freshExternalCall
          (EvmYul.UInt256.ofNat callGasYul)
      accountMap := yulCallMap }
  let charged : EvmYul.EVM.State :=
    { evm with
      gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
  let targetGasOf : EVMState → ByteArray → EvmYul.UInt256 :=
    fun evmChild output =>
      (charged.toMachineState.finishExternalCall output
        inOffset inSize outOffset outSize).gasAvailable +
        evmChild.gasAvailable
  have hInstalled :
      initialShared.executionEnv.code = program.contract := by
    simp [initialShared]
  have hCall' :
      EvmYul.Yul.callDispatcher referenceFuel (some program.contract)
          (.Ok initialShared default) =
        .ok (.Ok yulChild childStore, rets) := by
    simpa [initialShared, yulAccessed, callGasYul, callee] using hCall
  have hSourceRun' :
      SourceLowered.run prim sourceFuel program
          (Assembly.GasAware.installCodeAndGas target callGasEvm
            (thetaCodeRawInitialState target callGasEvm
              yul.executionEnv.blobVersionedHashes evm.createdAccounts
              evm.genesisBlockHeader evm.blocks evm.accountMap evm.σ₀
              { totalGasUsedInBlock := evm.totalGasUsedInBlock
                transactionReceipts := evm.transactionReceipts }
              (EvmYul.State.addAccessedAccount evm.toState callee).substate
              evm.executionEnv.codeOwner evm.executionEnv.sender callee
              (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice) value value
              (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
              (evm.executionEnv.depth + 1) evm.executionEnv.header
              evm.executionEnv.perm)) =
        .ok sourceOutcome := by
    simpa [callGasEvm, callee] using hSourceRun
  have hOutcomeRel' :
      Program.RecursiveBridgeSemanticContracts.dispatcherOutcomeRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        terminalRel revertRel program (.Ok initialShared default)
        (.regular (.Ok yulChild childStore)) sourceOutcome := by
    simpa [initialShared, yulAccessed, callGasYul, callee] using hOutcomeRel
  let hTargetGasForX' :
      ∀ {targetFuel targetOutcome},
        Assembly.Preservation.BlockTraceResult asm target targetFuel
          (Assembly.GasAware.installCodeAndGas target callGasEvm
            (thetaCodeRawInitialState target callGasEvm
              yul.executionEnv.blobVersionedHashes evm.createdAccounts
              evm.genesisBlockHeader evm.blocks evm.accountMap evm.σ₀
              { totalGasUsedInBlock := evm.totalGasUsedInBlock
                transactionReceipts := evm.transactionReceipts }
              (EvmYul.State.addAccessedAccount evm.toState callee).substate
              evm.executionEnv.codeOwner evm.executionEnv.sender callee
              (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice) value value
              (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
              (evm.executionEnv.depth + 1) evm.executionEnv.header
              evm.executionEnv.perm))
          targetOutcome →
        Assembly.GasAware.XResultPreconditionAssumptions target
          (Assembly.GasAware.installCodeAndGas target callGasEvm
            (thetaCodeRawInitialState target callGasEvm
              yul.executionEnv.blobVersionedHashes evm.createdAccounts
              evm.genesisBlockHeader evm.blocks evm.accountMap evm.σ₀
              { totalGasUsedInBlock := evm.totalGasUsedInBlock
                transactionReceipts := evm.transactionReceipts }
              (EvmYul.State.addAccessedAccount evm.toState callee).substate
              evm.executionEnv.codeOwner evm.executionEnv.sender callee
              (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice) value value
              (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
              (evm.executionEnv.depth + 1) evm.executionEnv.header
              evm.executionEnv.perm))
          targetOutcome := by
    intro targetFuel targetOutcome hTrace
    exact hTargetGasForX (by simpa [callGasEvm, callee] using hTrace)
  have hGasBound' :
      ∀ {targetFuel targetOutcome}
        (hTrace :
          Assembly.Preservation.BlockTraceResult asm target targetFuel
            (Assembly.GasAware.installCodeAndGas target callGasEvm
              (thetaCodeRawInitialState target callGasEvm
                yul.executionEnv.blobVersionedHashes evm.createdAccounts
                evm.genesisBlockHeader evm.blocks evm.accountMap evm.σ₀
                { totalGasUsedInBlock := evm.totalGasUsedInBlock
                  transactionReceipts := evm.transactionReceipts }
                (EvmYul.State.addAccessedAccount evm.toState callee).substate
                evm.executionEnv.codeOwner evm.executionEnv.sender callee
                (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice) value value
                (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
                (evm.executionEnv.depth + 1) evm.executionEnv.header
                evm.executionEnv.perm))
            targetOutcome),
        (hTargetGasForX' hTrace).gasBound ≤ callGasEvm := by
    intro targetFuel targetOutcome hTrace
    dsimp [hTargetGasForX']
    simpa [callGasEvm, callee] using
      hGasBound (by simpa [callGasEvm, callee] using hTrace)
  have hUInt256' : callGasEvm < EvmYul.UInt256.size := by
    simpa [callGasEvm, callee] using hUInt256
  have hReturnedGas' :
      ∀ {targetOutcome evmChild output},
        SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome →
          Assembly.GasAware.XResultAgrees targetOutcome
            (.success evmChild output) →
          gasAvailableRel
            (yul.toMachineState.finishExternalCall ByteArray.empty
              inOffset inSize outOffset outSize).gasAvailable
            (targetGasOf evmChild output) := by
    intro targetOutcome evmChild output hWhole hAgree
    simpa [targetGasOf, charged] using hReturnedGas hWhole hAgree
  rcases
      ordinaryCodeCall_runningSuccessBranch_rel_of_installed_childDispatcher_afterAccess_withTargetGas
        (prim := prim) hPrim
        (varStackRel := varStackRel)
        (terminalCfgRel := terminalCfgRel)
        (revertCfgRel := revertCfgRel)
        (gasAvailableRel := gasAvailableRel)
        (gasValueRel := gasValueRel)
        (totalGasRel := totalGasRel)
        hShared hInstalled hCall' hSourceRun' hOutcomeRel'
        hFacts.compileBoundary hTargetGasForX' hGasBound' hUInt256'
        hTargetChildGas hEvmChildGas inOffset inSize outOffset outSize
        targetGasOf hReturnedGas' with
    ⟨evmFuel, targetChild, evmChild, output, _hCall,
      hWhole, hTheta, hRestore⟩
  rcases hRestore with ⟨yulAfter, hRestoreRun, hRel⟩
  have hCallYul :
      let callee := EvmYul.AccountAddress.ofUInt256 address
      let calldata :=
        yul.toMachineState.memory.readWithPadding
          inOffset.toNat inSize.toNat
      let callGas :=
        EvmYul.EVM.Ccallgas callee callee value gas yul.accountMap
          yul.toMachineState yul.substate
      let yulAccessed : EvmYul.SharedState .Yul :=
        { yul with
          toState := EvmYul.State.addAccessedAccount yul.toState callee }
      let initialShared : EvmYul.SharedState .Yul :=
        { yulAccessed with
          executionEnv :=
            { yulAccessed.executionEnv with
              calldata := calldata
              code := yulRecipient.code
              codeBytes := yulRecipient.codeBytes
              codeOwner := callee
              source := yul.executionEnv.codeOwner
              weiValue := value
              depth := yul.executionEnv.depth + 1 }
          toMachineState :=
            EvmYul.MachineState.freshExternalCall
              (EvmYul.UInt256.ofNat callGas)
          accountMap := yulCallMap }
      EvmYul.Yul.callDispatcher referenceFuel (some yulRecipient.code)
          (.Ok initialShared default) =
        .ok (.Ok yulChild childStore, rets) := by
    simpa [hFacts.contract] using hCall
  have hRelAdapter :
      let callee := EvmYul.AccountAddress.ofUInt256 address
      let charged : EvmYul.EVM.State :=
        { evm with
          gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
      let targetGas :=
        (charged.toMachineState.finishExternalCall output
          inOffset inSize outOffset outSize).gasAvailable +
          evmChild.gasAvailable
      Reference.SharedStateRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        yulAfter
        ({ charged with
          toMachineState :=
            { charged.toMachineState.finishExternalCall output
                inOffset inSize outOffset outSize with
              gasAvailable := targetGas }
          accountMap :=
            if evmChild.accountMap.isEmpty then evm.accountMap
            else evmChild.accountMap
          substate :=
            if evmChild.accountMap.isEmpty then
              (EvmYul.State.addAccessedAccount evm.toState callee).substate
            else evmChild.substate
          createdAccounts := evmChild.createdAccounts } :
          EvmYul.EVM.State).toSharedState := by
    simpa [callee, charged, targetGasOf] using hRel
  rcases
      primCall_CALL_ordinary_runningSuccess_of_theta_restore
        (cfg :=
          stateRelConfig varStackRel terminalCfgRel revertCfgRel
            gasAvailableRel gasValueRel totalGasRel)
        (referenceFuel := referenceFuel)
        (evmThetaFuel := evmFuel.succ.succ)
        (gasCost := gasCost)
        (blobVersionedHashes := yul.executionEnv.blobVersionedHashes)
        (yul := yul) (yulChild := yulChild) (yulAfter := yulAfter)
        (evm := evm) (evmChild := evmChild)
        store childStore
        (gas := gas) (address := address) (value := value)
        (inOffset := inOffset) (inSize := inSize)
        (outOffset := outOffset) (outSize := outSize)
        (yulRecipient := yulRecipient) (yulCallMap := yulCallMap)
        (evmRecipient := evmRecipient) (target := target)
        (rets := rets) (output := output)
          hShared hStaticAllowed hEnough hDepth hNotPrecompile hFacts.findYul
          hFacts.transfer hFacts.findEvm hFacts.code hCallYul hTheta
          hRestoreRun
          hRelAdapter with
      ⟨hEvmCall, hYulCall, hFinalRel⟩
  refine ⟨evmFuel, targetChild, evmChild, output, yulAfter, ?_⟩
  dsimp
  exact ⟨hWhole, hEvmCall, hYulCall, hFinalRel⟩

theorem CALLPrimitiveRel.ordinaryRunningSuccess_stateRelConfig
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {varStackRel : Reference.VarStackRel}
    {terminalCfgRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop}
    {revertCfgRel : Reference.State → EVMState → Prop}
    {gasAvailableRel : Word → Word → Prop}
    {gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm}
    {totalGasRel : Nat → Nat → Prop}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {referenceFuel sourceFuel gasCost : Nat}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.EVM.State}
    (hShared :
      Reference.SharedStateRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        yul evm.toSharedState)
    (store childStore : EvmYul.Yul.VarStore)
    {gas address value inOffset inSize outOffset outSize : EvmYul.UInt256}
    {yulRecipient : EvmYul.Account .Yul}
    {yulCallMap : EvmYul.AccountMap .Yul}
    {evmRecipient : EvmYul.Account .EVM}
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    {yulChild : EvmYul.SharedState .Yul}
    {rets : List EvmYul.UInt256}
    {sourceOutcome : Objects.Source.Outcome}
    (hStaticAllowed :
      ¬ (¬ yul.executionEnv.perm ∧ value ≠ ⟨0⟩))
    (hEnough :
      value ≤
        (evm.accountMap.find? evm.executionEnv.codeOwner |>.option ⟨0⟩
          (·.balance)))
    (hDepth : evm.executionEnv.depth < 1024)
    (hNotPrecompile :
      EvmYul.PrecompiledContract.ofAddress?
        (EvmYul.AccountAddress.ofUInt256 address) = none)
    (hFacts :
      OrdinaryCALLBranchFacts yul evm address value yulRecipient
        yulCallMap evmRecipient program asm target)
    (hCall :
      let callee := EvmYul.AccountAddress.ofUInt256 address
      let calldata :=
        yul.toMachineState.memory.readWithPadding
          inOffset.toNat inSize.toNat
      let callGas :=
        EvmYul.EVM.Ccallgas callee callee value gas yul.accountMap
          yul.toMachineState yul.substate
      let yulAccessed : EvmYul.SharedState .Yul :=
        { yul with
          toState := EvmYul.State.addAccessedAccount yul.toState callee }
      let initialShared : EvmYul.SharedState .Yul :=
        { yulAccessed with
          executionEnv :=
            { yulAccessed.executionEnv with
              calldata := calldata
              code := program.contract
              codeBytes := yulRecipient.codeBytes
              codeOwner := callee
              source := yul.executionEnv.codeOwner
              weiValue := value
              depth := yul.executionEnv.depth + 1 }
          toMachineState :=
            EvmYul.MachineState.freshExternalCall
              (EvmYul.UInt256.ofNat callGas)
          accountMap := yulCallMap }
      EvmYul.Yul.callDispatcher referenceFuel (some program.contract)
          (.Ok initialShared default) =
        .ok (.Ok yulChild childStore, rets))
    (hSourceRun :
      let callee := EvmYul.AccountAddress.ofUInt256 address
      let callGas :=
        EvmYul.EVM.Ccallgas callee callee value gas evm.accountMap
          evm.toMachineState evm.substate
      SourceLowered.run prim sourceFuel program
          (Assembly.GasAware.installCodeAndGas target callGas
            (thetaCodeRawInitialState target callGas
              yul.executionEnv.blobVersionedHashes evm.createdAccounts
              evm.genesisBlockHeader evm.blocks evm.accountMap evm.σ₀
              { totalGasUsedInBlock := evm.totalGasUsedInBlock
                transactionReceipts := evm.transactionReceipts }
              (EvmYul.State.addAccessedAccount evm.toState callee).substate
              evm.executionEnv.codeOwner evm.executionEnv.sender callee
              (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice) value value
              (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
              (evm.executionEnv.depth + 1) evm.executionEnv.header
              evm.executionEnv.perm)) =
        .ok sourceOutcome)
    (hOutcomeRel :
      let callee := EvmYul.AccountAddress.ofUInt256 address
      let calldata :=
        yul.toMachineState.memory.readWithPadding
          inOffset.toNat inSize.toNat
      let callGas :=
        EvmYul.EVM.Ccallgas callee callee value gas yul.accountMap
          yul.toMachineState yul.substate
      let yulAccessed : EvmYul.SharedState .Yul :=
        { yul with
          toState := EvmYul.State.addAccessedAccount yul.toState callee }
      let initialShared : EvmYul.SharedState .Yul :=
        { yulAccessed with
          executionEnv :=
            { yulAccessed.executionEnv with
              calldata := calldata
              code := program.contract
              codeBytes := yulRecipient.codeBytes
              codeOwner := callee
              source := yul.executionEnv.codeOwner
              weiValue := value
              depth := yul.executionEnv.depth + 1 }
          toMachineState :=
            EvmYul.MachineState.freshExternalCall
              (EvmYul.UInt256.ofNat callGas)
          accountMap := yulCallMap }
      Program.RecursiveBridgeSemanticContracts.dispatcherOutcomeRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        terminalRel revertRel program (.Ok initialShared default)
        (.regular (.Ok yulChild childStore)) sourceOutcome)
    (hTargetGasForX :
      let callee := EvmYul.AccountAddress.ofUInt256 address
      let callGas :=
        EvmYul.EVM.Ccallgas callee callee value gas evm.accountMap
          evm.toMachineState evm.substate
      ∀ {targetFuel targetOutcome},
        Assembly.Preservation.BlockTraceResult asm target targetFuel
          (Assembly.GasAware.installCodeAndGas target callGas
            (thetaCodeRawInitialState target callGas
              yul.executionEnv.blobVersionedHashes evm.createdAccounts
              evm.genesisBlockHeader evm.blocks evm.accountMap evm.σ₀
              { totalGasUsedInBlock := evm.totalGasUsedInBlock
                transactionReceipts := evm.transactionReceipts }
              (EvmYul.State.addAccessedAccount evm.toState callee).substate
              evm.executionEnv.codeOwner evm.executionEnv.sender callee
              (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice) value value
              (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
              (evm.executionEnv.depth + 1) evm.executionEnv.header
              evm.executionEnv.perm))
          targetOutcome →
        Assembly.GasAware.XResultPreconditionAssumptions target
          (Assembly.GasAware.installCodeAndGas target callGas
            (thetaCodeRawInitialState target callGas
              yul.executionEnv.blobVersionedHashes evm.createdAccounts
              evm.genesisBlockHeader evm.blocks evm.accountMap evm.σ₀
              { totalGasUsedInBlock := evm.totalGasUsedInBlock
                transactionReceipts := evm.transactionReceipts }
              (EvmYul.State.addAccessedAccount evm.toState callee).substate
              evm.executionEnv.codeOwner evm.executionEnv.sender callee
              (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice) value value
              (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
              (evm.executionEnv.depth + 1) evm.executionEnv.header
              evm.executionEnv.perm))
          targetOutcome)
    (hGasBound :
      let callee := EvmYul.AccountAddress.ofUInt256 address
      let callGas :=
        EvmYul.EVM.Ccallgas callee callee value gas evm.accountMap
          evm.toMachineState evm.substate
      ∀ {targetFuel targetOutcome}
        (hTrace :
          Assembly.Preservation.BlockTraceResult asm target targetFuel
            (Assembly.GasAware.installCodeAndGas target callGas
              (thetaCodeRawInitialState target callGas
                yul.executionEnv.blobVersionedHashes evm.createdAccounts
                evm.genesisBlockHeader evm.blocks evm.accountMap evm.σ₀
                { totalGasUsedInBlock := evm.totalGasUsedInBlock
                  transactionReceipts := evm.transactionReceipts }
                (EvmYul.State.addAccessedAccount evm.toState callee).substate
                evm.executionEnv.codeOwner evm.executionEnv.sender callee
                (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice) value value
                (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
                (evm.executionEnv.depth + 1) evm.executionEnv.header
                evm.executionEnv.perm))
            targetOutcome),
        (hTargetGasForX hTrace).gasBound ≤ callGas)
    (hUInt256 :
      EvmYul.EVM.Ccallgas (EvmYul.AccountAddress.ofUInt256 address)
          (EvmYul.AccountAddress.ofUInt256 address) value gas
          evm.accountMap evm.toMachineState evm.substate <
        EvmYul.UInt256.size)
    (hTargetChildGas :
      ∀ {targetChild}, SourceLowered.WholeProgramOutcomeRel sourceOutcome
          (.running targetChild) →
        gasAvailableRel yulChild.toMachineState.gasAvailable
          targetChild.gasAvailable)
    (hEvmChildGas :
      ∀ {targetOutcome evmChild output},
        SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome →
          Assembly.GasAware.XResultAgrees targetOutcome
            (.success evmChild output) →
          gasAvailableRel yulChild.toMachineState.gasAvailable
            evmChild.gasAvailable)
    (hReturnedGas :
      ∀ {targetOutcome evmChild output},
        SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome →
          Assembly.GasAware.XResultAgrees targetOutcome
            (.success evmChild output) →
          let charged : EvmYul.EVM.State :=
            { evm with
              gasAvailable :=
                evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
          gasAvailableRel
            (yul.toMachineState.finishExternalCall ByteArray.empty
              inOffset inSize outOffset outSize).gasAvailable
            ((charged.toMachineState.finishExternalCall output
                inOffset inSize outOffset outSize).gasAvailable +
              evmChild.gasAvailable)) :
    ∃ (evmFuel : Nat),
      CALLPrimitiveRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        referenceFuel.succ evmFuel.succ.succ.succ gasCost
        yul.executionEnv.blobVersionedHashes yul evm store
        gas address value inOffset inSize outOffset outSize := by
  rcases
      primCall_CALL_ordinary_runningSuccess_rel_of_installed_childDispatcher_afterAccess_withTargetGas
        hPrim hShared store childStore hStaticAllowed hEnough hDepth
        hNotPrecompile hFacts hCall hSourceRun hOutcomeRel hTargetGasForX
        hGasBound hUInt256 hTargetChildGas hEvmChildGas hReturnedGas with
    ⟨evmFuel, _targetChild, _evmChild, _output, yulAfter, _hWhole,
      hEvmCall, hYulCall, hFinalRel⟩
  exact ⟨evmFuel, ⟨⟨1⟩, _, yulAfter, hEvmCall, hYulCall, hFinalRel⟩⟩

theorem primCall_CALL_ordinary_haltedSuccess_rel_of_installed_childDispatcher_afterAccess_withTargetGas
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {varStackRel : Reference.VarStackRel}
    {terminalCfgRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop}
    {revertCfgRel : Reference.State → EVMState → Prop}
    {gasAvailableRel : Word → Word → Prop}
    {gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm}
    {totalGasRel : Nat → Nat → Prop}
    {referenceFuel sourceFuel gasCost : Nat}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.EVM.State}
    (hShared :
      Reference.SharedStateRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        yul evm.toSharedState)
    (store childStore : EvmYul.Yul.VarStore)
    {gas address value inOffset inSize outOffset outSize : EvmYul.UInt256}
    {yulRecipient : EvmYul.Account .Yul}
    {yulCallMap : EvmYul.AccountMap .Yul}
    {evmRecipient : EvmYul.Account .EVM}
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    {yulChild : EvmYul.SharedState .Yul}
    {haltValue : EvmYul.UInt256}
    {sourceOutcome : Objects.Source.Outcome}
    (hStaticAllowed :
      ¬ (¬ yul.executionEnv.perm ∧ value ≠ ⟨0⟩))
    (hEnough :
      value ≤
        (evm.accountMap.find? evm.executionEnv.codeOwner |>.option ⟨0⟩
          (·.balance)))
    (hDepth : evm.executionEnv.depth < 1024)
    (hNotPrecompile :
      EvmYul.PrecompiledContract.ofAddress?
        (EvmYul.AccountAddress.ofUInt256 address) = none)
    (hFacts :
      OrdinaryCALLBranchFacts yul evm address value yulRecipient
        yulCallMap evmRecipient program asm target)
    (hCall :
      let callee := EvmYul.AccountAddress.ofUInt256 address
      let calldata :=
        yul.toMachineState.memory.readWithPadding
          inOffset.toNat inSize.toNat
      let callGas :=
        EvmYul.EVM.Ccallgas callee callee value gas yul.accountMap
          yul.toMachineState yul.substate
      let yulAccessed : EvmYul.SharedState .Yul :=
        { yul with
          toState := EvmYul.State.addAccessedAccount yul.toState callee }
      let initialShared : EvmYul.SharedState .Yul :=
        { yulAccessed with
          executionEnv :=
            { yulAccessed.executionEnv with
              calldata := calldata
              code := program.contract
              codeBytes := yulRecipient.codeBytes
              codeOwner := callee
              source := yul.executionEnv.codeOwner
              weiValue := value
              depth := yul.executionEnv.depth + 1 }
          toMachineState :=
            EvmYul.MachineState.freshExternalCall
              (EvmYul.UInt256.ofNat callGas)
          accountMap := yulCallMap }
      EvmYul.Yul.callDispatcher referenceFuel (some program.contract)
          (.Ok initialShared default) =
        .error (.YulHalt (.Ok yulChild childStore) haltValue))
    (hSourceRun :
      let callee := EvmYul.AccountAddress.ofUInt256 address
      let callGas :=
        EvmYul.EVM.Ccallgas callee callee value gas evm.accountMap
          evm.toMachineState evm.substate
      SourceLowered.run prim sourceFuel program
          (Assembly.GasAware.installCodeAndGas target callGas
            (thetaCodeRawInitialState target callGas
              yul.executionEnv.blobVersionedHashes evm.createdAccounts
              evm.genesisBlockHeader evm.blocks evm.accountMap evm.σ₀
              { totalGasUsedInBlock := evm.totalGasUsedInBlock
                transactionReceipts := evm.transactionReceipts }
              (EvmYul.State.addAccessedAccount evm.toState callee).substate
              evm.executionEnv.codeOwner evm.executionEnv.sender callee
              (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice) value value
              (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
              (evm.executionEnv.depth + 1) evm.executionEnv.header
              evm.executionEnv.perm)) =
        .ok sourceOutcome)
    (hOutcomeRel :
      let callee := EvmYul.AccountAddress.ofUInt256 address
      let calldata :=
        yul.toMachineState.memory.readWithPadding
          inOffset.toNat inSize.toNat
      let callGas :=
        EvmYul.EVM.Ccallgas callee callee value gas yul.accountMap
          yul.toMachineState yul.substate
      let yulAccessed : EvmYul.SharedState .Yul :=
        { yul with
          toState := EvmYul.State.addAccessedAccount yul.toState callee }
      let initialShared : EvmYul.SharedState .Yul :=
        { yulAccessed with
          executionEnv :=
            { yulAccessed.executionEnv with
              calldata := calldata
              code := program.contract
              codeBytes := yulRecipient.codeBytes
              codeOwner := callee
              source := yul.executionEnv.codeOwner
              weiValue := value
              depth := yul.executionEnv.depth + 1 }
          toMachineState :=
            EvmYul.MachineState.freshExternalCall
              (EvmYul.UInt256.ofNat callGas)
          accountMap := yulCallMap }
      Program.RecursiveBridgeSemanticContracts.dispatcherOutcomeRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        (Program.RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel
          (stateRelConfig varStackRel terminalCfgRel revertCfgRel
            gasAvailableRel gasValueRel totalGasRel))
        (Program.RecursiveBridgeTerminalObservationContracts.canonicalRevertRel
          (stateRelConfig varStackRel terminalCfgRel revertCfgRel
            gasAvailableRel gasValueRel totalGasRel))
        program (.Ok initialShared default)
        (.yulHalt (.Ok yulChild childStore) haltValue) sourceOutcome)
    (hTargetGasForX :
      let callee := EvmYul.AccountAddress.ofUInt256 address
      let callGas :=
        EvmYul.EVM.Ccallgas callee callee value gas evm.accountMap
          evm.toMachineState evm.substate
      ∀ {targetFuel targetOutcome},
        Assembly.Preservation.BlockTraceResult asm target targetFuel
          (Assembly.GasAware.installCodeAndGas target callGas
            (thetaCodeRawInitialState target callGas
              yul.executionEnv.blobVersionedHashes evm.createdAccounts
              evm.genesisBlockHeader evm.blocks evm.accountMap evm.σ₀
              { totalGasUsedInBlock := evm.totalGasUsedInBlock
                transactionReceipts := evm.transactionReceipts }
              (EvmYul.State.addAccessedAccount evm.toState callee).substate
              evm.executionEnv.codeOwner evm.executionEnv.sender callee
              (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice) value value
              (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
              (evm.executionEnv.depth + 1) evm.executionEnv.header
              evm.executionEnv.perm))
          targetOutcome →
        Assembly.GasAware.XResultPreconditionAssumptions target
          (Assembly.GasAware.installCodeAndGas target callGas
            (thetaCodeRawInitialState target callGas
              yul.executionEnv.blobVersionedHashes evm.createdAccounts
              evm.genesisBlockHeader evm.blocks evm.accountMap evm.σ₀
              { totalGasUsedInBlock := evm.totalGasUsedInBlock
                transactionReceipts := evm.transactionReceipts }
              (EvmYul.State.addAccessedAccount evm.toState callee).substate
              evm.executionEnv.codeOwner evm.executionEnv.sender callee
              (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice) value value
              (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
              (evm.executionEnv.depth + 1) evm.executionEnv.header
              evm.executionEnv.perm))
          targetOutcome)
    (hGasBound :
      let callee := EvmYul.AccountAddress.ofUInt256 address
      let callGas :=
        EvmYul.EVM.Ccallgas callee callee value gas evm.accountMap
          evm.toMachineState evm.substate
      ∀ {targetFuel targetOutcome}
        (hTrace :
          Assembly.Preservation.BlockTraceResult asm target targetFuel
            (Assembly.GasAware.installCodeAndGas target callGas
              (thetaCodeRawInitialState target callGas
                yul.executionEnv.blobVersionedHashes evm.createdAccounts
                evm.genesisBlockHeader evm.blocks evm.accountMap evm.σ₀
                { totalGasUsedInBlock := evm.totalGasUsedInBlock
                  transactionReceipts := evm.transactionReceipts }
                (EvmYul.State.addAccessedAccount evm.toState callee).substate
                evm.executionEnv.codeOwner evm.executionEnv.sender callee
                (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice) value value
                (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
                (evm.executionEnv.depth + 1) evm.executionEnv.header
                evm.executionEnv.perm))
            targetOutcome),
        (hTargetGasForX hTrace).gasBound ≤ callGas)
    (hUInt256 :
      EvmYul.EVM.Ccallgas (EvmYul.AccountAddress.ofUInt256 address)
          (EvmYul.AccountAddress.ofUInt256 address) value gas
          evm.accountMap evm.toMachineState evm.substate <
        EvmYul.UInt256.size)
    (hReturnedGas :
      ∀ {targetOutcome evmChild output},
        SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome →
          Assembly.GasAware.XResultAgrees targetOutcome
            (.success evmChild output) →
          let charged : EvmYul.EVM.State :=
            { evm with
              gasAvailable :=
                evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
          gasAvailableRel
            (yul.toMachineState.finishExternalCall output
              inOffset inSize outOffset outSize).gasAvailable
            ((charged.toMachineState.finishExternalCall output
                inOffset inSize outOffset outSize).gasAvailable +
              evmChild.gasAvailable)) :
    ∃ (evmFuel : Nat) (kind : Assembly.HaltKind)
      (compiler : Objects.Source.State) (halt : Assembly.Halt)
      (evmChild : EVMState) (output : ByteArray)
      (yulAfter : EvmYul.SharedState .Yul),
      let callee := EvmYul.AccountAddress.ofUInt256 address
      let charged : EvmYul.EVM.State :=
        { evm with
          gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
      let targetGas :=
        (charged.toMachineState.finishExternalCall output
          inOffset inSize outOffset outSize).gasAvailable +
          evmChild.gasAvailable
      let evmAfter : EvmYul.EVM.State :=
        { charged with
          toMachineState :=
            { charged.toMachineState.finishExternalCall output
                inOffset inSize outOffset outSize with
              gasAvailable := targetGas }
          accountMap :=
            if evmChild.accountMap.isEmpty then evm.accountMap
            else evmChild.accountMap
          substate :=
            if evmChild.accountMap.isEmpty then
              (EvmYul.State.addAccessedAccount evm.toState callee).substate
            else evmChild.substate
          createdAccounts := evmChild.createdAccounts }
      Program.RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        kind haltValue (.Ok yulChild childStore) compiler ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome (.halted halt) ∧
      halt.kind = kind ∧
      halt.kind ≠ .revert ∧
      EvmYul.EVM.call evmFuel.succ.succ.succ gasCost
          yul.executionEnv.blobVersionedHashes gas
          (EvmYul.UInt256.ofNat evm.executionEnv.codeOwner) address address
          value value inOffset inSize outOffset outSize
          evm.executionEnv.perm evm =
        .ok (⟨1⟩, evmAfter) ∧
      EvmYul.Yul.primCall referenceFuel.succ (.Ok yul store) .CALL
          [gas, address, value, inOffset, inSize, outOffset, outSize] =
        .ok (.Ok yulAfter store, [⟨1⟩]) ∧
      Reference.SharedStateRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        yulAfter evmAfter.toSharedState := by
  dsimp at hCall hSourceRun hOutcomeRel hTargetGasForX hGasBound hReturnedGas ⊢
  let callee := EvmYul.AccountAddress.ofUInt256 address
  let callGasYul :=
    EvmYul.EVM.Ccallgas callee callee value gas yul.accountMap
      yul.toMachineState yul.substate
  let callGasEvm :=
    EvmYul.EVM.Ccallgas callee callee value gas evm.accountMap
      evm.toMachineState evm.substate
  let yulAccessed : EvmYul.SharedState .Yul :=
    { yul with
      toState := EvmYul.State.addAccessedAccount yul.toState callee }
  let initialShared : EvmYul.SharedState .Yul :=
    { yulAccessed with
      executionEnv :=
        { yulAccessed.executionEnv with
          calldata :=
            yul.toMachineState.memory.readWithPadding
              inOffset.toNat inSize.toNat
          code := program.contract
          codeBytes := yulRecipient.codeBytes
          codeOwner := callee
          source := yul.executionEnv.codeOwner
          weiValue := value
          depth := yul.executionEnv.depth + 1 }
      toMachineState :=
        EvmYul.MachineState.freshExternalCall
          (EvmYul.UInt256.ofNat callGasYul)
      accountMap := yulCallMap }
  let charged : EvmYul.EVM.State :=
    { evm with
      gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
  let targetGasOf : EVMState → ByteArray → EvmYul.UInt256 :=
    fun evmChild output =>
      (charged.toMachineState.finishExternalCall output
        inOffset inSize outOffset outSize).gasAvailable +
        evmChild.gasAvailable
  have hInstalled :
      initialShared.executionEnv.code = program.contract := by
    simp [initialShared]
  have hCall' :
      EvmYul.Yul.callDispatcher referenceFuel (some program.contract)
          (.Ok initialShared default) =
        .error (.YulHalt (.Ok yulChild childStore) haltValue) := by
    simpa [initialShared, yulAccessed, callGasYul, callee] using hCall
  have hSourceRun' :
      SourceLowered.run prim sourceFuel program
          (Assembly.GasAware.installCodeAndGas target callGasEvm
            (thetaCodeRawInitialState target callGasEvm
              yul.executionEnv.blobVersionedHashes evm.createdAccounts
              evm.genesisBlockHeader evm.blocks evm.accountMap evm.σ₀
              { totalGasUsedInBlock := evm.totalGasUsedInBlock
                transactionReceipts := evm.transactionReceipts }
              (EvmYul.State.addAccessedAccount evm.toState callee).substate
              evm.executionEnv.codeOwner evm.executionEnv.sender callee
              (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice) value value
              (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
              (evm.executionEnv.depth + 1) evm.executionEnv.header
              evm.executionEnv.perm)) =
        .ok sourceOutcome := by
    simpa [callGasEvm, callee] using hSourceRun
  have hOutcomeRel' :
      Program.RecursiveBridgeSemanticContracts.dispatcherOutcomeRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        (Program.RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel
          (stateRelConfig varStackRel terminalCfgRel revertCfgRel
            gasAvailableRel gasValueRel totalGasRel))
        (Program.RecursiveBridgeTerminalObservationContracts.canonicalRevertRel
          (stateRelConfig varStackRel terminalCfgRel revertCfgRel
            gasAvailableRel gasValueRel totalGasRel))
        program (.Ok initialShared default)
        (.yulHalt (.Ok yulChild childStore) haltValue) sourceOutcome := by
    simpa [initialShared, yulAccessed, callGasYul, callee] using hOutcomeRel
  let hTargetGasForX' :
      ∀ {targetFuel targetOutcome},
        Assembly.Preservation.BlockTraceResult asm target targetFuel
          (Assembly.GasAware.installCodeAndGas target callGasEvm
            (thetaCodeRawInitialState target callGasEvm
              yul.executionEnv.blobVersionedHashes evm.createdAccounts
              evm.genesisBlockHeader evm.blocks evm.accountMap evm.σ₀
              { totalGasUsedInBlock := evm.totalGasUsedInBlock
                transactionReceipts := evm.transactionReceipts }
              (EvmYul.State.addAccessedAccount evm.toState callee).substate
              evm.executionEnv.codeOwner evm.executionEnv.sender callee
              (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice) value value
              (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
              (evm.executionEnv.depth + 1) evm.executionEnv.header
              evm.executionEnv.perm))
          targetOutcome →
        Assembly.GasAware.XResultPreconditionAssumptions target
          (Assembly.GasAware.installCodeAndGas target callGasEvm
            (thetaCodeRawInitialState target callGasEvm
              yul.executionEnv.blobVersionedHashes evm.createdAccounts
              evm.genesisBlockHeader evm.blocks evm.accountMap evm.σ₀
              { totalGasUsedInBlock := evm.totalGasUsedInBlock
                transactionReceipts := evm.transactionReceipts }
              (EvmYul.State.addAccessedAccount evm.toState callee).substate
              evm.executionEnv.codeOwner evm.executionEnv.sender callee
              (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice) value value
              (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
              (evm.executionEnv.depth + 1) evm.executionEnv.header
              evm.executionEnv.perm))
          targetOutcome := by
    intro targetFuel targetOutcome hTrace
    exact hTargetGasForX (by simpa [callGasEvm, callee] using hTrace)
  have hGasBound' :
      ∀ {targetFuel targetOutcome}
        (hTrace :
          Assembly.Preservation.BlockTraceResult asm target targetFuel
            (Assembly.GasAware.installCodeAndGas target callGasEvm
              (thetaCodeRawInitialState target callGasEvm
                yul.executionEnv.blobVersionedHashes evm.createdAccounts
                evm.genesisBlockHeader evm.blocks evm.accountMap evm.σ₀
                { totalGasUsedInBlock := evm.totalGasUsedInBlock
                  transactionReceipts := evm.transactionReceipts }
                (EvmYul.State.addAccessedAccount evm.toState callee).substate
                evm.executionEnv.codeOwner evm.executionEnv.sender callee
                (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice) value value
                (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
                (evm.executionEnv.depth + 1) evm.executionEnv.header
                evm.executionEnv.perm))
            targetOutcome),
        (hTargetGasForX' hTrace).gasBound ≤ callGasEvm := by
    intro targetFuel targetOutcome hTrace
    dsimp [hTargetGasForX']
    simpa [callGasEvm, callee] using
      hGasBound (by simpa [callGasEvm, callee] using hTrace)
  have hUInt256' : callGasEvm < EvmYul.UInt256.size := by
    simpa [callGasEvm, callee] using hUInt256
  rcases
      compile_preserves_of_installed_callDispatcher_yulHalt_sourceStaticBoundary_installedGas_XResult
        (prim := prim) hPrim
        (outcomeRel :=
          Program.RecursiveBridgeSemanticContracts.dispatcherOutcomeRel
            (stateRelConfig varStackRel terminalCfgRel revertCfgRel
              gasAvailableRel gasValueRel totalGasRel)
            (Program.RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel
              (stateRelConfig varStackRel terminalCfgRel revertCfgRel
                gasAvailableRel gasValueRel totalGasRel))
            (Program.RecursiveBridgeTerminalObservationContracts.canonicalRevertRel
              (stateRelConfig varStackRel terminalCfgRel revertCfgRel
                gasAvailableRel gasValueRel totalGasRel))
            program (.Ok initialShared default))
        (program := program) (asm := asm) (target := target)
        (referenceFuel := referenceFuel) (sourceFuel := sourceFuel)
        (gas := callGasEvm) (shared := initialShared)
        (store := default) (haltState := .Ok yulChild childStore)
        (value := haltValue)
        (rawInitial :=
          thetaCodeRawInitialState target callGasEvm
            yul.executionEnv.blobVersionedHashes evm.createdAccounts
            evm.genesisBlockHeader evm.blocks evm.accountMap evm.σ₀
            { totalGasUsedInBlock := evm.totalGasUsedInBlock
              transactionReceipts := evm.transactionReceipts }
            (EvmYul.State.addAccessedAccount evm.toState callee).substate
            evm.executionEnv.codeOwner evm.executionEnv.sender callee
            (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice) value value
            (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
            (evm.executionEnv.depth + 1) evm.executionEnv.header
            evm.executionEnv.perm)
        (sourceOutcome := sourceOutcome)
        hInstalled hCall' hSourceRun' hOutcomeRel' hFacts.compileBoundary
        (by
          simp [thetaCodeRawInitialState, Assembly.GasAware.installCodeAndGas])
        (by
          simp [thetaCodeRawInitialState, Assembly.GasAware.installCodeAndGas])
        hTargetGasForX' hGasBound' hUInt256' with
    ⟨targetFuel, targetOutcome, evmFuel, _gasBound, evmResult,
      _hReferenceRun, _hTargetRun, _hOutcomeRel, hWhole, hTrace,
      _hGasBound, hX, hAgree, _hDecode, _hJumpdest⟩
  have hXTheta :
      EvmYul.EVM.X evmFuel (Assembly.GasAware.validJumps target)
          (thetaCodeXInitialState target callGasEvm
            yul.executionEnv.blobVersionedHashes evm.createdAccounts
            evm.genesisBlockHeader evm.blocks evm.accountMap evm.σ₀
            { totalGasUsedInBlock := evm.totalGasUsedInBlock
              transactionReceipts := evm.transactionReceipts }
            (EvmYul.State.addAccessedAccount evm.toState callee).substate
            evm.executionEnv.codeOwner evm.executionEnv.sender callee
            (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice) value value
            (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
            (evm.executionEnv.depth + 1) evm.executionEnv.header
            evm.executionEnv.perm) =
        .ok evmResult := by
    simpa [thetaCodeXInitialState] using hX
  rcases
      dispatcherOutcomeRel_yulHalt_ok_whole_childMergeRelations
        (varStackRel := varStackRel)
        (terminalCfgRel := terminalCfgRel)
        (revertCfgRel := revertCfgRel)
        (gasAvailableRel := gasAvailableRel)
        (gasValueRel := gasValueRel)
        (totalGasRel := totalGasRel)
        hOutcomeRel' hWhole
        (by
          intro kind compiler hRel
          exact canonicalTerminalRel_externalChildMergeRel hRel) with
    ⟨kind, compiler, halt, hTerminal, hSource, hTarget, hKind,
      _hTargetChild⟩
  have hNotRevert : halt.kind ≠ .revert := by
    intro hRevert
    exact
      Program.RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel_nonrevert
        hTerminal (hKind.symm.trans hRevert)
  have hAgreeHalted :
      Assembly.GasAware.XResultAgrees (.halted halt) evmResult := by
    simpa [hTarget] using hAgree
  rcases XResultAgrees_halted_nonrevert_success_shape
      hAgreeHalted hNotRevert with
    ⟨evmChild, output, hResult, hAgreeSuccess⟩
  have hXSuccess :
      EvmYul.EVM.X evmFuel (Assembly.GasAware.validJumps target)
          (thetaCodeXInitialState target callGasEvm
            yul.executionEnv.blobVersionedHashes evm.createdAccounts
            evm.genesisBlockHeader evm.blocks evm.accountMap evm.σ₀
            { totalGasUsedInBlock := evm.totalGasUsedInBlock
              transactionReceipts := evm.transactionReceipts }
            (EvmYul.State.addAccessedAccount evm.toState callee).substate
            evm.executionEnv.codeOwner evm.executionEnv.sender callee
            (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice) value value
            (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
            (evm.executionEnv.depth + 1) evm.executionEnv.header
            evm.executionEnv.perm) =
        .ok (.success evmChild output) := by
    simpa [hResult] using hXTheta
  have hWholeHalted :
      SourceLowered.WholeProgramOutcomeRel sourceOutcome (.halted halt) := by
    simpa [hTarget] using hWhole
  have hWholeHaltSource :
      SourceLowered.WholeProgramOutcomeRel
        (Functions.Source.Outcome.halt kind compiler) (.halted halt) := by
    simpa [hSource, hTarget] using hWhole
  have hTargetHReturn :
      yulChild.toMachineState.H_return =
        halt.state.toMachineState.H_return :=
    wholeProgramOutcomeRel_halt_H_return
      (Program.RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel_H_return
        hTerminal)
      hWholeHaltSource
  have hTargetGas :
      gasAvailableRel
        (yul.toMachineState.finishExternalCall output
          inOffset inSize outOffset outSize).gasAvailable
        (targetGasOf evmChild output) := by
    simpa [targetGasOf, charged] using
      hReturnedGas hWholeHalted hAgreeSuccess
  rcases
      ordinaryCodeCall_haltedSuccessBranch_rel_of_childOutcome_afterAccess
        (varStackRel := varStackRel)
        (terminalCfgRel := terminalCfgRel)
        (revertCfgRel := revertCfgRel)
        (gasAvailableRel := gasAvailableRel)
        (gasValueRel := gasValueRel)
        (totalGasRel := totalGasRel)
        hShared hOutcomeRel' hWholeHalted
        (by
          intro kind compiler hRel
          exact canonicalTerminalRel_externalChildMergeRel hRel)
        (by
          intro kind compiler hRel
          exact
            Program.RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel_nonrevert
              hRel)
        hXSuccess hAgreeSuccess
        inOffset inSize outOffset outSize
        (targetGas := targetGasOf evmChild output)
        (by
          intro evmChildA outputA hResultA
          simpa [hResultA] using hTargetGas) with
    ⟨kindTerm, compilerTerm, haltTerm, evmChildTerm, outputTerm,
      hTerminalTerm, hTargetTerm, hKindTerm, hResultTerm, hTheta,
      hNotRevertTerm,
      yulAfter, hRestoreRun, hRel⟩
  cases hResultTerm
  have hWholeHaltedTerm :
      SourceLowered.WholeProgramOutcomeRel sourceOutcome
        (.halted haltTerm) := by
    simpa [hTargetTerm] using hWholeHalted
  have hHaltEq : haltTerm = halt := by
    cases hTarget
    cases hTargetTerm
    rfl
  have hTargetHReturnTerm :
      yulChild.toMachineState.H_return =
        haltTerm.state.toMachineState.H_return := by
    simpa [hHaltEq] using hTargetHReturn
  have hHaltOutputTerm :
      haltTerm.output = haltTerm.kind.output haltTerm.state := by
    have hHaltOutput : halt.output = halt.kind.output halt.state := by
      have hTraceHalted := hTrace
      rw [hTarget] at hTraceHalted
      exact hTraceHalted.halted_output
    simpa [hHaltEq] using hHaltOutput
  have hNonReturnEmptyTerm :
      haltTerm.kind ≠ .return →
        yulChild.toMachineState.H_return = ByteArray.empty := by
    intro hNotReturn
    exact
      Program.RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel_nonreturn_H_return_empty
        hTerminalTerm (by
        intro hKindReturn
        exact hNotReturn (hKindTerm.trans hKindReturn))
  have hYulOutput :
      yulChild.toMachineState.H_return = output :=
    terminalReturnData_eq_of_halted_success_H_return
      hTargetHReturnTerm hHaltOutputTerm
      (by simpa [hTargetTerm] using hAgreeSuccess)
      hNonReturnEmptyTerm
  have hRestoreRunActual :
      EvmYul.Yul.restoreSuccessfulContractCallState
          (EvmYul.Yul.addAccessedAccount (.Ok yul store) callee)
          (.Ok yulChild childStore) store
          yulChild.toMachineState.H_return
          inOffset inSize outOffset outSize =
        .ok (.Ok yulAfter store, [⟨1⟩]) := by
    simpa [hYulOutput] using hRestoreRun
  have hCallYul :
      let callee := EvmYul.AccountAddress.ofUInt256 address
      let calldata :=
        yul.toMachineState.memory.readWithPadding
          inOffset.toNat inSize.toNat
      let callGas :=
        EvmYul.EVM.Ccallgas callee callee value gas yul.accountMap
          yul.toMachineState yul.substate
      let yulAccessed : EvmYul.SharedState .Yul :=
        { yul with
          toState := EvmYul.State.addAccessedAccount yul.toState callee }
      let initialShared : EvmYul.SharedState .Yul :=
        { yulAccessed with
          executionEnv :=
            { yulAccessed.executionEnv with
              calldata := calldata
              code := yulRecipient.code
              codeBytes := yulRecipient.codeBytes
              codeOwner := callee
              source := yul.executionEnv.codeOwner
              weiValue := value
              depth := yul.executionEnv.depth + 1 }
          toMachineState :=
            EvmYul.MachineState.freshExternalCall
              (EvmYul.UInt256.ofNat callGas)
          accountMap := yulCallMap }
      EvmYul.Yul.callDispatcher referenceFuel (some yulRecipient.code)
          (.Ok initialShared default) =
        .error (.YulHalt (.Ok yulChild childStore) haltValue) := by
    simpa [hFacts.contract] using hCall
  have hRelAdapter :
      let callee := EvmYul.AccountAddress.ofUInt256 address
      let charged : EvmYul.EVM.State :=
        { evm with
          gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
      let targetGas :=
        (charged.toMachineState.finishExternalCall output
          inOffset inSize outOffset outSize).gasAvailable +
          evmChild.gasAvailable
      Reference.SharedStateRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        yulAfter
        ({ charged with
          toMachineState :=
            { charged.toMachineState.finishExternalCall output
                inOffset inSize outOffset outSize with
              gasAvailable := targetGas }
          accountMap :=
            if evmChild.accountMap.isEmpty then evm.accountMap
            else evmChild.accountMap
          substate :=
            if evmChild.accountMap.isEmpty then
              (EvmYul.State.addAccessedAccount evm.toState callee).substate
            else evmChild.substate
          createdAccounts := evmChild.createdAccounts } :
          EvmYul.EVM.State).toSharedState := by
    simpa [callee, charged, targetGasOf] using hRel
  rcases
      primCall_CALL_ordinary_haltedSuccess_of_theta_restore
        (cfg :=
          stateRelConfig varStackRel terminalCfgRel revertCfgRel
            gasAvailableRel gasValueRel totalGasRel)
        (referenceFuel := referenceFuel)
        (evmThetaFuel := evmFuel.succ.succ)
        (gasCost := gasCost)
        (blobVersionedHashes := yul.executionEnv.blobVersionedHashes)
        (yul := yul) (yulChild := yulChild) (yulAfter := yulAfter)
        (evm := evm) (evmChild := evmChild)
        store childStore
        (gas := gas) (address := address) (value := value)
        (inOffset := inOffset) (inSize := inSize)
        (outOffset := outOffset) (outSize := outSize)
        (yulRecipient := yulRecipient) (yulCallMap := yulCallMap)
        (evmRecipient := evmRecipient) (target := target)
        (haltValue := haltValue) (output := output)
        hShared hStaticAllowed hEnough hDepth hNotPrecompile hFacts.findYul
        hFacts.transfer hFacts.findEvm hFacts.code hCallYul hTheta
        hRestoreRunActual
        hRelAdapter with
    ⟨hEvmCall, hYulCall, hFinalRel⟩
  refine ⟨evmFuel, kindTerm, compilerTerm, haltTerm, evmChild, output,
    yulAfter, ?_⟩
  dsimp
  exact ⟨hTerminalTerm, hWholeHaltedTerm, hKindTerm, hNotRevertTerm,
    hEvmCall, hYulCall, hFinalRel⟩

theorem CALLPrimitiveRel.ordinaryHaltedSuccess_stateRelConfig
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {varStackRel : Reference.VarStackRel}
    {terminalCfgRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop}
    {revertCfgRel : Reference.State → EVMState → Prop}
    {gasAvailableRel : Word → Word → Prop}
    {gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm}
    {totalGasRel : Nat → Nat → Prop}
    {referenceFuel sourceFuel gasCost : Nat}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.EVM.State}
    (hShared :
      Reference.SharedStateRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        yul evm.toSharedState)
    (store childStore : EvmYul.Yul.VarStore)
    {gas address value inOffset inSize outOffset outSize : EvmYul.UInt256}
    {yulRecipient : EvmYul.Account .Yul}
    {yulCallMap : EvmYul.AccountMap .Yul}
    {evmRecipient : EvmYul.Account .EVM}
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    {yulChild : EvmYul.SharedState .Yul}
    {haltValue : EvmYul.UInt256}
    {sourceOutcome : Objects.Source.Outcome}
    (hStaticAllowed :
      ¬ (¬ yul.executionEnv.perm ∧ value ≠ ⟨0⟩))
    (hEnough :
      value ≤
        (evm.accountMap.find? evm.executionEnv.codeOwner |>.option ⟨0⟩
          (·.balance)))
    (hDepth : evm.executionEnv.depth < 1024)
    (hNotPrecompile :
      EvmYul.PrecompiledContract.ofAddress?
        (EvmYul.AccountAddress.ofUInt256 address) = none)
    (hFacts :
      OrdinaryCALLBranchFacts yul evm address value yulRecipient
        yulCallMap evmRecipient program asm target)
    (hCall :
      let callee := EvmYul.AccountAddress.ofUInt256 address
      let calldata :=
        yul.toMachineState.memory.readWithPadding
          inOffset.toNat inSize.toNat
      let callGas :=
        EvmYul.EVM.Ccallgas callee callee value gas yul.accountMap
          yul.toMachineState yul.substate
      let yulAccessed : EvmYul.SharedState .Yul :=
        { yul with
          toState := EvmYul.State.addAccessedAccount yul.toState callee }
      let initialShared : EvmYul.SharedState .Yul :=
        { yulAccessed with
          executionEnv :=
            { yulAccessed.executionEnv with
              calldata := calldata
              code := program.contract
              codeBytes := yulRecipient.codeBytes
              codeOwner := callee
              source := yul.executionEnv.codeOwner
              weiValue := value
              depth := yul.executionEnv.depth + 1 }
          toMachineState :=
            EvmYul.MachineState.freshExternalCall
              (EvmYul.UInt256.ofNat callGas)
          accountMap := yulCallMap }
      EvmYul.Yul.callDispatcher referenceFuel (some program.contract)
          (.Ok initialShared default) =
        .error (.YulHalt (.Ok yulChild childStore) haltValue))
    (hSourceRun :
      let callee := EvmYul.AccountAddress.ofUInt256 address
      let callGas :=
        EvmYul.EVM.Ccallgas callee callee value gas evm.accountMap
          evm.toMachineState evm.substate
      SourceLowered.run prim sourceFuel program
          (Assembly.GasAware.installCodeAndGas target callGas
            (thetaCodeRawInitialState target callGas
              yul.executionEnv.blobVersionedHashes evm.createdAccounts
              evm.genesisBlockHeader evm.blocks evm.accountMap evm.σ₀
              { totalGasUsedInBlock := evm.totalGasUsedInBlock
                transactionReceipts := evm.transactionReceipts }
              (EvmYul.State.addAccessedAccount evm.toState callee).substate
              evm.executionEnv.codeOwner evm.executionEnv.sender callee
              (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice) value value
              (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
              (evm.executionEnv.depth + 1) evm.executionEnv.header
              evm.executionEnv.perm)) =
        .ok sourceOutcome)
    (hOutcomeRel :
      let callee := EvmYul.AccountAddress.ofUInt256 address
      let calldata :=
        yul.toMachineState.memory.readWithPadding
          inOffset.toNat inSize.toNat
      let callGas :=
        EvmYul.EVM.Ccallgas callee callee value gas yul.accountMap
          yul.toMachineState yul.substate
      let yulAccessed : EvmYul.SharedState .Yul :=
        { yul with
          toState := EvmYul.State.addAccessedAccount yul.toState callee }
      let initialShared : EvmYul.SharedState .Yul :=
        { yulAccessed with
          executionEnv :=
            { yulAccessed.executionEnv with
              calldata := calldata
              code := program.contract
              codeBytes := yulRecipient.codeBytes
              codeOwner := callee
              source := yul.executionEnv.codeOwner
              weiValue := value
              depth := yul.executionEnv.depth + 1 }
          toMachineState :=
            EvmYul.MachineState.freshExternalCall
              (EvmYul.UInt256.ofNat callGas)
          accountMap := yulCallMap }
      Program.RecursiveBridgeSemanticContracts.dispatcherOutcomeRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        (Program.RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel
          (stateRelConfig varStackRel terminalCfgRel revertCfgRel
            gasAvailableRel gasValueRel totalGasRel))
        (Program.RecursiveBridgeTerminalObservationContracts.canonicalRevertRel
          (stateRelConfig varStackRel terminalCfgRel revertCfgRel
            gasAvailableRel gasValueRel totalGasRel))
        program (.Ok initialShared default)
        (.yulHalt (.Ok yulChild childStore) haltValue) sourceOutcome)
    (hTargetGasForX :
      let callee := EvmYul.AccountAddress.ofUInt256 address
      let callGas :=
        EvmYul.EVM.Ccallgas callee callee value gas evm.accountMap
          evm.toMachineState evm.substate
      ∀ {targetFuel targetOutcome},
        Assembly.Preservation.BlockTraceResult asm target targetFuel
          (Assembly.GasAware.installCodeAndGas target callGas
            (thetaCodeRawInitialState target callGas
              yul.executionEnv.blobVersionedHashes evm.createdAccounts
              evm.genesisBlockHeader evm.blocks evm.accountMap evm.σ₀
              { totalGasUsedInBlock := evm.totalGasUsedInBlock
                transactionReceipts := evm.transactionReceipts }
              (EvmYul.State.addAccessedAccount evm.toState callee).substate
              evm.executionEnv.codeOwner evm.executionEnv.sender callee
              (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice) value value
              (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
              (evm.executionEnv.depth + 1) evm.executionEnv.header
              evm.executionEnv.perm))
          targetOutcome →
        Assembly.GasAware.XResultPreconditionAssumptions target
          (Assembly.GasAware.installCodeAndGas target callGas
            (thetaCodeRawInitialState target callGas
              yul.executionEnv.blobVersionedHashes evm.createdAccounts
              evm.genesisBlockHeader evm.blocks evm.accountMap evm.σ₀
              { totalGasUsedInBlock := evm.totalGasUsedInBlock
                transactionReceipts := evm.transactionReceipts }
              (EvmYul.State.addAccessedAccount evm.toState callee).substate
              evm.executionEnv.codeOwner evm.executionEnv.sender callee
              (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice) value value
              (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
              (evm.executionEnv.depth + 1) evm.executionEnv.header
              evm.executionEnv.perm))
          targetOutcome)
    (hGasBound :
      let callee := EvmYul.AccountAddress.ofUInt256 address
      let callGas :=
        EvmYul.EVM.Ccallgas callee callee value gas evm.accountMap
          evm.toMachineState evm.substate
      ∀ {targetFuel targetOutcome}
        (hTrace :
          Assembly.Preservation.BlockTraceResult asm target targetFuel
            (Assembly.GasAware.installCodeAndGas target callGas
              (thetaCodeRawInitialState target callGas
                yul.executionEnv.blobVersionedHashes evm.createdAccounts
                evm.genesisBlockHeader evm.blocks evm.accountMap evm.σ₀
                { totalGasUsedInBlock := evm.totalGasUsedInBlock
                  transactionReceipts := evm.transactionReceipts }
                (EvmYul.State.addAccessedAccount evm.toState callee).substate
                evm.executionEnv.codeOwner evm.executionEnv.sender callee
                (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice) value value
                (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
                (evm.executionEnv.depth + 1) evm.executionEnv.header
                evm.executionEnv.perm))
            targetOutcome),
        (hTargetGasForX hTrace).gasBound ≤ callGas)
    (hUInt256 :
      EvmYul.EVM.Ccallgas (EvmYul.AccountAddress.ofUInt256 address)
          (EvmYul.AccountAddress.ofUInt256 address) value gas
          evm.accountMap evm.toMachineState evm.substate <
        EvmYul.UInt256.size)
    (hReturnedGas :
      ∀ {targetOutcome evmChild output},
        SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome →
          Assembly.GasAware.XResultAgrees targetOutcome
            (.success evmChild output) →
          let charged : EvmYul.EVM.State :=
            { evm with
              gasAvailable :=
                evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
          gasAvailableRel
            (yul.toMachineState.finishExternalCall output
              inOffset inSize outOffset outSize).gasAvailable
            ((charged.toMachineState.finishExternalCall output
                inOffset inSize outOffset outSize).gasAvailable +
              evmChild.gasAvailable)) :
    ∃ (evmFuel : Nat),
      CALLPrimitiveRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        referenceFuel.succ evmFuel.succ.succ.succ gasCost
        yul.executionEnv.blobVersionedHashes yul evm store
        gas address value inOffset inSize outOffset outSize := by
  rcases
      primCall_CALL_ordinary_haltedSuccess_rel_of_installed_childDispatcher_afterAccess_withTargetGas
        hPrim hShared store childStore hStaticAllowed hEnough hDepth
        hNotPrecompile hFacts hCall hSourceRun hOutcomeRel
        hTargetGasForX hGasBound hUInt256 hReturnedGas with
    ⟨evmFuel, _kind, _compiler, _halt, _evmChild, _output, yulAfter,
      _hTerminal, _hWhole, _hKind, _hNonRevert, hEvmCall, hYulCall,
      hFinalRel⟩
  exact ⟨evmFuel, ⟨⟨1⟩, _, yulAfter, hEvmCall, hYulCall, hFinalRel⟩⟩

theorem primCall_CALL_ordinary_revert_rel_of_installed_childDispatcher_afterAccess_withTargetGas
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {varStackRel : Reference.VarStackRel}
    {terminalCfgRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop}
    {revertCfgRel : Reference.State → EVMState → Prop}
    {gasAvailableRel : Word → Word → Prop}
    {gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm}
    {totalGasRel : Nat → Nat → Prop}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {referenceFuel sourceFuel gasCost : Nat}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.EVM.State}
    (hShared :
      Reference.SharedStateRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        yul evm.toSharedState)
    (store childStore : EvmYul.Yul.VarStore)
    {gas address value inOffset inSize outOffset outSize : EvmYul.UInt256}
    {yulRecipient : EvmYul.Account .Yul}
    {yulCallMap : EvmYul.AccountMap .Yul}
    {evmRecipient : EvmYul.Account .EVM}
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    {yulChild : EvmYul.SharedState .Yul}
    {sourceOutcome : Objects.Source.Outcome}
    (hStaticAllowed :
      ¬ (¬ yul.executionEnv.perm ∧ value ≠ ⟨0⟩))
    (hEnough :
      value ≤
        (evm.accountMap.find? evm.executionEnv.codeOwner |>.option ⟨0⟩
          (·.balance)))
    (hDepth : evm.executionEnv.depth < 1024)
    (hNotPrecompile :
      EvmYul.PrecompiledContract.ofAddress?
        (EvmYul.AccountAddress.ofUInt256 address) = none)
    (hFacts :
      OrdinaryCALLBranchFacts yul evm address value yulRecipient
        yulCallMap evmRecipient program asm target)
    (hCall :
      let callee := EvmYul.AccountAddress.ofUInt256 address
      let calldata :=
        yul.toMachineState.memory.readWithPadding
          inOffset.toNat inSize.toNat
      let callGas :=
        EvmYul.EVM.Ccallgas callee callee value gas yul.accountMap
          yul.toMachineState yul.substate
      let yulAccessed : EvmYul.SharedState .Yul :=
        { yul with
          toState := EvmYul.State.addAccessedAccount yul.toState callee }
      let initialShared : EvmYul.SharedState .Yul :=
        { yulAccessed with
          executionEnv :=
            { yulAccessed.executionEnv with
              calldata := calldata
              code := program.contract
              codeBytes := yulRecipient.codeBytes
              codeOwner := callee
              source := yul.executionEnv.codeOwner
              weiValue := value
              depth := yul.executionEnv.depth + 1 }
          toMachineState :=
            EvmYul.MachineState.freshExternalCall
              (EvmYul.UInt256.ofNat callGas)
          accountMap := yulCallMap }
      EvmYul.Yul.callDispatcher referenceFuel (some program.contract)
          (.Ok initialShared default) =
        .error (.Revert (.Ok yulChild childStore)))
    (hSourceRun :
      let callee := EvmYul.AccountAddress.ofUInt256 address
      let callGas :=
        EvmYul.EVM.Ccallgas callee callee value gas evm.accountMap
          evm.toMachineState evm.substate
      SourceLowered.run prim sourceFuel program
          (Assembly.GasAware.installCodeAndGas target callGas
            (thetaCodeRawInitialState target callGas
              yul.executionEnv.blobVersionedHashes evm.createdAccounts
              evm.genesisBlockHeader evm.blocks evm.accountMap evm.σ₀
              { totalGasUsedInBlock := evm.totalGasUsedInBlock
                transactionReceipts := evm.transactionReceipts }
              (EvmYul.State.addAccessedAccount evm.toState callee).substate
              evm.executionEnv.codeOwner evm.executionEnv.sender callee
              (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice) value value
              (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
              (evm.executionEnv.depth + 1) evm.executionEnv.header
              evm.executionEnv.perm)) =
        .ok sourceOutcome)
    (hOutcomeRel :
      let callee := EvmYul.AccountAddress.ofUInt256 address
      let calldata :=
        yul.toMachineState.memory.readWithPadding
          inOffset.toNat inSize.toNat
      let callGas :=
        EvmYul.EVM.Ccallgas callee callee value gas yul.accountMap
          yul.toMachineState yul.substate
      let yulAccessed : EvmYul.SharedState .Yul :=
        { yul with
          toState := EvmYul.State.addAccessedAccount yul.toState callee }
      let initialShared : EvmYul.SharedState .Yul :=
        { yulAccessed with
          executionEnv :=
            { yulAccessed.executionEnv with
              calldata := calldata
              code := program.contract
              codeBytes := yulRecipient.codeBytes
              codeOwner := callee
              source := yul.executionEnv.codeOwner
              weiValue := value
              depth := yul.executionEnv.depth + 1 }
          toMachineState :=
            EvmYul.MachineState.freshExternalCall
              (EvmYul.UInt256.ofNat callGas)
          accountMap := yulCallMap }
      Program.RecursiveBridgeSemanticContracts.dispatcherOutcomeRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        terminalRel revertRel program (.Ok initialShared default)
        (.revert (.Ok yulChild childStore)) sourceOutcome)
    (hRevertShared :
      ∀ {compiler},
        revertRel (.Ok yulChild childStore) compiler →
          Reference.SharedStateRel
            (stateRelConfig varStackRel terminalCfgRel revertCfgRel
              gasAvailableRel gasValueRel totalGasRel)
            yulChild compiler.shared)
    (hTargetGasForX :
      let callee := EvmYul.AccountAddress.ofUInt256 address
      let callGas :=
        EvmYul.EVM.Ccallgas callee callee value gas evm.accountMap
          evm.toMachineState evm.substate
      ∀ {targetFuel targetOutcome},
        Assembly.Preservation.BlockTraceResult asm target targetFuel
          (Assembly.GasAware.installCodeAndGas target callGas
            (thetaCodeRawInitialState target callGas
              yul.executionEnv.blobVersionedHashes evm.createdAccounts
              evm.genesisBlockHeader evm.blocks evm.accountMap evm.σ₀
              { totalGasUsedInBlock := evm.totalGasUsedInBlock
                transactionReceipts := evm.transactionReceipts }
              (EvmYul.State.addAccessedAccount evm.toState callee).substate
              evm.executionEnv.codeOwner evm.executionEnv.sender callee
              (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice) value value
              (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
              (evm.executionEnv.depth + 1) evm.executionEnv.header
              evm.executionEnv.perm))
          targetOutcome →
        Assembly.GasAware.XResultPreconditionAssumptions target
          (Assembly.GasAware.installCodeAndGas target callGas
            (thetaCodeRawInitialState target callGas
              yul.executionEnv.blobVersionedHashes evm.createdAccounts
              evm.genesisBlockHeader evm.blocks evm.accountMap evm.σ₀
              { totalGasUsedInBlock := evm.totalGasUsedInBlock
                transactionReceipts := evm.transactionReceipts }
              (EvmYul.State.addAccessedAccount evm.toState callee).substate
              evm.executionEnv.codeOwner evm.executionEnv.sender callee
              (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice) value value
              (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
              (evm.executionEnv.depth + 1) evm.executionEnv.header
              evm.executionEnv.perm))
          targetOutcome)
    (hGasBound :
      let callee := EvmYul.AccountAddress.ofUInt256 address
      let callGas :=
        EvmYul.EVM.Ccallgas callee callee value gas evm.accountMap
          evm.toMachineState evm.substate
      ∀ {targetFuel targetOutcome}
        (hTrace :
          Assembly.Preservation.BlockTraceResult asm target targetFuel
            (Assembly.GasAware.installCodeAndGas target callGas
              (thetaCodeRawInitialState target callGas
                yul.executionEnv.blobVersionedHashes evm.createdAccounts
                evm.genesisBlockHeader evm.blocks evm.accountMap evm.σ₀
                { totalGasUsedInBlock := evm.totalGasUsedInBlock
                  transactionReceipts := evm.transactionReceipts }
                (EvmYul.State.addAccessedAccount evm.toState callee).substate
                evm.executionEnv.codeOwner evm.executionEnv.sender callee
                (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice) value value
                (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
                (evm.executionEnv.depth + 1) evm.executionEnv.header
                evm.executionEnv.perm))
            targetOutcome),
        (hTargetGasForX hTrace).gasBound ≤ callGas)
    (hUInt256 :
      EvmYul.EVM.Ccallgas (EvmYul.AccountAddress.ofUInt256 address)
          (EvmYul.AccountAddress.ofUInt256 address) value gas
          evm.accountMap evm.toMachineState evm.substate <
        EvmYul.UInt256.size)
    (hTargetChildGas :
      ∀ {halt}, SourceLowered.WholeProgramOutcomeRel sourceOutcome
          (.halted halt) →
        gasAvailableRel yulChild.toMachineState.gasAvailable
          halt.state.gasAvailable)
    (hReturnedGas :
      ∀ {targetOutcome returnedGas output},
        SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome →
          Assembly.GasAware.XResultAgrees targetOutcome
            (.revert returnedGas output) →
          let charged : EvmYul.EVM.State :=
            { evm with
              gasAvailable :=
                evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
          gasAvailableRel
            (yul.toMachineState.finishExternalCall output
              inOffset inSize outOffset outSize).gasAvailable
            ((charged.toMachineState.finishExternalCall output
                inOffset inSize outOffset outSize).gasAvailable +
              returnedGas)) :
    ∃ (evmFuel : Nat) (compiler : Objects.Source.State)
      (halt : Assembly.Halt) (returnedGas : EvmYul.UInt256)
      (output : ByteArray) (yulAfter : EvmYul.SharedState .Yul),
      let callee := EvmYul.AccountAddress.ofUInt256 address
      let charged : EvmYul.EVM.State :=
        { evm with
          gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
      let targetGas :=
        (charged.toMachineState.finishExternalCall output
          inOffset inSize outOffset outSize).gasAvailable +
          returnedGas
      let evmAfter : EvmYul.EVM.State :=
        { charged with
          toMachineState :=
            { charged.toMachineState.finishExternalCall output
                inOffset inSize outOffset outSize with
              gasAvailable := targetGas }
          accountMap := evm.accountMap
          substate :=
            (EvmYul.State.addAccessedAccount evm.toState callee).substate
          createdAccounts := evm.createdAccounts }
      SourceLowered.WholeProgramOutcomeRel sourceOutcome (.halted halt) ∧
      halt.kind = .revert ∧
      revertRel (.Ok yulChild childStore) compiler ∧
      EvmYul.EVM.call evmFuel.succ.succ.succ gasCost
          yul.executionEnv.blobVersionedHashes gas
          (EvmYul.UInt256.ofNat evm.executionEnv.codeOwner) address address
          value value inOffset inSize outOffset outSize
          evm.executionEnv.perm evm =
        .ok (⟨0⟩, evmAfter) ∧
      EvmYul.Yul.primCall referenceFuel.succ (.Ok yul store) .CALL
          [gas, address, value, inOffset, inSize, outOffset, outSize] =
        .ok (.Ok yulAfter store, [⟨0⟩]) ∧
      Reference.SharedStateRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        yulAfter evmAfter.toSharedState := by
  dsimp at hCall hSourceRun hOutcomeRel hTargetGasForX hGasBound hReturnedGas ⊢
  let callee := EvmYul.AccountAddress.ofUInt256 address
  let callGasYul :=
    EvmYul.EVM.Ccallgas callee callee value gas yul.accountMap
      yul.toMachineState yul.substate
  let callGasEvm :=
    EvmYul.EVM.Ccallgas callee callee value gas evm.accountMap
      evm.toMachineState evm.substate
  let yulAccessed : EvmYul.SharedState .Yul :=
    { yul with
      toState := EvmYul.State.addAccessedAccount yul.toState callee }
  let initialShared : EvmYul.SharedState .Yul :=
    { yulAccessed with
      executionEnv :=
        { yulAccessed.executionEnv with
          calldata :=
            yul.toMachineState.memory.readWithPadding
              inOffset.toNat inSize.toNat
          code := program.contract
          codeBytes := yulRecipient.codeBytes
          codeOwner := callee
          source := yul.executionEnv.codeOwner
          weiValue := value
          depth := yul.executionEnv.depth + 1 }
      toMachineState :=
        EvmYul.MachineState.freshExternalCall
          (EvmYul.UInt256.ofNat callGasYul)
      accountMap := yulCallMap }
  let charged : EvmYul.EVM.State :=
    { evm with
      gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
  let targetGasOf : EvmYul.UInt256 → ByteArray → EvmYul.UInt256 :=
    fun returnedGas output =>
      (charged.toMachineState.finishExternalCall output
        inOffset inSize outOffset outSize).gasAvailable +
        returnedGas
  have hInstalled :
      initialShared.executionEnv.code = program.contract := by
    simp [initialShared]
  have hCall' :
      EvmYul.Yul.callDispatcher referenceFuel (some program.contract)
          (.Ok initialShared default) =
        .error (.Revert (.Ok yulChild childStore)) := by
    simpa [initialShared, yulAccessed, callGasYul, callee] using hCall
  have hSourceRun' :
      SourceLowered.run prim sourceFuel program
          (Assembly.GasAware.installCodeAndGas target callGasEvm
            (thetaCodeRawInitialState target callGasEvm
              yul.executionEnv.blobVersionedHashes evm.createdAccounts
              evm.genesisBlockHeader evm.blocks evm.accountMap evm.σ₀
              { totalGasUsedInBlock := evm.totalGasUsedInBlock
                transactionReceipts := evm.transactionReceipts }
              (EvmYul.State.addAccessedAccount evm.toState callee).substate
              evm.executionEnv.codeOwner evm.executionEnv.sender callee
              (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice) value value
              (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
              (evm.executionEnv.depth + 1) evm.executionEnv.header
              evm.executionEnv.perm)) =
        .ok sourceOutcome := by
    simpa [callGasEvm, callee] using hSourceRun
  have hOutcomeRel' :
      Program.RecursiveBridgeSemanticContracts.dispatcherOutcomeRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        terminalRel revertRel program (.Ok initialShared default)
        (.revert (.Ok yulChild childStore)) sourceOutcome := by
    simpa [initialShared, yulAccessed, callGasYul, callee] using hOutcomeRel
  let hTargetGasForX' :
      ∀ {targetFuel targetOutcome},
        Assembly.Preservation.BlockTraceResult asm target targetFuel
          (Assembly.GasAware.installCodeAndGas target callGasEvm
            (thetaCodeRawInitialState target callGasEvm
              yul.executionEnv.blobVersionedHashes evm.createdAccounts
              evm.genesisBlockHeader evm.blocks evm.accountMap evm.σ₀
              { totalGasUsedInBlock := evm.totalGasUsedInBlock
                transactionReceipts := evm.transactionReceipts }
              (EvmYul.State.addAccessedAccount evm.toState callee).substate
              evm.executionEnv.codeOwner evm.executionEnv.sender callee
              (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice) value value
              (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
              (evm.executionEnv.depth + 1) evm.executionEnv.header
              evm.executionEnv.perm))
          targetOutcome →
        Assembly.GasAware.XResultPreconditionAssumptions target
          (Assembly.GasAware.installCodeAndGas target callGasEvm
            (thetaCodeRawInitialState target callGasEvm
              yul.executionEnv.blobVersionedHashes evm.createdAccounts
              evm.genesisBlockHeader evm.blocks evm.accountMap evm.σ₀
              { totalGasUsedInBlock := evm.totalGasUsedInBlock
                transactionReceipts := evm.transactionReceipts }
              (EvmYul.State.addAccessedAccount evm.toState callee).substate
              evm.executionEnv.codeOwner evm.executionEnv.sender callee
              (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice) value value
              (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
              (evm.executionEnv.depth + 1) evm.executionEnv.header
              evm.executionEnv.perm))
          targetOutcome := by
    intro targetFuel targetOutcome hTrace
    exact hTargetGasForX (by simpa [callGasEvm, callee] using hTrace)
  have hGasBound' :
      ∀ {targetFuel targetOutcome}
        (hTrace :
          Assembly.Preservation.BlockTraceResult asm target targetFuel
            (Assembly.GasAware.installCodeAndGas target callGasEvm
              (thetaCodeRawInitialState target callGasEvm
                yul.executionEnv.blobVersionedHashes evm.createdAccounts
                evm.genesisBlockHeader evm.blocks evm.accountMap evm.σ₀
                { totalGasUsedInBlock := evm.totalGasUsedInBlock
                  transactionReceipts := evm.transactionReceipts }
                (EvmYul.State.addAccessedAccount evm.toState callee).substate
                evm.executionEnv.codeOwner evm.executionEnv.sender callee
                (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice) value value
                (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
                (evm.executionEnv.depth + 1) evm.executionEnv.header
                evm.executionEnv.perm))
            targetOutcome),
        (hTargetGasForX' hTrace).gasBound ≤ callGasEvm := by
    intro targetFuel targetOutcome hTrace
    dsimp [hTargetGasForX']
    simpa [callGasEvm, callee] using
      hGasBound (by simpa [callGasEvm, callee] using hTrace)
  have hUInt256' : callGasEvm < EvmYul.UInt256.size := by
    simpa [callGasEvm, callee] using hUInt256
  rcases
      compile_preserves_of_installed_callDispatcher_revert_sourceStaticBoundary_installedGas_XResult
        (prim := prim) hPrim
        (outcomeRel :=
          Program.RecursiveBridgeSemanticContracts.dispatcherOutcomeRel
            (stateRelConfig varStackRel terminalCfgRel revertCfgRel
              gasAvailableRel gasValueRel totalGasRel)
            terminalRel revertRel program (.Ok initialShared default))
        (program := program) (asm := asm) (target := target)
        (referenceFuel := referenceFuel) (sourceFuel := sourceFuel)
        (gas := callGasEvm) (shared := initialShared)
        (store := default) (revertState := .Ok yulChild childStore)
        (rawInitial :=
          thetaCodeRawInitialState target callGasEvm
            yul.executionEnv.blobVersionedHashes evm.createdAccounts
            evm.genesisBlockHeader evm.blocks evm.accountMap evm.σ₀
            { totalGasUsedInBlock := evm.totalGasUsedInBlock
              transactionReceipts := evm.transactionReceipts }
            (EvmYul.State.addAccessedAccount evm.toState callee).substate
            evm.executionEnv.codeOwner evm.executionEnv.sender callee
            (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice) value value
            (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
            (evm.executionEnv.depth + 1) evm.executionEnv.header
            evm.executionEnv.perm)
        (sourceOutcome := sourceOutcome)
        hInstalled hCall' hSourceRun' hOutcomeRel' hFacts.compileBoundary
        (by
          simp [thetaCodeRawInitialState, Assembly.GasAware.installCodeAndGas])
        (by
          simp [thetaCodeRawInitialState, Assembly.GasAware.installCodeAndGas])
        hTargetGasForX' hGasBound' hUInt256' with
    ⟨targetFuel, targetOutcome, evmFuel, _gasBound, evmResult,
      _hReferenceRun, _hTargetRun, _hOutcomeRel, hWhole, hTrace,
      _hGasBound, hX, hAgree, _hDecode, _hJumpdest⟩
  have hXTheta :
      EvmYul.EVM.X evmFuel (Assembly.GasAware.validJumps target)
          (thetaCodeXInitialState target callGasEvm
            yul.executionEnv.blobVersionedHashes evm.createdAccounts
            evm.genesisBlockHeader evm.blocks evm.accountMap evm.σ₀
            { totalGasUsedInBlock := evm.totalGasUsedInBlock
              transactionReceipts := evm.transactionReceipts }
            (EvmYul.State.addAccessedAccount evm.toState callee).substate
            evm.executionEnv.codeOwner evm.executionEnv.sender callee
            (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice) value value
            (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
            (evm.executionEnv.depth + 1) evm.executionEnv.header
            evm.executionEnv.perm) =
        .ok evmResult := by
    simpa [thetaCodeXInitialState] using hX
  rcases
      dispatcherOutcomeRel_revert_ok_whole_childRelations
        (varStackRel := varStackRel)
        (terminalCfgRel := terminalCfgRel)
        (revertCfgRel := revertCfgRel)
          (gasAvailableRel := gasAvailableRel)
          (gasValueRel := gasValueRel)
          (totalGasRel := totalGasRel)
          hOutcomeRel' hWhole hRevertShared
          (by
            intro halt hTarget
            exact hTargetChildGas (by simpa [hTarget] using hWhole)) with
    ⟨compiler, halt, hRevert, _hSource, hTarget, hKind,
      hTargetChild, _hTargetChildWorld⟩
  have hAgreeHalted :
      Assembly.GasAware.XResultAgrees (.halted halt) evmResult := by
    simpa [hTarget] using hAgree
  rcases XResultAgrees_halted_revert_shape hAgreeHalted hKind with
    ⟨returnedGas, output, hResult, hAgreeRevert⟩
  have hXRevert :
      EvmYul.EVM.X evmFuel (Assembly.GasAware.validJumps target)
          (thetaCodeXInitialState target callGasEvm
            yul.executionEnv.blobVersionedHashes evm.createdAccounts
            evm.genesisBlockHeader evm.blocks evm.accountMap evm.σ₀
            { totalGasUsedInBlock := evm.totalGasUsedInBlock
              transactionReceipts := evm.transactionReceipts }
            (EvmYul.State.addAccessedAccount evm.toState callee).substate
            evm.executionEnv.codeOwner evm.executionEnv.sender callee
            (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice) value value
            (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
            (evm.executionEnv.depth + 1) evm.executionEnv.header
            evm.executionEnv.perm) =
        .ok (.revert returnedGas output) := by
    simpa [hResult] using hXTheta
  have hTraceHalt :
      Assembly.Preservation.BlockTraceResult asm target targetFuel
        (Assembly.GasAware.installCodeAndGas target callGasEvm
          (thetaCodeRawInitialState target callGasEvm
            yul.executionEnv.blobVersionedHashes evm.createdAccounts
            evm.genesisBlockHeader evm.blocks evm.accountMap evm.σ₀
            { totalGasUsedInBlock := evm.totalGasUsedInBlock
              transactionReceipts := evm.transactionReceipts }
            (EvmYul.State.addAccessedAccount evm.toState callee).substate
            evm.executionEnv.codeOwner evm.executionEnv.sender callee
            (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice) value value
            (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
            (evm.executionEnv.depth + 1) evm.executionEnv.header
            evm.executionEnv.perm))
        (.halted halt) := by
    simpa [hTarget] using hTrace
  have hTargetGas :
      gasAvailableRel
        (yul.toMachineState.finishExternalCall output
          inOffset inSize outOffset outSize).gasAvailable
        (targetGasOf returnedGas output) := by
    simpa [targetGasOf, charged] using
      hReturnedGas hWhole (by simpa [hResult] using hAgree)
  rcases
      ordinaryCodeCall_revertBranch_rel_withTargetGas
        (cfg :=
          stateRelConfig varStackRel terminalCfgRel revertCfgRel
            gasAvailableRel gasValueRel totalGasRel)
        hShared store childStore callee hTargetChild hTraceHalt
        hXRevert hAgreeRevert inOffset inSize outOffset outSize
        hTargetGas with
    ⟨hTheta, _hKind, yulAfter, hRestoreRun, hRel⟩
  have hCallYul :
      let callee := EvmYul.AccountAddress.ofUInt256 address
      let calldata :=
        yul.toMachineState.memory.readWithPadding
          inOffset.toNat inSize.toNat
      let callGas :=
        EvmYul.EVM.Ccallgas callee callee value gas yul.accountMap
          yul.toMachineState yul.substate
      let yulAccessed : EvmYul.SharedState .Yul :=
        { yul with
          toState := EvmYul.State.addAccessedAccount yul.toState callee }
      let initialShared : EvmYul.SharedState .Yul :=
        { yulAccessed with
          executionEnv :=
            { yulAccessed.executionEnv with
              calldata := calldata
              code := yulRecipient.code
              codeBytes := yulRecipient.codeBytes
              codeOwner := callee
              source := yul.executionEnv.codeOwner
              weiValue := value
              depth := yul.executionEnv.depth + 1 }
          toMachineState :=
            EvmYul.MachineState.freshExternalCall
              (EvmYul.UInt256.ofNat callGas)
          accountMap := yulCallMap }
      EvmYul.Yul.callDispatcher referenceFuel (some yulRecipient.code)
          (.Ok initialShared default) =
        .error (.Revert (.Ok yulChild childStore)) := by
    simpa [hFacts.contract] using hCall
  have hRelAdapter :
      let callee := EvmYul.AccountAddress.ofUInt256 address
      let charged : EvmYul.EVM.State :=
        { evm with
          gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
      let targetGas :=
        (charged.toMachineState.finishExternalCall output
          inOffset inSize outOffset outSize).gasAvailable +
          returnedGas
      Reference.SharedStateRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        yulAfter
        ({ charged with
          toMachineState :=
            { charged.toMachineState.finishExternalCall output
                inOffset inSize outOffset outSize with
              gasAvailable := targetGas }
          accountMap := evm.accountMap
          substate :=
            (EvmYul.State.addAccessedAccount evm.toState callee).substate
          createdAccounts := evm.createdAccounts } :
          EvmYul.EVM.State).toSharedState := by
    simpa [callee, charged, targetGasOf] using hRel
  rcases
      primCall_CALL_ordinary_revert_of_theta_restore
        (cfg :=
          stateRelConfig varStackRel terminalCfgRel revertCfgRel
            gasAvailableRel gasValueRel totalGasRel)
        (referenceFuel := referenceFuel)
        (evmThetaFuel := evmFuel.succ.succ)
        (gasCost := gasCost)
        (blobVersionedHashes := yul.executionEnv.blobVersionedHashes)
        (yul := yul) (yulChild := yulChild) (yulAfter := yulAfter)
        (evm := evm)
        store childStore
        (gas := gas) (address := address) (value := value)
        (inOffset := inOffset) (inSize := inSize)
        (outOffset := outOffset) (outSize := outSize)
        (yulRecipient := yulRecipient) (yulCallMap := yulCallMap)
        (evmRecipient := evmRecipient) (target := target)
        (returnedGas := returnedGas) (output := output)
          hShared hStaticAllowed hEnough hDepth hNotPrecompile hFacts.findYul
          hFacts.transfer hFacts.findEvm hFacts.code hCallYul hTheta hRestoreRun
          hRelAdapter with
    ⟨hEvmCall, hYulCall, hFinalRel⟩
  refine ⟨evmFuel, compiler, halt, returnedGas, output, yulAfter, ?_⟩
  dsimp
  exact ⟨by simpa [hTarget] using hWhole, hKind, hRevert,
    hEvmCall, hYulCall, hFinalRel⟩

theorem CALLPrimitiveRel.ordinaryRevert_stateRelConfig
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {varStackRel : Reference.VarStackRel}
    {terminalCfgRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop}
    {revertCfgRel : Reference.State → EVMState → Prop}
    {gasAvailableRel : Word → Word → Prop}
    {gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm}
    {totalGasRel : Nat → Nat → Prop}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {referenceFuel sourceFuel gasCost : Nat}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.EVM.State}
    (hShared :
      Reference.SharedStateRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        yul evm.toSharedState)
    (store childStore : EvmYul.Yul.VarStore)
    {gas address value inOffset inSize outOffset outSize : EvmYul.UInt256}
    {yulRecipient : EvmYul.Account .Yul}
    {yulCallMap : EvmYul.AccountMap .Yul}
    {evmRecipient : EvmYul.Account .EVM}
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    {yulChild : EvmYul.SharedState .Yul}
    {sourceOutcome : Objects.Source.Outcome}
    (hStaticAllowed :
      ¬ (¬ yul.executionEnv.perm ∧ value ≠ ⟨0⟩))
    (hEnough :
      value ≤
        (evm.accountMap.find? evm.executionEnv.codeOwner |>.option ⟨0⟩
          (·.balance)))
    (hDepth : evm.executionEnv.depth < 1024)
    (hNotPrecompile :
      EvmYul.PrecompiledContract.ofAddress?
        (EvmYul.AccountAddress.ofUInt256 address) = none)
    (hFacts :
      OrdinaryCALLBranchFacts yul evm address value yulRecipient
        yulCallMap evmRecipient program asm target)
    (hCall :
      let callee := EvmYul.AccountAddress.ofUInt256 address
      let calldata :=
        yul.toMachineState.memory.readWithPadding
          inOffset.toNat inSize.toNat
      let callGas :=
        EvmYul.EVM.Ccallgas callee callee value gas yul.accountMap
          yul.toMachineState yul.substate
      let yulAccessed : EvmYul.SharedState .Yul :=
        { yul with
          toState := EvmYul.State.addAccessedAccount yul.toState callee }
      let initialShared : EvmYul.SharedState .Yul :=
        { yulAccessed with
          executionEnv :=
            { yulAccessed.executionEnv with
              calldata := calldata
              code := program.contract
              codeBytes := yulRecipient.codeBytes
              codeOwner := callee
              source := yul.executionEnv.codeOwner
              weiValue := value
              depth := yul.executionEnv.depth + 1 }
          toMachineState :=
            EvmYul.MachineState.freshExternalCall
              (EvmYul.UInt256.ofNat callGas)
          accountMap := yulCallMap }
      EvmYul.Yul.callDispatcher referenceFuel (some program.contract)
          (.Ok initialShared default) =
        .error (.Revert (.Ok yulChild childStore)))
    (hSourceRun :
      let callee := EvmYul.AccountAddress.ofUInt256 address
      let callGas :=
        EvmYul.EVM.Ccallgas callee callee value gas evm.accountMap
          evm.toMachineState evm.substate
      SourceLowered.run prim sourceFuel program
          (Assembly.GasAware.installCodeAndGas target callGas
            (thetaCodeRawInitialState target callGas
              yul.executionEnv.blobVersionedHashes evm.createdAccounts
              evm.genesisBlockHeader evm.blocks evm.accountMap evm.σ₀
              { totalGasUsedInBlock := evm.totalGasUsedInBlock
                transactionReceipts := evm.transactionReceipts }
              (EvmYul.State.addAccessedAccount evm.toState callee).substate
              evm.executionEnv.codeOwner evm.executionEnv.sender callee
              (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice) value value
              (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
              (evm.executionEnv.depth + 1) evm.executionEnv.header
              evm.executionEnv.perm)) =
        .ok sourceOutcome)
    (hOutcomeRel :
      let callee := EvmYul.AccountAddress.ofUInt256 address
      let calldata :=
        yul.toMachineState.memory.readWithPadding
          inOffset.toNat inSize.toNat
      let callGas :=
        EvmYul.EVM.Ccallgas callee callee value gas yul.accountMap
          yul.toMachineState yul.substate
      let yulAccessed : EvmYul.SharedState .Yul :=
        { yul with
          toState := EvmYul.State.addAccessedAccount yul.toState callee }
      let initialShared : EvmYul.SharedState .Yul :=
        { yulAccessed with
          executionEnv :=
            { yulAccessed.executionEnv with
              calldata := calldata
              code := program.contract
              codeBytes := yulRecipient.codeBytes
              codeOwner := callee
              source := yul.executionEnv.codeOwner
              weiValue := value
              depth := yul.executionEnv.depth + 1 }
          toMachineState :=
            EvmYul.MachineState.freshExternalCall
              (EvmYul.UInt256.ofNat callGas)
          accountMap := yulCallMap }
      Program.RecursiveBridgeSemanticContracts.dispatcherOutcomeRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        terminalRel revertRel program (.Ok initialShared default)
        (.revert (.Ok yulChild childStore)) sourceOutcome)
    (hRevertShared :
      ∀ {compiler},
        revertRel (.Ok yulChild childStore) compiler →
          Reference.SharedStateRel
            (stateRelConfig varStackRel terminalCfgRel revertCfgRel
              gasAvailableRel gasValueRel totalGasRel)
            yulChild compiler.shared)
    (hTargetGasForX :
      let callee := EvmYul.AccountAddress.ofUInt256 address
      let callGas :=
        EvmYul.EVM.Ccallgas callee callee value gas evm.accountMap
          evm.toMachineState evm.substate
      ∀ {targetFuel targetOutcome},
        Assembly.Preservation.BlockTraceResult asm target targetFuel
          (Assembly.GasAware.installCodeAndGas target callGas
            (thetaCodeRawInitialState target callGas
              yul.executionEnv.blobVersionedHashes evm.createdAccounts
              evm.genesisBlockHeader evm.blocks evm.accountMap evm.σ₀
              { totalGasUsedInBlock := evm.totalGasUsedInBlock
                transactionReceipts := evm.transactionReceipts }
              (EvmYul.State.addAccessedAccount evm.toState callee).substate
              evm.executionEnv.codeOwner evm.executionEnv.sender callee
              (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice) value value
              (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
              (evm.executionEnv.depth + 1) evm.executionEnv.header
              evm.executionEnv.perm))
          targetOutcome →
        Assembly.GasAware.XResultPreconditionAssumptions target
          (Assembly.GasAware.installCodeAndGas target callGas
            (thetaCodeRawInitialState target callGas
              yul.executionEnv.blobVersionedHashes evm.createdAccounts
              evm.genesisBlockHeader evm.blocks evm.accountMap evm.σ₀
              { totalGasUsedInBlock := evm.totalGasUsedInBlock
                transactionReceipts := evm.transactionReceipts }
              (EvmYul.State.addAccessedAccount evm.toState callee).substate
              evm.executionEnv.codeOwner evm.executionEnv.sender callee
              (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice) value value
              (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
              (evm.executionEnv.depth + 1) evm.executionEnv.header
              evm.executionEnv.perm))
          targetOutcome)
    (hGasBound :
      let callee := EvmYul.AccountAddress.ofUInt256 address
      let callGas :=
        EvmYul.EVM.Ccallgas callee callee value gas evm.accountMap
          evm.toMachineState evm.substate
      ∀ {targetFuel targetOutcome}
        (hTrace :
          Assembly.Preservation.BlockTraceResult asm target targetFuel
            (Assembly.GasAware.installCodeAndGas target callGas
              (thetaCodeRawInitialState target callGas
                yul.executionEnv.blobVersionedHashes evm.createdAccounts
                evm.genesisBlockHeader evm.blocks evm.accountMap evm.σ₀
                { totalGasUsedInBlock := evm.totalGasUsedInBlock
                  transactionReceipts := evm.transactionReceipts }
                (EvmYul.State.addAccessedAccount evm.toState callee).substate
                evm.executionEnv.codeOwner evm.executionEnv.sender callee
                (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice) value value
                (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
                (evm.executionEnv.depth + 1) evm.executionEnv.header
                evm.executionEnv.perm))
            targetOutcome),
        (hTargetGasForX hTrace).gasBound ≤ callGas)
    (hUInt256 :
      EvmYul.EVM.Ccallgas (EvmYul.AccountAddress.ofUInt256 address)
          (EvmYul.AccountAddress.ofUInt256 address) value gas
          evm.accountMap evm.toMachineState evm.substate <
        EvmYul.UInt256.size)
    (hTargetChildGas :
      ∀ {halt}, SourceLowered.WholeProgramOutcomeRel sourceOutcome
          (.halted halt) →
        gasAvailableRel yulChild.toMachineState.gasAvailable
          halt.state.gasAvailable)
    (hReturnedGas :
      ∀ {targetOutcome returnedGas output},
        SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome →
          Assembly.GasAware.XResultAgrees targetOutcome
            (.revert returnedGas output) →
          let charged : EvmYul.EVM.State :=
            { evm with
              gasAvailable :=
                evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
          gasAvailableRel
            (yul.toMachineState.finishExternalCall output
              inOffset inSize outOffset outSize).gasAvailable
            ((charged.toMachineState.finishExternalCall output
                inOffset inSize outOffset outSize).gasAvailable +
              returnedGas)) :
    ∃ (evmFuel : Nat),
      CALLPrimitiveRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        referenceFuel.succ evmFuel.succ.succ.succ gasCost
        yul.executionEnv.blobVersionedHashes yul evm store
        gas address value inOffset inSize outOffset outSize := by
  rcases
      primCall_CALL_ordinary_revert_rel_of_installed_childDispatcher_afterAccess_withTargetGas
        hPrim hShared store childStore hStaticAllowed hEnough hDepth
        hNotPrecompile hFacts hCall hSourceRun hOutcomeRel hRevertShared
        hTargetGasForX hGasBound hUInt256 hTargetChildGas hReturnedGas with
    ⟨evmFuel, _compiler, _halt, _returnedGas, _output, yulAfter,
      _hWhole, _hKind, _hRevert, hEvmCall, hYulCall, hFinalRel⟩
  exact ⟨evmFuel, ⟨⟨0⟩, _, yulAfter, hEvmCall, hYulCall, hFinalRel⟩⟩

def ordinaryCALLCallee (address : EvmYul.UInt256) :
    EvmYul.AccountAddress :=
  EvmYul.AccountAddress.ofUInt256 address

def ordinaryCALLYulCallGas
    (yul : EvmYul.SharedState .Yul)
    (gas address value : EvmYul.UInt256) : Nat :=
  let callee := ordinaryCALLCallee address
  EvmYul.EVM.Ccallgas callee callee value gas yul.accountMap
    yul.toMachineState yul.substate

def ordinaryCALLEvmCallGas
    (evm : EvmYul.EVM.State)
    (gas address value : EvmYul.UInt256) : Nat :=
  let callee := ordinaryCALLCallee address
  EvmYul.EVM.Ccallgas callee callee value gas evm.accountMap
    evm.toMachineState evm.substate

theorem ordinaryCALLCallGas_eq_of_compiledAccountMapRel
    {cfg : Reference.StateRelConfig}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.EVM.State}
    (hShared : Reference.SharedStateRel cfg yul evm.toSharedState)
    (hWorld : CompiledAccountMapRel yul.accountMap evm.accountMap)
    (gas address value : EvmYul.UInt256) :
    ordinaryCALLYulCallGas yul gas address value =
      ordinaryCALLEvmCallGas evm gas address value := by
  rcases hShared with ⟨hChain, hMachine⟩
  simpa [ordinaryCALLYulCallGas, ordinaryCALLEvmCallGas,
    ordinaryCALLCallee] using
    hWorld.Ccallgas_eq
      (machineStateRel_gasAvailable_eq hMachine) hChain.substate

theorem ordinaryCALLCallGas_eq_stateRelConfig
    {varStackRel : Reference.VarStackRel}
    {terminalCfgRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop}
    {revertCfgRel : Reference.State → EVMState → Prop}
    {gasAvailableRel : Word → Word → Prop}
    {gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm}
    {totalGasRel : Nat → Nat → Prop}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.EVM.State}
    (hShared :
      Reference.SharedStateRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        yul evm.toSharedState)
    (gas address value : EvmYul.UInt256) :
    ordinaryCALLYulCallGas yul gas address value =
      ordinaryCALLEvmCallGas evm gas address value := by
  exact
    ordinaryCALLCallGas_eq_of_compiledAccountMapRel hShared
      (compiledAccountMapRel_of_sharedStateRel_stateRelConfig hShared)
      gas address value

def ordinaryCALLYulInitialShared
    (program : Program)
    (calleeCodeBytes : ByteArray)
    (yul : EvmYul.SharedState .Yul)
    (yulCallMap : EvmYul.AccountMap .Yul)
    (gas address value inOffset inSize : EvmYul.UInt256) :
    EvmYul.SharedState .Yul :=
  let callee := ordinaryCALLCallee address
  let calldata :=
    yul.toMachineState.memory.readWithPadding inOffset.toNat inSize.toNat
  let callGas := ordinaryCALLYulCallGas yul gas address value
  let yulAccessed : EvmYul.SharedState .Yul :=
    { yul with
      toState := EvmYul.State.addAccessedAccount yul.toState callee }
  { yulAccessed with
    executionEnv :=
      { yulAccessed.executionEnv with
        calldata := calldata
        code := program.contract
        codeBytes := calleeCodeBytes
        codeOwner := callee
        source := yul.executionEnv.codeOwner
        weiValue := value
        depth := yul.executionEnv.depth + 1 }
    toMachineState :=
      EvmYul.MachineState.freshExternalCall
        (EvmYul.UInt256.ofNat callGas)
    accountMap := yulCallMap }

def ordinaryCALLReferenceInitialState
    (program : Program)
    (calleeCodeBytes : ByteArray)
    (yul : EvmYul.SharedState .Yul)
    (yulCallMap : EvmYul.AccountMap .Yul)
    (gas address value inOffset inSize : EvmYul.UInt256) :
    Reference.State :=
  .Ok (ordinaryCALLYulInitialShared program calleeCodeBytes yul yulCallMap
        gas address value inOffset inSize) default

def ordinaryCALLTargetInitialState
    (target : Assembly.TargetProgram)
    (yul : EvmYul.SharedState .Yul)
    (evm : EvmYul.EVM.State)
    (gas address value inOffset inSize : EvmYul.UInt256) : EVMState :=
  let callee := ordinaryCALLCallee address
  let callGas := ordinaryCALLEvmCallGas evm gas address value
  Assembly.GasAware.installCodeAndGas target callGas
    (thetaCodeRawInitialState target callGas
      yul.executionEnv.blobVersionedHashes evm.createdAccounts
      evm.genesisBlockHeader evm.blocks evm.accountMap evm.σ₀
      { totalGasUsedInBlock := evm.totalGasUsedInBlock
        transactionReceipts := evm.transactionReceipts }
      (EvmYul.State.addAccessedAccount evm.toState callee).substate
      evm.executionEnv.codeOwner evm.executionEnv.sender callee
      (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice) value value
      (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
      (evm.executionEnv.depth + 1) evm.executionEnv.header
      evm.executionEnv.perm)

theorem ordinaryCALLTargetInitialState_pc
    (target : Assembly.TargetProgram)
    (yul : EvmYul.SharedState .Yul)
    (evm : EvmYul.EVM.State)
    (gas address value inOffset inSize : EvmYul.UInt256) :
    (ordinaryCALLTargetInitialState target yul evm gas address value
      inOffset inSize).pc = Assembly.Program.pcAfter [] := by
  simp [ordinaryCALLTargetInitialState, Assembly.GasAware.installCodeAndGas,
    thetaCodeRawInitialState]

theorem ordinaryCALLTargetInitialState_stack
    (target : Assembly.TargetProgram)
    (yul : EvmYul.SharedState .Yul)
    (evm : EvmYul.EVM.State)
    (gas address value inOffset inSize : EvmYul.UInt256) :
    (ordinaryCALLTargetInitialState target yul evm gas address value
      inOffset inSize).stack = [] := by
  simp [ordinaryCALLTargetInitialState, Assembly.GasAware.installCodeAndGas,
    thetaCodeRawInitialState]

theorem OrdinaryCALLBranchFacts.initialSharedRel_stateRelConfig
    {varStackRel : Reference.VarStackRel}
    {terminalCfgRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop}
    {revertCfgRel : Reference.State → EVMState → Prop}
    {gasAvailableRel : Word → Word → Prop}
    {gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm}
    {totalGasRel : Nat → Nat → Prop}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.EVM.State}
    (hShared :
      Reference.SharedStateRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        yul evm.toSharedState)
    {gas address value inOffset inSize : EvmYul.UInt256}
    {yulRecipient : EvmYul.Account .Yul}
    {yulCallMap : EvmYul.AccountMap .Yul}
    {evmRecipient : EvmYul.Account .EVM}
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    (hFacts :
      OrdinaryCALLBranchFacts yul evm address value yulRecipient
        yulCallMap evmRecipient program asm target)
    (hCallGas :
      gasAvailableRel
        (EvmYul.UInt256.ofNat
          (ordinaryCALLYulCallGas yul gas address value))
        (EvmYul.UInt256.ofNat
          (ordinaryCALLEvmCallGas evm gas address value)))
    (hGasPriceFits :
      (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice).toNat =
        evm.executionEnv.gasPrice) :
    Reference.SharedStateRel
      (stateRelConfig varStackRel terminalCfgRel revertCfgRel
        gasAvailableRel gasValueRel totalGasRel)
      (ordinaryCALLYulInitialShared program yulRecipient.codeBytes yul
        yulCallMap gas address value inOffset inSize)
      (ordinaryCALLTargetInitialState target yul evm gas address value
        inOffset inSize).toSharedState := by
  let callee := ordinaryCALLCallee address
  let calldata :=
    yul.toMachineState.memory.readWithPadding inOffset.toNat inSize.toNat
  let yulAccessed : EvmYul.SharedState .Yul :=
    { yul with
      toState := EvmYul.State.addAccessedAccount yul.toState callee }
  let evmAccessed : EvmYul.SharedState .EVM :=
    { evm.toSharedState with
      toState := EvmYul.State.addAccessedAccount evm.toState callee }
  have hOwner :
      yul.executionEnv.codeOwner = evm.executionEnv.codeOwner := by
    rcases hShared with ⟨hChain, _hMachine⟩
    simpa using hChain.executionEnv.codeOwner
  have hSender :
      yul.executionEnv.sender = evm.executionEnv.sender := by
    rcases hShared with ⟨hChain, _hMachine⟩
    simpa using hChain.executionEnv.sender
  have hGasPrice :
      yul.executionEnv.gasPrice = evm.executionEnv.gasPrice := by
    rcases hShared with ⟨hChain, _hMachine⟩
    simpa using hChain.executionEnv.gasPrice
  have hHeader :
      yul.executionEnv.header = evm.executionEnv.header := by
    rcases hShared with ⟨hChain, _hMachine⟩
    simpa using hChain.executionEnv.header
  have hDepth :
      yul.executionEnv.depth = evm.executionEnv.depth := by
    rcases hShared with ⟨hChain, _hMachine⟩
    simpa using hChain.executionEnv.depth
  have hPerm :
      yul.executionEnv.perm = evm.executionEnv.perm := by
    rcases hShared with ⟨hChain, _hMachine⟩
    simpa using hChain.executionEnv.perm
  have hSharedAccessed :
      Reference.SharedStateRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        yulAccessed evmAccessed := by
    simpa [yulAccessed, evmAccessed, callee, ordinaryCALLCallee] using
      sharedStateRel_addAccessedAccount hShared callee
  have hCalldata :
      calldata =
        evm.toMachineState.memory.readWithPadding
          inOffset.toNat inSize.toNat := by
    rcases hShared with ⟨_hChain, hMachine⟩
    simpa [calldata] using
      congrArg
        (fun memory =>
          memory.readWithPadding inOffset.toNat inSize.toNat)
        hMachine.memory
  have hCode :
      (stateRelConfig varStackRel terminalCfgRel revertCfgRel
        gasAvailableRel gasValueRel totalGasRel).codeRel
        yulRecipient.code (Assembly.Bytecode.encodeTarget target) := by
    simpa [stateRelConfig, codeImageRel, hFacts.code] using
      hFacts.accountRel.code
  have hAccountMap :
      (stateRelConfig varStackRel terminalCfgRel revertCfgRel
        gasAvailableRel gasValueRel totalGasRel).accountMapRel
        yulCallMap
        (EvmYul.EVM.thetaCallTransfer evm.accountMap
          evm.executionEnv.codeOwner callee value) := by
    simpa [stateRelConfig, accountMapRel, callee, ordinaryCALLCallee,
      evmCallTransfer_eq_thetaCallTransfer] using
      hFacts.transferRel
  simpa [ordinaryCALLYulInitialShared, ordinaryCALLTargetInitialState,
    ordinaryCALLYulCallGas, ordinaryCALLEvmCallGas, ordinaryCALLCallee,
    callee, calldata, yulAccessed, evmAccessed, hFacts.contract, hOwner,
    hSender, hGasPrice, hGasPriceFits, hHeader, hDepth, hPerm, hCalldata,
    EvmYul.State.addAccessedAccount]
    using
      sharedStateRel_callFrameFromThetaCodeXInitialState
        (cfg :=
          stateRelConfig varStackRel terminalCfgRel revertCfgRel
            gasAvailableRel gasValueRel totalGasRel)
        (yul := yulAccessed)
        (evm := evmAccessed)
        hSharedAccessed
        (yulAccountMap := yulCallMap)
        (evmSubstate := evmAccessed.substate)
        (yulCreated := yulAccessed.createdAccounts)
        (yulGas :=
          EvmYul.UInt256.ofNat
            (ordinaryCALLYulCallGas yul gas address value))
        (yulCode := yulRecipient.code)
        (yulSubstate := yulAccessed.substate)
        evm.executionEnv.codeOwner evm.executionEnv.sender callee
        (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice) value value
        (evm.toMachineState.memory.readWithPadding
          inOffset.toNat inSize.toNat)
        (evm.executionEnv.depth + 1) evm.executionEnv.header
        evm.executionEnv.perm yul.executionEnv.blobVersionedHashes
        yulRecipient.codeBytes target
        (ordinaryCALLEvmCallGas evm gas address value)
        hAccountMap hSharedAccessed.chain.substate hCode
        (hFacts.accountRel.codeBytes.trans hFacts.code)
        hSharedAccessed.chain.createdAccounts hCallGas

def OrdinaryCALLTargetGasForX
    (asm : Assembly.Program)
    (target : Assembly.TargetProgram)
    (yul : EvmYul.SharedState .Yul)
    (evm : EvmYul.EVM.State)
    (gas address value inOffset inSize : EvmYul.UInt256) : Type :=
  ∀ {targetFuel targetOutcome},
    Assembly.Preservation.BlockTraceResult asm target targetFuel
      (ordinaryCALLTargetInitialState target yul evm gas address value
        inOffset inSize)
      targetOutcome →
    Assembly.GasAware.XResultPreconditionAssumptions target
      (ordinaryCALLTargetInitialState target yul evm gas address value
        inOffset inSize)
      targetOutcome

def OrdinaryCALLGasBound
    (asm : Assembly.Program)
    (target : Assembly.TargetProgram)
    (yul : EvmYul.SharedState .Yul)
    (evm : EvmYul.EVM.State)
    (gas address value inOffset inSize : EvmYul.UInt256)
    (hTargetGasForX :
      OrdinaryCALLTargetGasForX asm target yul evm gas address value
        inOffset inSize) : Prop :=
  let callGas := ordinaryCALLEvmCallGas evm gas address value
  ∀ {targetFuel targetOutcome}
    (hTrace :
      Assembly.Preservation.BlockTraceResult asm target targetFuel
        (ordinaryCALLTargetInitialState target yul evm gas address value
          inOffset inSize)
        targetOutcome),
    (hTargetGasForX hTrace).gasBound ≤ callGas

inductive OrdinaryCALLPrimitiveEvidence
    (prim : Objects.Source.PrimitiveSemantics)
    (varStackRel : Reference.VarStackRel)
    (terminalCfgRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop)
    (revertCfgRel : Reference.State → EVMState → Prop)
    (gasAvailableRel : Word → Word → Prop)
    (gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm)
    (totalGasRel : Nat → Nat → Prop)
    (gasCost : Nat)
    (yul : EvmYul.SharedState .Yul) (evm : EvmYul.EVM.State)
    (gas address value inOffset inSize outOffset outSize : EvmYul.UInt256)
    (yulRecipient : EvmYul.Account .Yul)
    (yulCallMap : EvmYul.AccountMap .Yul)
    (evmRecipient : EvmYul.Account .EVM)
    (program : Program) (asm : Assembly.Program)
    (target : Assembly.TargetProgram) : Prop where
  | running
      {terminalRel :
        Assembly.HaltKind → Word → Reference.State →
          Objects.Source.State → Prop}
      {revertRel : Reference.State → Objects.Source.State → Prop}
      {referenceFuel sourceFuel : Nat}
      {childStore : EvmYul.Yul.VarStore}
      {yulChild : EvmYul.SharedState .Yul}
      {rets : List EvmYul.UInt256}
      {sourceOutcome : Objects.Source.Outcome}
      (hCall :
        EvmYul.Yul.callDispatcher referenceFuel (some program.contract)
            (ordinaryCALLReferenceInitialState program yulRecipient.codeBytes
              yul yulCallMap
              gas address value inOffset inSize) =
          .ok (.Ok yulChild childStore, rets))
      (hSourceRun :
        SourceLowered.run prim sourceFuel program
            (ordinaryCALLTargetInitialState target yul evm gas address value
              inOffset inSize) =
          .ok sourceOutcome)
      (hOutcomeRel :
        Program.RecursiveBridgeSemanticContracts.dispatcherOutcomeRel
          (stateRelConfig varStackRel terminalCfgRel revertCfgRel
            gasAvailableRel gasValueRel totalGasRel)
          terminalRel revertRel program
          (ordinaryCALLReferenceInitialState program yulRecipient.codeBytes
            yul yulCallMap
            gas address value inOffset inSize)
          (.regular (.Ok yulChild childStore)) sourceOutcome)
      (hTargetGasForX :
        OrdinaryCALLTargetGasForX asm target yul evm gas address value
          inOffset inSize)
      (hGasBound :
        OrdinaryCALLGasBound asm target yul evm gas address value
          inOffset inSize hTargetGasForX)
      (hUInt256 :
        ordinaryCALLEvmCallGas evm gas address value < EvmYul.UInt256.size)
      (hTargetChildGas :
        ∀ {targetChild},
          SourceLowered.WholeProgramOutcomeRel sourceOutcome
            (.running targetChild) →
          gasAvailableRel yulChild.toMachineState.gasAvailable
            targetChild.gasAvailable)
      (hEvmChildGas :
        ∀ {targetOutcome evmChild output},
          SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome →
            Assembly.GasAware.XResultAgrees targetOutcome
              (.success evmChild output) →
            gasAvailableRel yulChild.toMachineState.gasAvailable
              evmChild.gasAvailable)
      (hReturnedGas :
        ∀ {targetOutcome evmChild output},
          SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome →
            Assembly.GasAware.XResultAgrees targetOutcome
              (.success evmChild output) →
            let charged : EvmYul.EVM.State :=
              { evm with
                gasAvailable :=
                  evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
            gasAvailableRel
              (yul.toMachineState.finishExternalCall ByteArray.empty
                inOffset inSize outOffset outSize).gasAvailable
              ((charged.toMachineState.finishExternalCall output
                  inOffset inSize outOffset outSize).gasAvailable +
                evmChild.gasAvailable)) :
      OrdinaryCALLPrimitiveEvidence prim varStackRel terminalCfgRel
        revertCfgRel gasAvailableRel gasValueRel totalGasRel gasCost yul evm
        gas address value inOffset inSize outOffset outSize yulRecipient
        yulCallMap evmRecipient program asm target
  | haltedSuccess
      {referenceFuel sourceFuel : Nat}
      {childStore : EvmYul.Yul.VarStore}
      {yulChild : EvmYul.SharedState .Yul}
      {haltValue : EvmYul.UInt256}
      {sourceOutcome : Objects.Source.Outcome}
      (hCall :
        EvmYul.Yul.callDispatcher referenceFuel (some program.contract)
            (ordinaryCALLReferenceInitialState program yulRecipient.codeBytes
              yul yulCallMap
              gas address value inOffset inSize) =
          .error (.YulHalt (.Ok yulChild childStore) haltValue))
      (hSourceRun :
        SourceLowered.run prim sourceFuel program
            (ordinaryCALLTargetInitialState target yul evm gas address value
              inOffset inSize) =
          .ok sourceOutcome)
      (hOutcomeRel :
        Program.RecursiveBridgeSemanticContracts.dispatcherOutcomeRel
          (stateRelConfig varStackRel terminalCfgRel revertCfgRel
            gasAvailableRel gasValueRel totalGasRel)
          (Program.RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel
            (stateRelConfig varStackRel terminalCfgRel revertCfgRel
              gasAvailableRel gasValueRel totalGasRel))
          (Program.RecursiveBridgeTerminalObservationContracts.canonicalRevertRel
            (stateRelConfig varStackRel terminalCfgRel revertCfgRel
              gasAvailableRel gasValueRel totalGasRel))
          program
          (ordinaryCALLReferenceInitialState program yulRecipient.codeBytes
            yul yulCallMap
            gas address value inOffset inSize)
          (.yulHalt (.Ok yulChild childStore) haltValue) sourceOutcome)
      (hTargetGasForX :
        OrdinaryCALLTargetGasForX asm target yul evm gas address value
          inOffset inSize)
      (hGasBound :
        OrdinaryCALLGasBound asm target yul evm gas address value
          inOffset inSize hTargetGasForX)
      (hUInt256 :
        ordinaryCALLEvmCallGas evm gas address value < EvmYul.UInt256.size)
      (hReturnedGas :
        ∀ {targetOutcome evmChild output},
          SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome →
            Assembly.GasAware.XResultAgrees targetOutcome
              (.success evmChild output) →
            let charged : EvmYul.EVM.State :=
              { evm with
                gasAvailable :=
                  evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
            gasAvailableRel
              (yul.toMachineState.finishExternalCall output
                inOffset inSize outOffset outSize).gasAvailable
              ((charged.toMachineState.finishExternalCall output
                  inOffset inSize outOffset outSize).gasAvailable +
                evmChild.gasAvailable)) :
      OrdinaryCALLPrimitiveEvidence prim varStackRel terminalCfgRel
        revertCfgRel gasAvailableRel gasValueRel totalGasRel gasCost yul evm
        gas address value inOffset inSize outOffset outSize yulRecipient
        yulCallMap evmRecipient program asm target
  | reverted
      {terminalRel :
        Assembly.HaltKind → Word → Reference.State →
          Objects.Source.State → Prop}
      {revertRel : Reference.State → Objects.Source.State → Prop}
      {referenceFuel sourceFuel : Nat}
      {childStore : EvmYul.Yul.VarStore}
      {yulChild : EvmYul.SharedState .Yul}
      {sourceOutcome : Objects.Source.Outcome}
      (hCall :
        EvmYul.Yul.callDispatcher referenceFuel (some program.contract)
            (ordinaryCALLReferenceInitialState program yulRecipient.codeBytes
              yul yulCallMap
              gas address value inOffset inSize) =
          .error (.Revert (.Ok yulChild childStore)))
      (hSourceRun :
        SourceLowered.run prim sourceFuel program
            (ordinaryCALLTargetInitialState target yul evm gas address value
              inOffset inSize) =
          .ok sourceOutcome)
      (hOutcomeRel :
        Program.RecursiveBridgeSemanticContracts.dispatcherOutcomeRel
          (stateRelConfig varStackRel terminalCfgRel revertCfgRel
            gasAvailableRel gasValueRel totalGasRel)
          terminalRel revertRel program
          (ordinaryCALLReferenceInitialState program yulRecipient.codeBytes
            yul yulCallMap
            gas address value inOffset inSize)
          (.revert (.Ok yulChild childStore)) sourceOutcome)
      (hRevertShared :
        ∀ {compiler},
          revertRel (.Ok yulChild childStore) compiler →
            Reference.SharedStateRel
              (stateRelConfig varStackRel terminalCfgRel revertCfgRel
                gasAvailableRel gasValueRel totalGasRel)
              yulChild compiler.shared)
      (hTargetGasForX :
        OrdinaryCALLTargetGasForX asm target yul evm gas address value
          inOffset inSize)
      (hGasBound :
        OrdinaryCALLGasBound asm target yul evm gas address value
          inOffset inSize hTargetGasForX)
      (hUInt256 :
        ordinaryCALLEvmCallGas evm gas address value < EvmYul.UInt256.size)
      (hTargetChildGas :
        ∀ {halt},
          SourceLowered.WholeProgramOutcomeRel sourceOutcome (.halted halt) →
            gasAvailableRel yulChild.toMachineState.gasAvailable
              halt.state.gasAvailable)
      (hReturnedGas :
        ∀ {targetOutcome returnedGas output},
          SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome →
            Assembly.GasAware.XResultAgrees targetOutcome
              (.revert returnedGas output) →
            let charged : EvmYul.EVM.State :=
              { evm with
                gasAvailable :=
                  evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
            gasAvailableRel
              (yul.toMachineState.finishExternalCall output
                inOffset inSize outOffset outSize).gasAvailable
              ((charged.toMachineState.finishExternalCall output
                  inOffset inSize outOffset outSize).gasAvailable +
                returnedGas)) :
      OrdinaryCALLPrimitiveEvidence prim varStackRel terminalCfgRel
        revertCfgRel gasAvailableRel gasValueRel totalGasRel gasCost yul evm
        gas address value inOffset inSize outOffset outSize yulRecipient
        yulCallMap evmRecipient program asm target

inductive OrdinaryCALLSourceStaticEvidence
    (prim : Objects.Source.PrimitiveSemantics)
    (varStackRel : Reference.VarStackRel)
    (terminalCfgRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop)
    (revertCfgRel : Reference.State → EVMState → Prop)
    (gasAvailableRel : Word → Word → Prop)
    (gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm)
    (totalGasRel : Nat → Nat → Prop)
    (gasCost : Nat)
    (yul : EvmYul.SharedState .Yul) (evm : EvmYul.EVM.State)
    (gas address value inOffset inSize outOffset outSize : EvmYul.UInt256)
    (yulRecipient : EvmYul.Account .Yul)
    (yulCallMap : EvmYul.AccountMap .Yul)
    (evmRecipient : EvmYul.Account .EVM)
    (program : Program) (asm : Assembly.Program)
    (target : Assembly.TargetProgram) : Prop where
  | running
      {terminalRel :
        Assembly.HaltKind → Word → Reference.State →
          Objects.Source.State → Prop}
      {revertRel : Reference.State → Objects.Source.State → Prop}
      {referenceFuel sourceFuel : Nat}
      {childStore : EvmYul.Yul.VarStore}
      {yulChild : EvmYul.SharedState .Yul}
      {sourceOutcome : Objects.Source.Outcome}
      (hReferenceRun :
        Reference.runResult referenceFuel program
            (ordinaryCALLReferenceInitialState program yulRecipient.codeBytes
              yul yulCallMap gas address value inOffset inSize) =
          .ok (.regular (.Ok yulChild childStore)))
      (hSourceRun :
        SourceLowered.run prim sourceFuel program
            (ordinaryCALLTargetInitialState target yul evm gas address value
              inOffset inSize) =
          .ok sourceOutcome)
      (hOutcomeRel :
        Program.RecursiveBridgeSemanticContracts.dispatcherOutcomeRel
          (stateRelConfig varStackRel terminalCfgRel revertCfgRel
            gasAvailableRel gasValueRel totalGasRel)
          terminalRel revertRel program
          (ordinaryCALLReferenceInitialState program yulRecipient.codeBytes
            yul yulCallMap
            gas address value inOffset inSize)
          (.regular (.Ok yulChild childStore)) sourceOutcome)
      (hTargetGasForX :
        OrdinaryCALLTargetGasForX asm target yul evm gas address value
          inOffset inSize)
      (hGasBound :
        OrdinaryCALLGasBound asm target yul evm gas address value
          inOffset inSize hTargetGasForX)
      (hUInt256 :
        ordinaryCALLEvmCallGas evm gas address value < EvmYul.UInt256.size)
      (hTargetChildGas :
        ∀ {targetChild},
          SourceLowered.WholeProgramOutcomeRel sourceOutcome
            (.running targetChild) →
          gasAvailableRel yulChild.toMachineState.gasAvailable
            targetChild.gasAvailable)
      (hEvmChildGas :
        ∀ {targetOutcome evmChild output},
          SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome →
            Assembly.GasAware.XResultAgrees targetOutcome
              (.success evmChild output) →
            gasAvailableRel yulChild.toMachineState.gasAvailable
              evmChild.gasAvailable)
      (hReturnedGas :
        ∀ {targetOutcome evmChild output},
          SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome →
            Assembly.GasAware.XResultAgrees targetOutcome
              (.success evmChild output) →
            let charged : EvmYul.EVM.State :=
              { evm with
                gasAvailable :=
                  evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
            gasAvailableRel
              (yul.toMachineState.finishExternalCall ByteArray.empty
                inOffset inSize outOffset outSize).gasAvailable
              ((charged.toMachineState.finishExternalCall output
                  inOffset inSize outOffset outSize).gasAvailable +
                evmChild.gasAvailable)) :
      OrdinaryCALLSourceStaticEvidence prim varStackRel terminalCfgRel
        revertCfgRel gasAvailableRel gasValueRel totalGasRel gasCost yul evm
        gas address value inOffset inSize outOffset outSize yulRecipient
        yulCallMap evmRecipient program asm target
  | haltedSuccess
      {referenceFuel sourceFuel : Nat}
      {childStore : EvmYul.Yul.VarStore}
      {yulChild : EvmYul.SharedState .Yul}
      {haltValue : EvmYul.UInt256}
      {sourceOutcome : Objects.Source.Outcome}
      (hReferenceRun :
        Reference.runResult referenceFuel program
            (ordinaryCALLReferenceInitialState program yulRecipient.codeBytes
              yul yulCallMap gas address value inOffset inSize) =
          .ok (.yulHalt (.Ok yulChild childStore) haltValue))
      (hSourceRun :
        SourceLowered.run prim sourceFuel program
            (ordinaryCALLTargetInitialState target yul evm gas address value
              inOffset inSize) =
          .ok sourceOutcome)
      (hOutcomeRel :
        Program.RecursiveBridgeSemanticContracts.dispatcherOutcomeRel
          (stateRelConfig varStackRel terminalCfgRel revertCfgRel
            gasAvailableRel gasValueRel totalGasRel)
          (Program.RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel
            (stateRelConfig varStackRel terminalCfgRel revertCfgRel
              gasAvailableRel gasValueRel totalGasRel))
          (Program.RecursiveBridgeTerminalObservationContracts.canonicalRevertRel
            (stateRelConfig varStackRel terminalCfgRel revertCfgRel
              gasAvailableRel gasValueRel totalGasRel))
          program
          (ordinaryCALLReferenceInitialState program yulRecipient.codeBytes
            yul yulCallMap
            gas address value inOffset inSize)
          (.yulHalt (.Ok yulChild childStore) haltValue) sourceOutcome)
      (hTargetGasForX :
        OrdinaryCALLTargetGasForX asm target yul evm gas address value
          inOffset inSize)
      (hGasBound :
        OrdinaryCALLGasBound asm target yul evm gas address value
          inOffset inSize hTargetGasForX)
      (hUInt256 :
        ordinaryCALLEvmCallGas evm gas address value < EvmYul.UInt256.size)
      (hReturnedGas :
        ∀ {targetOutcome evmChild output},
          SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome →
            Assembly.GasAware.XResultAgrees targetOutcome
              (.success evmChild output) →
            let charged : EvmYul.EVM.State :=
              { evm with
                gasAvailable :=
                  evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
            gasAvailableRel
              (yul.toMachineState.finishExternalCall output
                inOffset inSize outOffset outSize).gasAvailable
              ((charged.toMachineState.finishExternalCall output
                  inOffset inSize outOffset outSize).gasAvailable +
                evmChild.gasAvailable)) :
      OrdinaryCALLSourceStaticEvidence prim varStackRel terminalCfgRel
        revertCfgRel gasAvailableRel gasValueRel totalGasRel gasCost yul evm
        gas address value inOffset inSize outOffset outSize yulRecipient
        yulCallMap evmRecipient program asm target
  | reverted
      {terminalRel :
        Assembly.HaltKind → Word → Reference.State →
          Objects.Source.State → Prop}
      {revertRel : Reference.State → Objects.Source.State → Prop}
      {referenceFuel sourceFuel : Nat}
      {childStore : EvmYul.Yul.VarStore}
      {yulChild : EvmYul.SharedState .Yul}
      {sourceOutcome : Objects.Source.Outcome}
      (hReferenceRun :
        Reference.runResult referenceFuel program
            (ordinaryCALLReferenceInitialState program yulRecipient.codeBytes
              yul yulCallMap gas address value inOffset inSize) =
          .ok (.revert (.Ok yulChild childStore)))
      (hSourceRun :
        SourceLowered.run prim sourceFuel program
            (ordinaryCALLTargetInitialState target yul evm gas address value
              inOffset inSize) =
          .ok sourceOutcome)
      (hOutcomeRel :
        Program.RecursiveBridgeSemanticContracts.dispatcherOutcomeRel
          (stateRelConfig varStackRel terminalCfgRel revertCfgRel
            gasAvailableRel gasValueRel totalGasRel)
          terminalRel revertRel program
          (ordinaryCALLReferenceInitialState program yulRecipient.codeBytes
            yul yulCallMap
            gas address value inOffset inSize)
          (.revert (.Ok yulChild childStore)) sourceOutcome)
      (hRevertShared :
        ∀ {compiler},
          revertRel (.Ok yulChild childStore) compiler →
            Reference.SharedStateRel
              (stateRelConfig varStackRel terminalCfgRel revertCfgRel
                gasAvailableRel gasValueRel totalGasRel)
              yulChild compiler.shared)
      (hTargetGasForX :
        OrdinaryCALLTargetGasForX asm target yul evm gas address value
          inOffset inSize)
      (hGasBound :
        OrdinaryCALLGasBound asm target yul evm gas address value
          inOffset inSize hTargetGasForX)
      (hUInt256 :
        ordinaryCALLEvmCallGas evm gas address value < EvmYul.UInt256.size)
      (hTargetChildGas :
        ∀ {halt},
          SourceLowered.WholeProgramOutcomeRel sourceOutcome (.halted halt) →
            gasAvailableRel yulChild.toMachineState.gasAvailable
              halt.state.gasAvailable)
      (hReturnedGas :
        ∀ {targetOutcome returnedGas output},
          SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome →
            Assembly.GasAware.XResultAgrees targetOutcome
              (.revert returnedGas output) →
            let charged : EvmYul.EVM.State :=
              { evm with
                gasAvailable :=
                  evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
            gasAvailableRel
              (yul.toMachineState.finishExternalCall output
                inOffset inSize outOffset outSize).gasAvailable
              ((charged.toMachineState.finishExternalCall output
                  inOffset inSize outOffset outSize).gasAvailable +
                returnedGas)) :
      OrdinaryCALLSourceStaticEvidence prim varStackRel terminalCfgRel
        revertCfgRel gasAvailableRel gasValueRel totalGasRel gasCost yul evm
        gas address value inOffset inSize outOffset outSize yulRecipient
        yulCallMap evmRecipient program asm target

def OrdinaryCALLChildTopAssumptions
    (prim : Objects.Source.PrimitiveSemantics)
    (varStackRel : Reference.VarStackRel)
    (terminalCfgRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop)
    (revertCfgRel : Reference.State → EVMState → Prop)
    (gasAvailableRel : Word → Word → Prop)
    (gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm)
    (totalGasRel : Nat → Nat → Prop)
    (terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop)
    (revertRel : Reference.State → Objects.Source.State → Prop)
    (yul : EvmYul.SharedState .Yul) (evm : EvmYul.EVM.State)
    (gas address value inOffset inSize : EvmYul.UInt256)
    (yulRecipient : EvmYul.Account .Yul)
    (yulCallMap : EvmYul.AccountMap .Yul)
    (program : Program) (asm : Assembly.Program)
    (target : Assembly.TargetProgram)
    (referenceFuel : Nat)
    (referenceResult : Reference.Result) : Prop :=
  Program.RecursiveBridgeTopAssumptions
    (stateRelConfig varStackRel terminalCfgRel revertCfgRel
      gasAvailableRel gasValueRel totalGasRel)
    terminalRel revertRel prim
    (Program.RecursiveBridgeSemanticContracts.dispatcherOutcomeRel
      (stateRelConfig varStackRel terminalCfgRel revertCfgRel
        gasAvailableRel gasValueRel totalGasRel)
      terminalRel revertRel program
      (ordinaryCALLReferenceInitialState program yulRecipient.codeBytes yul
        yulCallMap gas address value inOffset inSize))
    program asm target
    (ordinaryCALLYulInitialShared program yulRecipient.codeBytes yul
      yulCallMap gas address value inOffset inSize)
    default referenceFuel
    (ordinaryCALLTargetInitialState target yul evm gas address value
      inOffset inSize)
    referenceResult

theorem OrdinaryCALLChildTopAssumptions.of_branchFacts_stateRelConfig
    {prim : Objects.Source.PrimitiveSemantics}
    {varStackRel : Reference.VarStackRel}
    {terminalCfgRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop}
    {revertCfgRel : Reference.State → EVMState → Prop}
    {gasAvailableRel : Word → Word → Prop}
    {gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm}
    {totalGasRel : Nat → Nat → Prop}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.EVM.State}
    {gas address value inOffset inSize : EvmYul.UInt256}
    {yulRecipient : EvmYul.Account .Yul}
    {yulCallMap : EvmYul.AccountMap .Yul}
    {evmRecipient : EvmYul.Account .EVM}
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    {referenceFuel : Nat} {referenceResult : Reference.Result}
    (hShared :
      Reference.SharedStateRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        yul evm.toSharedState)
    (hFacts :
      OrdinaryCALLBranchFacts yul evm address value yulRecipient
        yulCallMap evmRecipient program asm target)
    (hCallGas :
      gasAvailableRel
        (EvmYul.UInt256.ofNat
          (ordinaryCALLYulCallGas yul gas address value))
        (EvmYul.UInt256.ofNat
          (ordinaryCALLEvmCallGas evm gas address value)))
    (hGasPriceFits :
      (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice).toNat =
        evm.executionEnv.gasPrice)
    (hChildFeatureCoverage :
      Program.RecursiveBridgeFeatureCoverage program)
    (hChildSemantics :
      Program.RecursiveBridgeSemanticContracts
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        terminalRel revertRel prim
        (Program.RecursiveBridgeSemanticContracts.dispatcherOutcomeRel
          (stateRelConfig varStackRel terminalCfgRel revertCfgRel
            gasAvailableRel gasValueRel totalGasRel)
          terminalRel revertRel program
          (ordinaryCALLReferenceInitialState program yulRecipient.codeBytes
            yul yulCallMap gas address value inOffset inSize))
        program
        (ordinaryCALLYulInitialShared program yulRecipient.codeBytes yul
          yulCallMap gas address value inOffset inSize)
        default)
    (hChildSourceRun :
      Program.RecursiveBridgeSourceRun program
        (ordinaryCALLYulInitialShared program yulRecipient.codeBytes yul
          yulCallMap gas address value inOffset inSize)
        default referenceFuel referenceResult)
    (hChildRuntime :
      Assembly.RuntimeAssumptions asm target
        (ordinaryCALLTargetInitialState target yul evm gas address value
          inOffset inSize)) :
    OrdinaryCALLChildTopAssumptions prim varStackRel terminalCfgRel
      revertCfgRel gasAvailableRel gasValueRel totalGasRel terminalRel
      revertRel yul evm gas address value inOffset inSize yulRecipient
      yulCallMap program asm target referenceFuel referenceResult := by
  refine
    { sourceAccepted :=
        Program.RecursiveBridgeSourceAccepted.ofFullCoverageAndCompileChecked
          hFacts.fullSourceAccepted hChildFeatureCoverage
          hFacts.compileChecked
      compileResources := hFacts.resources
      semantics := hChildSemantics
      initialShared := ?_
      sourceRun := hChildSourceRun
      compileTarget := ?_
      targetRuntime := ?_ }
  · have hInitial :=
      OrdinaryCALLBranchFacts.initialSharedRel_stateRelConfig
        (gas := gas) (address := address) (value := value)
        (inOffset := inOffset) (inSize := inSize)
        hShared hFacts hCallGas hGasPriceFits
    simpa [ordinaryCALLYulInitialShared] using hInitial
  · exact
      (Program.compileCheckedAssemblyTargetBytecode?_eq_some
        hFacts.bytecode).1
  · exact
      { runtime := hChildRuntime
        initialPc :=
          ordinaryCALLTargetInitialState_pc target yul evm gas address value
            inOffset inSize
        initialStack :=
          ordinaryCALLTargetInitialState_stack target yul evm gas address
            value inOffset inSize }

def OrdinaryCALLChildCALLTopAssumptions
    (prim : Objects.Source.PrimitiveSemantics)
    (varStackRel : Reference.VarStackRel)
    (terminalCfgRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop)
    (revertCfgRel : Reference.State → EVMState → Prop)
    (gasAvailableRel : Word → Word → Prop)
    (gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm)
    (totalGasRel : Nat → Nat → Prop)
    (terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop)
    (revertRel : Reference.State → Objects.Source.State → Prop)
    (yul : EvmYul.SharedState .Yul) (evm : EvmYul.EVM.State)
    (gas address value inOffset inSize : EvmYul.UInt256)
    (yulRecipient : EvmYul.Account .Yul)
    (yulCallMap : EvmYul.AccountMap .Yul)
    (program : Program) (asm : Assembly.Program)
    (target : Assembly.TargetProgram)
    (referenceFuel : Nat)
    (referenceResult : Reference.Result) : Prop :=
  Program.RecursiveBridgeCALLTopAssumptions
    (stateRelConfig varStackRel terminalCfgRel revertCfgRel
      gasAvailableRel gasValueRel totalGasRel)
    terminalRel revertRel prim
    (Program.RecursiveBridgeSemanticContracts.dispatcherOutcomeRel
      (stateRelConfig varStackRel terminalCfgRel revertCfgRel
        gasAvailableRel gasValueRel totalGasRel)
      terminalRel revertRel program
      (ordinaryCALLReferenceInitialState program yulRecipient.codeBytes yul
        yulCallMap gas address value inOffset inSize))
    program asm target
    (ordinaryCALLYulInitialShared program yulRecipient.codeBytes yul
      yulCallMap gas address value inOffset inSize)
    default referenceFuel
    (ordinaryCALLTargetInitialState target yul evm gas address value
      inOffset inSize)
    referenceResult

theorem OrdinaryCALLChildCALLTopAssumptions.of_branchFacts_stateRelConfig
    {prim : Objects.Source.PrimitiveSemantics}
    {varStackRel : Reference.VarStackRel}
    {terminalCfgRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop}
    {revertCfgRel : Reference.State → EVMState → Prop}
    {gasAvailableRel : Word → Word → Prop}
    {gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm}
    {totalGasRel : Nat → Nat → Prop}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.EVM.State}
    {gas address value inOffset inSize : EvmYul.UInt256}
    {yulRecipient : EvmYul.Account .Yul}
    {yulCallMap : EvmYul.AccountMap .Yul}
    {evmRecipient : EvmYul.Account .EVM}
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    {referenceFuel : Nat} {referenceResult : Reference.Result}
    (hShared :
      Reference.SharedStateRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        yul evm.toSharedState)
    (hFacts :
      OrdinaryCALLBranchFacts yul evm address value yulRecipient
        yulCallMap evmRecipient program asm target)
    (hCallGas :
      gasAvailableRel
        (EvmYul.UInt256.ofNat
          (ordinaryCALLYulCallGas yul gas address value))
        (EvmYul.UInt256.ofNat
          (ordinaryCALLEvmCallGas evm gas address value)))
    (hGasPriceFits :
      (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice).toNat =
        evm.executionEnv.gasPrice)
    (hChildFeatureCoverage :
      Program.RecursiveBridgeCALLFeatureCoverage program)
    (hChildSemantics :
      Program.RecursiveBridgeCALLSemanticContracts
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        terminalRel revertRel prim
        (Program.RecursiveBridgeSemanticContracts.dispatcherOutcomeRel
          (stateRelConfig varStackRel terminalCfgRel revertCfgRel
            gasAvailableRel gasValueRel totalGasRel)
          terminalRel revertRel program
          (ordinaryCALLReferenceInitialState program yulRecipient.codeBytes
            yul yulCallMap gas address value inOffset inSize))
        program
        (ordinaryCALLYulInitialShared program yulRecipient.codeBytes yul
          yulCallMap gas address value inOffset inSize)
        default)
    (hChildSourceRun :
      Program.RecursiveBridgeSourceRun program
        (ordinaryCALLYulInitialShared program yulRecipient.codeBytes yul
          yulCallMap gas address value inOffset inSize)
        default referenceFuel referenceResult)
    (hChildRuntime :
      Assembly.RuntimeAssumptions asm target
        (ordinaryCALLTargetInitialState target yul evm gas address value
          inOffset inSize)) :
    OrdinaryCALLChildCALLTopAssumptions prim varStackRel terminalCfgRel
      revertCfgRel gasAvailableRel gasValueRel totalGasRel terminalRel
      revertRel yul evm gas address value inOffset inSize yulRecipient
      yulCallMap program asm target referenceFuel referenceResult := by
  refine
    { fullSourceAccepted := hFacts.fullSourceAccepted
      callFeatureCoverage := hChildFeatureCoverage
      compileResources := hFacts.resources
      semantics := hChildSemantics
      initialShared := ?_
      sourceRun := hChildSourceRun
      compileTarget := ?_
      targetRuntime := ?_ }
  · have hInitial :=
      OrdinaryCALLBranchFacts.initialSharedRel_stateRelConfig
        (gas := gas) (address := address) (value := value)
        (inOffset := inOffset) (inSize := inSize)
        hShared hFacts hCallGas hGasPriceFits
    simpa [ordinaryCALLYulInitialShared] using hInitial
  · exact
      (Program.compileCheckedAssemblyTargetBytecode?_eq_some
        hFacts.bytecode).1
  · exact
      { runtime := hChildRuntime
        initialPc :=
          ordinaryCALLTargetInitialState_pc target yul evm gas address value
            inOffset inSize
        initialStack :=
          ordinaryCALLTargetInitialState_stack target yul evm gas address
            value inOffset inSize }

theorem OrdinaryCALLSourceStaticEvidence.running_of_childTopAssumptions
    {prim : Objects.Source.PrimitiveSemantics}
    {varStackRel : Reference.VarStackRel}
    {terminalCfgRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop}
    {revertCfgRel : Reference.State → EVMState → Prop}
    {gasAvailableRel : Word → Word → Prop}
    {gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm}
    {totalGasRel : Nat → Nat → Prop}
    {gasCost : Nat}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.EVM.State}
    {gas address value inOffset inSize outOffset outSize : EvmYul.UInt256}
    {yulRecipient : EvmYul.Account .Yul}
    {yulCallMap : EvmYul.AccountMap .Yul}
    {evmRecipient : EvmYul.Account .EVM}
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {referenceFuel : Nat}
    {childStore : EvmYul.Yul.VarStore}
    {yulChild : EvmYul.SharedState .Yul}
    (hTop :
      OrdinaryCALLChildTopAssumptions prim varStackRel terminalCfgRel
        revertCfgRel gasAvailableRel gasValueRel totalGasRel terminalRel
        revertRel yul evm gas address value inOffset inSize yulRecipient
        yulCallMap program asm target referenceFuel
        (.regular (.Ok yulChild childStore)))
    (hTargetGasForX :
      OrdinaryCALLTargetGasForX asm target yul evm gas address value
        inOffset inSize)
    (hGasBound :
      OrdinaryCALLGasBound asm target yul evm gas address value
        inOffset inSize hTargetGasForX)
    (hUInt256 :
      ordinaryCALLEvmCallGas evm gas address value < EvmYul.UInt256.size)
    (hTargetChildGas :
      ∀ {targetChild sourceOutcome},
        SourceLowered.WholeProgramOutcomeRel sourceOutcome
          (.running targetChild) →
        gasAvailableRel yulChild.toMachineState.gasAvailable
          targetChild.gasAvailable)
    (hEvmChildGas :
      ∀ {sourceOutcome targetOutcome evmChild output},
        SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome →
          Assembly.GasAware.XResultAgrees targetOutcome
            (.success evmChild output) →
          gasAvailableRel yulChild.toMachineState.gasAvailable
            evmChild.gasAvailable)
    (hReturnedGas :
      ∀ {sourceOutcome targetOutcome evmChild output},
        SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome →
          Assembly.GasAware.XResultAgrees targetOutcome
            (.success evmChild output) →
          let charged : EvmYul.EVM.State :=
            { evm with
              gasAvailable :=
                evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
          gasAvailableRel
            (yul.toMachineState.finishExternalCall ByteArray.empty
              inOffset inSize outOffset outSize).gasAvailable
            ((charged.toMachineState.finishExternalCall output
                inOffset inSize outOffset outSize).gasAvailable +
              evmChild.gasAvailable)) :
    OrdinaryCALLSourceStaticEvidence prim varStackRel terminalCfgRel
      revertCfgRel gasAvailableRel gasValueRel totalGasRel gasCost yul evm
      gas address value inOffset inSize outOffset outSize yulRecipient
      yulCallMap evmRecipient program asm target := by
  rcases
      Program.compile_whole_program_result_sound_with_source_run_of_programAcceptedRecursiveBridgeAllBoundsReserved_top
        (hTop := hTop) with
    ⟨sourceOutcome, sourceFuel, _targetFuel, _targetOutcome,
      hReferenceRun, hSourceRun, hOutcomeRel, _hWhole, _hAccepted,
      _hCompileBytes, _hEncoding, _hGasOpcode, _hGasOracle,
      _hOutOfGas, _hProjection, _hTrace⟩
  exact
    OrdinaryCALLSourceStaticEvidence.running
      (by simpa [ordinaryCALLReferenceInitialState] using hReferenceRun)
      hSourceRun hOutcomeRel hTargetGasForX hGasBound hUInt256
      (by
        intro targetChild hWhole
        exact hTargetChildGas hWhole)
      (by
        intro targetOutcome evmChild output hWhole hAgree
        exact hEvmChildGas hWhole hAgree)
      (by
        intro targetOutcome evmChild output hWhole hAgree
        exact hReturnedGas hWhole hAgree)

theorem OrdinaryCALLSourceStaticEvidence.haltedSuccess_of_childTopAssumptions
    {prim : Objects.Source.PrimitiveSemantics}
    {varStackRel : Reference.VarStackRel}
    {terminalCfgRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop}
    {revertCfgRel : Reference.State → EVMState → Prop}
    {gasAvailableRel : Word → Word → Prop}
    {gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm}
    {totalGasRel : Nat → Nat → Prop}
    {gasCost : Nat}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.EVM.State}
    {gas address value inOffset inSize outOffset outSize : EvmYul.UInt256}
    {yulRecipient : EvmYul.Account .Yul}
    {yulCallMap : EvmYul.AccountMap .Yul}
    {evmRecipient : EvmYul.Account .EVM}
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    {referenceFuel : Nat}
    {childStore : EvmYul.Yul.VarStore}
    {yulChild : EvmYul.SharedState .Yul}
    {haltValue : EvmYul.UInt256}
    (hTop :
      OrdinaryCALLChildTopAssumptions prim varStackRel terminalCfgRel
        revertCfgRel gasAvailableRel gasValueRel totalGasRel
        (Program.RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel
          (stateRelConfig varStackRel terminalCfgRel revertCfgRel
            gasAvailableRel gasValueRel totalGasRel))
        (Program.RecursiveBridgeTerminalObservationContracts.canonicalRevertRel
          (stateRelConfig varStackRel terminalCfgRel revertCfgRel
            gasAvailableRel gasValueRel totalGasRel))
        yul evm gas address value inOffset inSize yulRecipient
        yulCallMap program asm target referenceFuel
        (.yulHalt (.Ok yulChild childStore) haltValue))
    (hTargetGasForX :
      OrdinaryCALLTargetGasForX asm target yul evm gas address value
        inOffset inSize)
    (hGasBound :
      OrdinaryCALLGasBound asm target yul evm gas address value
        inOffset inSize hTargetGasForX)
    (hUInt256 :
      ordinaryCALLEvmCallGas evm gas address value < EvmYul.UInt256.size)
    (hReturnedGas :
      ∀ {sourceOutcome targetOutcome evmChild output},
        SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome →
          Assembly.GasAware.XResultAgrees targetOutcome
            (.success evmChild output) →
          let charged : EvmYul.EVM.State :=
            { evm with
              gasAvailable :=
                evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
          gasAvailableRel
            (yul.toMachineState.finishExternalCall output
              inOffset inSize outOffset outSize).gasAvailable
            ((charged.toMachineState.finishExternalCall output
                inOffset inSize outOffset outSize).gasAvailable +
              evmChild.gasAvailable)) :
    OrdinaryCALLSourceStaticEvidence prim varStackRel terminalCfgRel
      revertCfgRel gasAvailableRel gasValueRel totalGasRel gasCost yul evm
      gas address value inOffset inSize outOffset outSize yulRecipient
      yulCallMap evmRecipient program asm target := by
  rcases
      Program.compile_whole_program_result_sound_with_source_run_of_programAcceptedRecursiveBridgeAllBoundsReserved_top
        (hTop := hTop) with
    ⟨sourceOutcome, sourceFuel, _targetFuel, _targetOutcome,
      hReferenceRun, hSourceRun, hOutcomeRel, _hWhole, _hAccepted,
      _hCompileBytes, _hEncoding, _hGasOpcode, _hGasOracle,
      _hOutOfGas, _hProjection, _hTrace⟩
  exact
    OrdinaryCALLSourceStaticEvidence.haltedSuccess
      (by simpa [ordinaryCALLReferenceInitialState] using hReferenceRun)
      hSourceRun hOutcomeRel hTargetGasForX hGasBound hUInt256
      (by
        intro targetOutcome evmChild output hWhole hAgree
        exact hReturnedGas hWhole hAgree)

theorem OrdinaryCALLSourceStaticEvidence.reverted_of_childTopAssumptions
    {prim : Objects.Source.PrimitiveSemantics}
    {varStackRel : Reference.VarStackRel}
    {terminalCfgRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop}
    {revertCfgRel : Reference.State → EVMState → Prop}
    {gasAvailableRel : Word → Word → Prop}
    {gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm}
    {totalGasRel : Nat → Nat → Prop}
    {gasCost : Nat}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.EVM.State}
    {gas address value inOffset inSize outOffset outSize : EvmYul.UInt256}
    {yulRecipient : EvmYul.Account .Yul}
    {yulCallMap : EvmYul.AccountMap .Yul}
    {evmRecipient : EvmYul.Account .EVM}
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {referenceFuel : Nat}
    {childStore : EvmYul.Yul.VarStore}
    {yulChild : EvmYul.SharedState .Yul}
    (hTop :
      OrdinaryCALLChildTopAssumptions prim varStackRel terminalCfgRel
        revertCfgRel gasAvailableRel gasValueRel totalGasRel terminalRel
        revertRel yul evm gas address value inOffset inSize yulRecipient
        yulCallMap program asm target referenceFuel
        (.revert (.Ok yulChild childStore)))
    (hRevertShared :
      ∀ {compiler},
        revertRel (.Ok yulChild childStore) compiler →
          Reference.SharedStateRel
            (stateRelConfig varStackRel terminalCfgRel revertCfgRel
              gasAvailableRel gasValueRel totalGasRel)
            yulChild compiler.shared)
    (hTargetGasForX :
      OrdinaryCALLTargetGasForX asm target yul evm gas address value
        inOffset inSize)
    (hGasBound :
      OrdinaryCALLGasBound asm target yul evm gas address value
        inOffset inSize hTargetGasForX)
    (hUInt256 :
      ordinaryCALLEvmCallGas evm gas address value < EvmYul.UInt256.size)
    (hTargetChildGas :
      ∀ {halt sourceOutcome},
        SourceLowered.WholeProgramOutcomeRel sourceOutcome (.halted halt) →
          gasAvailableRel yulChild.toMachineState.gasAvailable
            halt.state.gasAvailable)
    (hReturnedGas :
      ∀ {sourceOutcome targetOutcome returnedGas output},
        SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome →
          Assembly.GasAware.XResultAgrees targetOutcome
            (.revert returnedGas output) →
          let charged : EvmYul.EVM.State :=
            { evm with
              gasAvailable :=
                evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
          gasAvailableRel
            (yul.toMachineState.finishExternalCall output
              inOffset inSize outOffset outSize).gasAvailable
            ((charged.toMachineState.finishExternalCall output
                inOffset inSize outOffset outSize).gasAvailable +
              returnedGas)) :
    OrdinaryCALLSourceStaticEvidence prim varStackRel terminalCfgRel
      revertCfgRel gasAvailableRel gasValueRel totalGasRel gasCost yul evm
      gas address value inOffset inSize outOffset outSize yulRecipient
      yulCallMap evmRecipient program asm target := by
  rcases
      Program.compile_whole_program_result_sound_with_source_run_of_programAcceptedRecursiveBridgeAllBoundsReserved_top
        (hTop := hTop) with
    ⟨sourceOutcome, sourceFuel, _targetFuel, _targetOutcome,
      hReferenceRun, hSourceRun, hOutcomeRel, _hWhole, _hAccepted,
      _hCompileBytes, _hEncoding, _hGasOpcode, _hGasOracle,
      _hOutOfGas, _hProjection, _hTrace⟩
  exact
    OrdinaryCALLSourceStaticEvidence.reverted
      (by simpa [ordinaryCALLReferenceInitialState] using hReferenceRun)
      hSourceRun hOutcomeRel hRevertShared hTargetGasForX hGasBound
      hUInt256
      (by
        intro halt hWhole
        exact hTargetChildGas hWhole)
      (by
        intro targetOutcome returnedGas output hWhole hAgree
        exact hReturnedGas hWhole hAgree)

inductive OrdinaryCALLChildTopEvidence
    (prim : Objects.Source.PrimitiveSemantics)
    (varStackRel : Reference.VarStackRel)
    (terminalCfgRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop)
    (revertCfgRel : Reference.State → EVMState → Prop)
    (gasAvailableRel : Word → Word → Prop)
    (gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm)
    (totalGasRel : Nat → Nat → Prop)
    (gasCost : Nat)
    (yul : EvmYul.SharedState .Yul) (evm : EvmYul.EVM.State)
    (gas address value inOffset inSize outOffset outSize : EvmYul.UInt256)
    (yulRecipient : EvmYul.Account .Yul)
    (yulCallMap : EvmYul.AccountMap .Yul)
    (evmRecipient : EvmYul.Account .EVM)
    (program : Program) (asm : Assembly.Program)
    (target : Assembly.TargetProgram) : Prop where
  | running
      {terminalRel :
        Assembly.HaltKind → Word → Reference.State →
          Objects.Source.State → Prop}
      {revertRel : Reference.State → Objects.Source.State → Prop}
      {referenceFuel : Nat}
      {childStore : EvmYul.Yul.VarStore}
      {yulChild : EvmYul.SharedState .Yul}
      (hTop :
        OrdinaryCALLChildTopAssumptions prim varStackRel terminalCfgRel
          revertCfgRel gasAvailableRel gasValueRel totalGasRel terminalRel
          revertRel yul evm gas address value inOffset inSize yulRecipient
          yulCallMap program asm target referenceFuel
          (.regular (.Ok yulChild childStore)))
      (hTargetGasForX :
        OrdinaryCALLTargetGasForX asm target yul evm gas address value
          inOffset inSize)
      (hGasBound :
        OrdinaryCALLGasBound asm target yul evm gas address value
          inOffset inSize hTargetGasForX)
      (hUInt256 :
        ordinaryCALLEvmCallGas evm gas address value < EvmYul.UInt256.size)
      (hTargetChildGas :
        ∀ {targetChild sourceOutcome},
          SourceLowered.WholeProgramOutcomeRel sourceOutcome
            (.running targetChild) →
          gasAvailableRel yulChild.toMachineState.gasAvailable
            targetChild.gasAvailable)
      (hEvmChildGas :
        ∀ {sourceOutcome targetOutcome evmChild output},
          SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome →
            Assembly.GasAware.XResultAgrees targetOutcome
              (.success evmChild output) →
            gasAvailableRel yulChild.toMachineState.gasAvailable
              evmChild.gasAvailable)
      (hReturnedGas :
        ∀ {sourceOutcome targetOutcome evmChild output},
          SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome →
            Assembly.GasAware.XResultAgrees targetOutcome
              (.success evmChild output) →
            let charged : EvmYul.EVM.State :=
              { evm with
                gasAvailable :=
                  evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
            gasAvailableRel
              (yul.toMachineState.finishExternalCall ByteArray.empty
                inOffset inSize outOffset outSize).gasAvailable
              ((charged.toMachineState.finishExternalCall output
                  inOffset inSize outOffset outSize).gasAvailable +
                evmChild.gasAvailable)) :
      OrdinaryCALLChildTopEvidence prim varStackRel terminalCfgRel
        revertCfgRel gasAvailableRel gasValueRel totalGasRel gasCost yul evm
        gas address value inOffset inSize outOffset outSize yulRecipient
        yulCallMap evmRecipient program asm target
  | haltedSuccess
      {referenceFuel : Nat}
      {childStore : EvmYul.Yul.VarStore}
      {yulChild : EvmYul.SharedState .Yul}
      {haltValue : EvmYul.UInt256}
      (hTop :
        OrdinaryCALLChildTopAssumptions prim varStackRel terminalCfgRel
          revertCfgRel gasAvailableRel gasValueRel totalGasRel
          (Program.RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel
            (stateRelConfig varStackRel terminalCfgRel revertCfgRel
              gasAvailableRel gasValueRel totalGasRel))
          (Program.RecursiveBridgeTerminalObservationContracts.canonicalRevertRel
            (stateRelConfig varStackRel terminalCfgRel revertCfgRel
              gasAvailableRel gasValueRel totalGasRel))
          yul evm gas address value inOffset inSize yulRecipient
          yulCallMap program asm target referenceFuel
          (.yulHalt (.Ok yulChild childStore) haltValue))
      (hTargetGasForX :
        OrdinaryCALLTargetGasForX asm target yul evm gas address value
          inOffset inSize)
      (hGasBound :
        OrdinaryCALLGasBound asm target yul evm gas address value
          inOffset inSize hTargetGasForX)
      (hUInt256 :
        ordinaryCALLEvmCallGas evm gas address value < EvmYul.UInt256.size)
      (hReturnedGas :
        ∀ {sourceOutcome targetOutcome evmChild output},
          SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome →
            Assembly.GasAware.XResultAgrees targetOutcome
              (.success evmChild output) →
            let charged : EvmYul.EVM.State :=
              { evm with
                gasAvailable :=
                  evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
            gasAvailableRel
              (yul.toMachineState.finishExternalCall output
                inOffset inSize outOffset outSize).gasAvailable
              ((charged.toMachineState.finishExternalCall output
                  inOffset inSize outOffset outSize).gasAvailable +
                evmChild.gasAvailable)) :
      OrdinaryCALLChildTopEvidence prim varStackRel terminalCfgRel
        revertCfgRel gasAvailableRel gasValueRel totalGasRel gasCost yul evm
        gas address value inOffset inSize outOffset outSize yulRecipient
        yulCallMap evmRecipient program asm target
  | reverted
      {terminalRel :
        Assembly.HaltKind → Word → Reference.State →
          Objects.Source.State → Prop}
      {revertRel : Reference.State → Objects.Source.State → Prop}
      {referenceFuel : Nat}
      {childStore : EvmYul.Yul.VarStore}
      {yulChild : EvmYul.SharedState .Yul}
      (hTop :
        OrdinaryCALLChildTopAssumptions prim varStackRel terminalCfgRel
          revertCfgRel gasAvailableRel gasValueRel totalGasRel terminalRel
          revertRel yul evm gas address value inOffset inSize yulRecipient
          yulCallMap program asm target referenceFuel
          (.revert (.Ok yulChild childStore)))
      (hRevertShared :
        ∀ {compiler},
          revertRel (.Ok yulChild childStore) compiler →
            Reference.SharedStateRel
              (stateRelConfig varStackRel terminalCfgRel revertCfgRel
                gasAvailableRel gasValueRel totalGasRel)
              yulChild compiler.shared)
      (hTargetGasForX :
        OrdinaryCALLTargetGasForX asm target yul evm gas address value
          inOffset inSize)
      (hGasBound :
        OrdinaryCALLGasBound asm target yul evm gas address value
          inOffset inSize hTargetGasForX)
      (hUInt256 :
        ordinaryCALLEvmCallGas evm gas address value < EvmYul.UInt256.size)
      (hTargetChildGas :
        ∀ {halt sourceOutcome},
          SourceLowered.WholeProgramOutcomeRel sourceOutcome (.halted halt) →
            gasAvailableRel yulChild.toMachineState.gasAvailable
              halt.state.gasAvailable)
      (hReturnedGas :
        ∀ {sourceOutcome targetOutcome returnedGas output},
          SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome →
            Assembly.GasAware.XResultAgrees targetOutcome
              (.revert returnedGas output) →
            let charged : EvmYul.EVM.State :=
              { evm with
                gasAvailable :=
                  evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
            gasAvailableRel
              (yul.toMachineState.finishExternalCall output
                inOffset inSize outOffset outSize).gasAvailable
              ((charged.toMachineState.finishExternalCall output
                  inOffset inSize outOffset outSize).gasAvailable +
                returnedGas)) :
      OrdinaryCALLChildTopEvidence prim varStackRel terminalCfgRel
        revertCfgRel gasAvailableRel gasValueRel totalGasRel gasCost yul evm
        gas address value inOffset inSize outOffset outSize yulRecipient
        yulCallMap evmRecipient program asm target

theorem OrdinaryCALLChildTopEvidence.running_of_branchFacts_stateRelConfig
    {prim : Objects.Source.PrimitiveSemantics}
    {varStackRel : Reference.VarStackRel}
    {terminalCfgRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop}
    {revertCfgRel : Reference.State → EVMState → Prop}
    {gasAvailableRel : Word → Word → Prop}
    {gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm}
    {totalGasRel : Nat → Nat → Prop}
    {gasCost : Nat}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.EVM.State}
    {gas address value inOffset inSize outOffset outSize : EvmYul.UInt256}
    {yulRecipient : EvmYul.Account .Yul}
    {yulCallMap : EvmYul.AccountMap .Yul}
    {evmRecipient : EvmYul.Account .EVM}
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {referenceFuel : Nat}
    {childStore : EvmYul.Yul.VarStore}
    {yulChild : EvmYul.SharedState .Yul}
    (hShared :
      Reference.SharedStateRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        yul evm.toSharedState)
    (hFacts :
      OrdinaryCALLBranchFacts yul evm address value yulRecipient
        yulCallMap evmRecipient program asm target)
    (hCallGas :
      gasAvailableRel
        (EvmYul.UInt256.ofNat
          (ordinaryCALLYulCallGas yul gas address value))
        (EvmYul.UInt256.ofNat
          (ordinaryCALLEvmCallGas evm gas address value)))
    (hGasPriceFits :
      (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice).toNat =
        evm.executionEnv.gasPrice)
    (hChildFeatureCoverage :
      Program.RecursiveBridgeFeatureCoverage program)
    (hChildSemantics :
      Program.RecursiveBridgeSemanticContracts
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        terminalRel revertRel prim
        (Program.RecursiveBridgeSemanticContracts.dispatcherOutcomeRel
          (stateRelConfig varStackRel terminalCfgRel revertCfgRel
            gasAvailableRel gasValueRel totalGasRel)
          terminalRel revertRel program
          (ordinaryCALLReferenceInitialState program yulRecipient.codeBytes
            yul yulCallMap gas address value inOffset inSize))
        program
        (ordinaryCALLYulInitialShared program yulRecipient.codeBytes yul
          yulCallMap gas address value inOffset inSize)
        default)
    (hChildSourceRun :
      Program.RecursiveBridgeSourceRun program
        (ordinaryCALLYulInitialShared program yulRecipient.codeBytes yul
          yulCallMap gas address value inOffset inSize)
        default referenceFuel (.regular (.Ok yulChild childStore)))
    (hChildRuntime :
      Assembly.RuntimeAssumptions asm target
        (ordinaryCALLTargetInitialState target yul evm gas address value
          inOffset inSize))
    (hTargetGasForX :
      OrdinaryCALLTargetGasForX asm target yul evm gas address value
        inOffset inSize)
    (hGasBound :
      OrdinaryCALLGasBound asm target yul evm gas address value
        inOffset inSize hTargetGasForX)
    (hUInt256 :
      ordinaryCALLEvmCallGas evm gas address value < EvmYul.UInt256.size)
    (hTargetChildGas :
      ∀ {targetChild sourceOutcome},
        SourceLowered.WholeProgramOutcomeRel sourceOutcome
          (.running targetChild) →
        gasAvailableRel yulChild.toMachineState.gasAvailable
          targetChild.gasAvailable)
    (hEvmChildGas :
      ∀ {sourceOutcome targetOutcome evmChild output},
        SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome →
          Assembly.GasAware.XResultAgrees targetOutcome
            (.success evmChild output) →
          gasAvailableRel yulChild.toMachineState.gasAvailable
            evmChild.gasAvailable)
    (hReturnedGas :
      ∀ {sourceOutcome targetOutcome evmChild output},
        SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome →
          Assembly.GasAware.XResultAgrees targetOutcome
            (.success evmChild output) →
          let charged : EvmYul.EVM.State :=
            { evm with
              gasAvailable :=
                evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
          gasAvailableRel
            (yul.toMachineState.finishExternalCall ByteArray.empty
              inOffset inSize outOffset outSize).gasAvailable
            ((charged.toMachineState.finishExternalCall output
                inOffset inSize outOffset outSize).gasAvailable +
              evmChild.gasAvailable)) :
    OrdinaryCALLChildTopEvidence prim varStackRel terminalCfgRel
      revertCfgRel gasAvailableRel gasValueRel totalGasRel gasCost yul evm
      gas address value inOffset inSize outOffset outSize yulRecipient
      yulCallMap evmRecipient program asm target :=
    OrdinaryCALLChildTopEvidence.running
    (OrdinaryCALLChildTopAssumptions.of_branchFacts_stateRelConfig
      hShared hFacts hCallGas hGasPriceFits hChildFeatureCoverage
      hChildSemantics hChildSourceRun hChildRuntime)
    hTargetGasForX hGasBound hUInt256 hTargetChildGas hEvmChildGas
    hReturnedGas

theorem OrdinaryCALLChildTopEvidence.haltedSuccess_of_branchFacts_stateRelConfig
    {prim : Objects.Source.PrimitiveSemantics}
    {varStackRel : Reference.VarStackRel}
    {terminalCfgRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop}
    {revertCfgRel : Reference.State → EVMState → Prop}
    {gasAvailableRel : Word → Word → Prop}
    {gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm}
    {totalGasRel : Nat → Nat → Prop}
    {gasCost : Nat}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.EVM.State}
    {gas address value inOffset inSize outOffset outSize : EvmYul.UInt256}
    {yulRecipient : EvmYul.Account .Yul}
    {yulCallMap : EvmYul.AccountMap .Yul}
    {evmRecipient : EvmYul.Account .EVM}
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    {referenceFuel : Nat}
    {childStore : EvmYul.Yul.VarStore}
    {yulChild : EvmYul.SharedState .Yul}
    {haltValue : EvmYul.UInt256}
    (hShared :
      Reference.SharedStateRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        yul evm.toSharedState)
    (hFacts :
      OrdinaryCALLBranchFacts yul evm address value yulRecipient
        yulCallMap evmRecipient program asm target)
    (hCallGas :
      gasAvailableRel
        (EvmYul.UInt256.ofNat
          (ordinaryCALLYulCallGas yul gas address value))
        (EvmYul.UInt256.ofNat
          (ordinaryCALLEvmCallGas evm gas address value)))
    (hGasPriceFits :
      (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice).toNat =
        evm.executionEnv.gasPrice)
    (hChildFeatureCoverage :
      Program.RecursiveBridgeFeatureCoverage program)
    (hChildSemantics :
      Program.RecursiveBridgeSemanticContracts
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        (Program.RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel
          (stateRelConfig varStackRel terminalCfgRel revertCfgRel
            gasAvailableRel gasValueRel totalGasRel))
        (Program.RecursiveBridgeTerminalObservationContracts.canonicalRevertRel
          (stateRelConfig varStackRel terminalCfgRel revertCfgRel
            gasAvailableRel gasValueRel totalGasRel))
        prim
        (Program.RecursiveBridgeSemanticContracts.dispatcherOutcomeRel
          (stateRelConfig varStackRel terminalCfgRel revertCfgRel
            gasAvailableRel gasValueRel totalGasRel)
          (Program.RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel
            (stateRelConfig varStackRel terminalCfgRel revertCfgRel
              gasAvailableRel gasValueRel totalGasRel))
          (Program.RecursiveBridgeTerminalObservationContracts.canonicalRevertRel
            (stateRelConfig varStackRel terminalCfgRel revertCfgRel
              gasAvailableRel gasValueRel totalGasRel))
          program
          (ordinaryCALLReferenceInitialState program yulRecipient.codeBytes
            yul yulCallMap gas address value inOffset inSize))
        program
        (ordinaryCALLYulInitialShared program yulRecipient.codeBytes yul
          yulCallMap gas address value inOffset inSize)
        default)
    (hChildSourceRun :
      Program.RecursiveBridgeSourceRun program
        (ordinaryCALLYulInitialShared program yulRecipient.codeBytes yul
          yulCallMap gas address value inOffset inSize)
        default referenceFuel (.yulHalt (.Ok yulChild childStore) haltValue))
    (hChildRuntime :
      Assembly.RuntimeAssumptions asm target
        (ordinaryCALLTargetInitialState target yul evm gas address value
          inOffset inSize))
    (hTargetGasForX :
      OrdinaryCALLTargetGasForX asm target yul evm gas address value
        inOffset inSize)
    (hGasBound :
      OrdinaryCALLGasBound asm target yul evm gas address value
        inOffset inSize hTargetGasForX)
    (hUInt256 :
      ordinaryCALLEvmCallGas evm gas address value < EvmYul.UInt256.size)
    (hReturnedGas :
      ∀ {sourceOutcome targetOutcome evmChild output},
        SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome →
          Assembly.GasAware.XResultAgrees targetOutcome
            (.success evmChild output) →
          let charged : EvmYul.EVM.State :=
            { evm with
              gasAvailable :=
                evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
          gasAvailableRel
            (yul.toMachineState.finishExternalCall output
              inOffset inSize outOffset outSize).gasAvailable
            ((charged.toMachineState.finishExternalCall output
                inOffset inSize outOffset outSize).gasAvailable +
              evmChild.gasAvailable)) :
    OrdinaryCALLChildTopEvidence prim varStackRel terminalCfgRel
      revertCfgRel gasAvailableRel gasValueRel totalGasRel gasCost yul evm
      gas address value inOffset inSize outOffset outSize yulRecipient
      yulCallMap evmRecipient program asm target :=
    OrdinaryCALLChildTopEvidence.haltedSuccess
    (OrdinaryCALLChildTopAssumptions.of_branchFacts_stateRelConfig
      hShared hFacts hCallGas hGasPriceFits hChildFeatureCoverage
      hChildSemantics hChildSourceRun hChildRuntime)
    hTargetGasForX hGasBound hUInt256 hReturnedGas

theorem OrdinaryCALLChildTopEvidence.reverted_of_branchFacts_stateRelConfig
    {prim : Objects.Source.PrimitiveSemantics}
    {varStackRel : Reference.VarStackRel}
    {terminalCfgRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop}
    {revertCfgRel : Reference.State → EVMState → Prop}
    {gasAvailableRel : Word → Word → Prop}
    {gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm}
    {totalGasRel : Nat → Nat → Prop}
    {gasCost : Nat}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.EVM.State}
    {gas address value inOffset inSize outOffset outSize : EvmYul.UInt256}
    {yulRecipient : EvmYul.Account .Yul}
    {yulCallMap : EvmYul.AccountMap .Yul}
    {evmRecipient : EvmYul.Account .EVM}
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {referenceFuel : Nat}
    {childStore : EvmYul.Yul.VarStore}
    {yulChild : EvmYul.SharedState .Yul}
    (hShared :
      Reference.SharedStateRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        yul evm.toSharedState)
    (hFacts :
      OrdinaryCALLBranchFacts yul evm address value yulRecipient
        yulCallMap evmRecipient program asm target)
    (hCallGas :
      gasAvailableRel
        (EvmYul.UInt256.ofNat
          (ordinaryCALLYulCallGas yul gas address value))
        (EvmYul.UInt256.ofNat
          (ordinaryCALLEvmCallGas evm gas address value)))
    (hGasPriceFits :
      (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice).toNat =
        evm.executionEnv.gasPrice)
    (hChildFeatureCoverage :
      Program.RecursiveBridgeFeatureCoverage program)
    (hChildSemantics :
      Program.RecursiveBridgeSemanticContracts
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        terminalRel revertRel prim
        (Program.RecursiveBridgeSemanticContracts.dispatcherOutcomeRel
          (stateRelConfig varStackRel terminalCfgRel revertCfgRel
            gasAvailableRel gasValueRel totalGasRel)
          terminalRel revertRel program
          (ordinaryCALLReferenceInitialState program yulRecipient.codeBytes
            yul yulCallMap gas address value inOffset inSize))
        program
        (ordinaryCALLYulInitialShared program yulRecipient.codeBytes yul
          yulCallMap gas address value inOffset inSize)
        default)
    (hChildSourceRun :
      Program.RecursiveBridgeSourceRun program
        (ordinaryCALLYulInitialShared program yulRecipient.codeBytes yul
          yulCallMap gas address value inOffset inSize)
        default referenceFuel (.revert (.Ok yulChild childStore)))
    (hChildRuntime :
      Assembly.RuntimeAssumptions asm target
        (ordinaryCALLTargetInitialState target yul evm gas address value
          inOffset inSize))
    (hRevertShared :
      ∀ {compiler},
        revertRel (.Ok yulChild childStore) compiler →
          Reference.SharedStateRel
            (stateRelConfig varStackRel terminalCfgRel revertCfgRel
              gasAvailableRel gasValueRel totalGasRel)
            yulChild compiler.shared)
    (hTargetGasForX :
      OrdinaryCALLTargetGasForX asm target yul evm gas address value
        inOffset inSize)
    (hGasBound :
      OrdinaryCALLGasBound asm target yul evm gas address value
        inOffset inSize hTargetGasForX)
    (hUInt256 :
      ordinaryCALLEvmCallGas evm gas address value < EvmYul.UInt256.size)
    (hTargetChildGas :
      ∀ {halt sourceOutcome},
        SourceLowered.WholeProgramOutcomeRel sourceOutcome (.halted halt) →
          gasAvailableRel yulChild.toMachineState.gasAvailable
            halt.state.gasAvailable)
    (hReturnedGas :
      ∀ {sourceOutcome targetOutcome returnedGas output},
        SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome →
          Assembly.GasAware.XResultAgrees targetOutcome
            (.revert returnedGas output) →
          let charged : EvmYul.EVM.State :=
            { evm with
              gasAvailable :=
                evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
          gasAvailableRel
            (yul.toMachineState.finishExternalCall output
              inOffset inSize outOffset outSize).gasAvailable
            ((charged.toMachineState.finishExternalCall output
                inOffset inSize outOffset outSize).gasAvailable +
              returnedGas)) :
    OrdinaryCALLChildTopEvidence prim varStackRel terminalCfgRel
      revertCfgRel gasAvailableRel gasValueRel totalGasRel gasCost yul evm
      gas address value inOffset inSize outOffset outSize yulRecipient
      yulCallMap evmRecipient program asm target :=
    OrdinaryCALLChildTopEvidence.reverted
    (OrdinaryCALLChildTopAssumptions.of_branchFacts_stateRelConfig
      hShared hFacts hCallGas hGasPriceFits hChildFeatureCoverage
      hChildSemantics hChildSourceRun hChildRuntime)
    hRevertShared hTargetGasForX hGasBound hUInt256 hTargetChildGas
    hReturnedGas

theorem OrdinaryCALLSourceStaticEvidence.of_childTopEvidence
    {prim : Objects.Source.PrimitiveSemantics}
    {varStackRel : Reference.VarStackRel}
    {terminalCfgRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop}
    {revertCfgRel : Reference.State → EVMState → Prop}
    {gasAvailableRel : Word → Word → Prop}
    {gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm}
    {totalGasRel : Nat → Nat → Prop}
    {gasCost : Nat}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.EVM.State}
    {gas address value inOffset inSize outOffset outSize : EvmYul.UInt256}
    {yulRecipient : EvmYul.Account .Yul}
    {yulCallMap : EvmYul.AccountMap .Yul}
    {evmRecipient : EvmYul.Account .EVM}
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    (hEvidence :
      OrdinaryCALLChildTopEvidence prim varStackRel terminalCfgRel
        revertCfgRel gasAvailableRel gasValueRel totalGasRel gasCost yul evm
        gas address value inOffset inSize outOffset outSize yulRecipient
        yulCallMap evmRecipient program asm target) :
    OrdinaryCALLSourceStaticEvidence prim varStackRel terminalCfgRel
      revertCfgRel gasAvailableRel gasValueRel totalGasRel gasCost yul evm
      gas address value inOffset inSize outOffset outSize yulRecipient
      yulCallMap evmRecipient program asm target := by
  cases hEvidence with
  | running hTop hTargetGasForX hGasBound hUInt256 hTargetChildGas
      hEvmChildGas hReturnedGas =>
      exact
        OrdinaryCALLSourceStaticEvidence.running_of_childTopAssumptions
          hTop hTargetGasForX hGasBound hUInt256 hTargetChildGas
          hEvmChildGas hReturnedGas
  | haltedSuccess hTop hTargetGasForX hGasBound hUInt256 hReturnedGas =>
      exact
        OrdinaryCALLSourceStaticEvidence.haltedSuccess_of_childTopAssumptions
          hTop hTargetGasForX hGasBound hUInt256 hReturnedGas
  | reverted hTop hRevertShared hTargetGasForX hGasBound hUInt256
      hTargetChildGas hReturnedGas =>
      exact
        OrdinaryCALLSourceStaticEvidence.reverted_of_childTopAssumptions
          hTop hRevertShared hTargetGasForX hGasBound hUInt256
          hTargetChildGas hReturnedGas

theorem OrdinaryCALLPrimitiveEvidence.of_sourceStaticEvidence
    {prim : Objects.Source.PrimitiveSemantics}
    {varStackRel : Reference.VarStackRel}
    {terminalCfgRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop}
    {revertCfgRel : Reference.State → EVMState → Prop}
    {gasAvailableRel : Word → Word → Prop}
    {gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm}
    {totalGasRel : Nat → Nat → Prop}
    {gasCost : Nat}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.EVM.State}
    {gas address value inOffset inSize outOffset outSize : EvmYul.UInt256}
    {yulRecipient : EvmYul.Account .Yul}
    {yulCallMap : EvmYul.AccountMap .Yul}
    {evmRecipient : EvmYul.Account .EVM}
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    (hEvidence :
      OrdinaryCALLSourceStaticEvidence prim varStackRel terminalCfgRel
        revertCfgRel gasAvailableRel gasValueRel totalGasRel gasCost yul evm
        gas address value inOffset inSize outOffset outSize yulRecipient
        yulCallMap evmRecipient program asm target) :
    OrdinaryCALLPrimitiveEvidence prim varStackRel terminalCfgRel
      revertCfgRel gasAvailableRel gasValueRel totalGasRel gasCost yul evm
      gas address value inOffset inSize outOffset outSize yulRecipient
      yulCallMap evmRecipient program asm target := by
  let initialShared :=
    ordinaryCALLYulInitialShared program yulRecipient.codeBytes yul yulCallMap
      gas address value inOffset inSize
  have hInstalled :
      initialShared.executionEnv.code = program.contract := by
    simp [initialShared, ordinaryCALLYulInitialShared]
  cases hEvidence with
  | running hReferenceRun hSourceRun hOutcomeRel hTargetGasForX hGasBound
      hUInt256 hTargetChildGas hEvmChildGas hReturnedGas =>
      rcases
          installed_callDispatcher_regular_of_runResult
            (program := program) (fuel := _)
            (shared := initialShared) (store := default)
            (hCode := hInstalled)
            (by
              simpa [initialShared, ordinaryCALLReferenceInitialState]
                using hReferenceRun) with
        ⟨rets, hCall⟩
      exact
        OrdinaryCALLPrimitiveEvidence.running
          (rets := rets)
          (by
            simpa [initialShared, ordinaryCALLReferenceInitialState]
              using hCall)
          hSourceRun hOutcomeRel hTargetGasForX hGasBound hUInt256
          hTargetChildGas hEvmChildGas hReturnedGas
  | haltedSuccess hReferenceRun hSourceRun hOutcomeRel hTargetGasForX
      hGasBound hUInt256 hReturnedGas =>
      have hCall :=
        installed_callDispatcher_yulHalt_of_runResult
          (program := program) (fuel := _)
          (shared := initialShared) (store := default)
          (hCode := hInstalled)
          (by
            simpa [initialShared, ordinaryCALLReferenceInitialState]
              using hReferenceRun)
      exact
        OrdinaryCALLPrimitiveEvidence.haltedSuccess
          (by
            simpa [initialShared, ordinaryCALLReferenceInitialState]
              using hCall)
          hSourceRun hOutcomeRel hTargetGasForX hGasBound hUInt256
          hReturnedGas
  | reverted hReferenceRun hSourceRun hOutcomeRel hRevertShared hTargetGasForX
      hGasBound hUInt256 hTargetChildGas hReturnedGas =>
      have hCall :=
        installed_callDispatcher_revert_of_runResult
          (program := program) (fuel := _)
          (shared := initialShared) (store := default)
          (hCode := hInstalled)
          (by
            simpa [initialShared, ordinaryCALLReferenceInitialState]
              using hReferenceRun)
      exact
        OrdinaryCALLPrimitiveEvidence.reverted
          (by
            simpa [initialShared, ordinaryCALLReferenceInitialState]
              using hCall)
          hSourceRun hOutcomeRel hRevertShared hTargetGasForX hGasBound
          hUInt256 hTargetChildGas hReturnedGas

theorem CALLPrimitiveRel.ordinaryEvidence_stateRelConfig
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {varStackRel : Reference.VarStackRel}
    {terminalCfgRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop}
    {revertCfgRel : Reference.State → EVMState → Prop}
    {gasAvailableRel : Word → Word → Prop}
    {gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm}
    {totalGasRel : Nat → Nat → Prop}
    {gasCost : Nat}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.EVM.State}
    (hShared :
      Reference.SharedStateRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        yul evm.toSharedState)
    (store : EvmYul.Yul.VarStore)
    {gas address value inOffset inSize outOffset outSize : EvmYul.UInt256}
    {yulRecipient : EvmYul.Account .Yul}
    {yulCallMap : EvmYul.AccountMap .Yul}
    {evmRecipient : EvmYul.Account .EVM}
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    (hStaticAllowed :
      ¬ (¬ yul.executionEnv.perm ∧ value ≠ ⟨0⟩))
    (hEnough :
      value ≤
        (evm.accountMap.find? evm.executionEnv.codeOwner |>.option ⟨0⟩
          (·.balance)))
    (hDepth : evm.executionEnv.depth < 1024)
    (hNotPrecompile :
      EvmYul.PrecompiledContract.ofAddress?
        (EvmYul.AccountAddress.ofUInt256 address) = none)
    (hFacts :
      OrdinaryCALLBranchFacts yul evm address value yulRecipient
        yulCallMap evmRecipient program asm target)
    (hEvidence :
      OrdinaryCALLPrimitiveEvidence prim varStackRel terminalCfgRel
        revertCfgRel gasAvailableRel gasValueRel totalGasRel gasCost yul evm
        gas address value inOffset inSize outOffset outSize yulRecipient
        yulCallMap evmRecipient program asm target) :
    ∃ sourceFuel evmFuel,
      CALLPrimitiveRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        sourceFuel evmFuel gasCost yul.executionEnv.blobVersionedHashes
        yul evm store gas address value inOffset inSize outOffset outSize := by
  cases hEvidence with
  | running hCall hSourceRun hOutcomeRel hTargetGasForX hGasBound hUInt256
      hTargetChildGas hEvmChildGas hReturnedGas =>
      rcases
          CALLPrimitiveRel.ordinaryRunningSuccess_stateRelConfig
            hPrim hShared store _ hStaticAllowed hEnough hDepth
            hNotPrecompile hFacts hCall hSourceRun hOutcomeRel
            hTargetGasForX hGasBound hUInt256 hTargetChildGas hEvmChildGas
            hReturnedGas with
        ⟨evmFuel, hRel⟩
      exact ⟨_, _, hRel⟩
  | haltedSuccess hCall hSourceRun hOutcomeRel hTargetGasForX hGasBound
      hUInt256 hReturnedGas =>
      rcases
          CALLPrimitiveRel.ordinaryHaltedSuccess_stateRelConfig
            hPrim hShared store _ hStaticAllowed hEnough hDepth
            hNotPrecompile hFacts hCall hSourceRun hOutcomeRel
            hTargetGasForX hGasBound hUInt256 hReturnedGas with
        ⟨evmFuel, hRel⟩
      exact ⟨_, _, hRel⟩
  | reverted hCall hSourceRun hOutcomeRel hRevertShared hTargetGasForX hGasBound
      hUInt256 hTargetChildGas hReturnedGas =>
      rcases
          CALLPrimitiveRel.ordinaryRevert_stateRelConfig
            hPrim hShared store _ hStaticAllowed hEnough hDepth
            hNotPrecompile hFacts hCall hSourceRun hOutcomeRel hRevertShared
            hTargetGasForX hGasBound hUInt256 hTargetChildGas hReturnedGas with
        ⟨evmFuel, hRel⟩
      exact ⟨_, _, hRel⟩

theorem CALLPrimitiveRel.ordinaryChildTopEvidence_stateRelConfig
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {varStackRel : Reference.VarStackRel}
    {terminalCfgRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop}
    {revertCfgRel : Reference.State → EVMState → Prop}
    {gasAvailableRel : Word → Word → Prop}
    {gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm}
    {totalGasRel : Nat → Nat → Prop}
    {gasCost : Nat}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.EVM.State}
    (hShared :
      Reference.SharedStateRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        yul evm.toSharedState)
    (store : EvmYul.Yul.VarStore)
    {gas address value inOffset inSize outOffset outSize : EvmYul.UInt256}
    {yulRecipient : EvmYul.Account .Yul}
    {yulCallMap : EvmYul.AccountMap .Yul}
    {evmRecipient : EvmYul.Account .EVM}
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    (hStaticAllowed :
      ¬ (¬ yul.executionEnv.perm ∧ value ≠ ⟨0⟩))
    (hEnough :
      value ≤
        (evm.accountMap.find? evm.executionEnv.codeOwner |>.option ⟨0⟩
          (·.balance)))
    (hDepth : evm.executionEnv.depth < 1024)
    (hNotPrecompile :
      EvmYul.PrecompiledContract.ofAddress?
        (EvmYul.AccountAddress.ofUInt256 address) = none)
    (hFacts :
      OrdinaryCALLBranchFacts yul evm address value yulRecipient
        yulCallMap evmRecipient program asm target)
    (hEvidence :
      OrdinaryCALLChildTopEvidence prim varStackRel terminalCfgRel
        revertCfgRel gasAvailableRel gasValueRel totalGasRel gasCost yul evm
        gas address value inOffset inSize outOffset outSize yulRecipient
        yulCallMap evmRecipient program asm target) :
    ∃ sourceFuel evmFuel,
      CALLPrimitiveRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        sourceFuel evmFuel gasCost yul.executionEnv.blobVersionedHashes
        yul evm store gas address value inOffset inSize outOffset outSize := by
  exact
    CALLPrimitiveRel.ordinaryEvidence_stateRelConfig
      hPrim hShared store hStaticAllowed hEnough hDepth hNotPrecompile hFacts
      (OrdinaryCALLPrimitiveEvidence.of_sourceStaticEvidence
        (OrdinaryCALLSourceStaticEvidence.of_childTopEvidence hEvidence))

theorem CALLPrimitiveRel.of_branchFacts_withOrdinaryBranchRel_stateRelConfig
    {varStackRel : Reference.VarStackRel}
    {terminalCfgRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop}
    {revertCfgRel : Reference.State → EVMState → Prop}
    {gasAvailableRel : Word → Word → Prop}
    {gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm}
    {totalGasRel : Nat → Nat → Prop}
    {fuel gasCost : Nat}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.EVM.State}
    (hShared :
      Reference.SharedStateRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        yul evm.toSharedState)
    (store : EvmYul.Yul.VarStore)
    {gas address value inOffset inSize outOffset outSize : EvmYul.UInt256}
    (hStaticAllowed :
      ¬ (¬ yul.executionEnv.perm ∧ value ≠ ⟨0⟩))
    (hBranch : CALLBranchFacts yul evm address value)
    (hGasEmpty :
      let target := EvmYul.AccountAddress.ofUInt256 address
      let callGas :=
        EvmYul.EVM.Ccallgas target target value gas evm.accountMap
          evm.toMachineState evm.substate
      let charged : EvmYul.EVM.State :=
        { evm with
          gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
      let targetGas :=
        (charged.toMachineState.finishExternalCall ByteArray.empty
          inOffset inSize outOffset outSize).gasAvailable +
          EvmYul.UInt256.ofNat callGas
      gasAvailableRel
        (yul.toMachineState.finishExternalCall ByteArray.empty
          inOffset inSize outOffset outSize).gasAvailable
        targetGas)
    (hPrecompiledSuccessGas :
      ∀ {precompiled : EvmYul.PrecompiledContract}
        (_hPrecompile :
          EvmYul.PrecompiledContract.ofAddress?
            (EvmYul.AccountAddress.ofUInt256 address) = some precompiled)
        (_hSuccess :
          let target := EvmYul.AccountAddress.ofUInt256 address
          let callMap :=
            evmCallTransfer evm.accountMap evm.executionEnv.codeOwner
              target value
          let callGas :=
            EvmYul.EVM.Ccallgas target target value gas evm.accountMap
              evm.toMachineState evm.substate
          let accessedSubstate :=
            (EvmYul.State.addAccessedAccount evm.toState target).substate
          let childEnv :=
            EvmYul.EVM.thetaCallExecutionEnv
              yul.executionEnv.blobVersionedHashes
              evm.executionEnv.codeOwner evm.executionEnv.sender target
              (.Precompiled precompiled)
              (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice)
              value
              (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
              (evm.executionEnv.depth + 1) evm.executionEnv.header
              evm.executionEnv.perm
          (runPrecompiledContract precompiled callMap
            (EvmYul.UInt256.ofNat callGas) accessedSubstate childEnv).1 =
            true),
        let target := EvmYul.AccountAddress.ofUInt256 address
        let callMap :=
          evmCallTransfer evm.accountMap evm.executionEnv.codeOwner
            target value
        let callGas :=
          EvmYul.EVM.Ccallgas target target value gas evm.accountMap
            evm.toMachineState evm.substate
        let charged : EvmYul.EVM.State :=
          { evm with
            gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
        let accessedSubstate :=
          (EvmYul.State.addAccessedAccount charged.toState target).substate
        let childEnv :=
          EvmYul.EVM.thetaCallExecutionEnv
            yul.executionEnv.blobVersionedHashes
            evm.executionEnv.codeOwner evm.executionEnv.sender target
            (.Precompiled precompiled)
            (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice)
            value
            (charged.memory.readWithPadding inOffset.toNat inSize.toNat)
            (evm.executionEnv.depth + 1) evm.executionEnv.header
            evm.executionEnv.perm
        let precompileResult :=
          runPrecompiledContract precompiled callMap
            (EvmYul.UInt256.ofNat callGas) accessedSubstate childEnv
        let targetGas :=
          (charged.toMachineState.finishExternalCall
            precompileResult.2.2.2.2 inOffset inSize outOffset outSize).gasAvailable +
            precompileResult.2.2.1
        gasAvailableRel
          (yul.toMachineState.finishExternalCall
            precompileResult.2.2.2.2 inOffset inSize outOffset outSize).gasAvailable
          targetGas)
    (hPrecompiledFailureGas :
      ∀ {precompiled : EvmYul.PrecompiledContract}
        (_hPrecompile :
          EvmYul.PrecompiledContract.ofAddress?
            (EvmYul.AccountAddress.ofUInt256 address) = some precompiled)
        (_hFailure :
          let target := EvmYul.AccountAddress.ofUInt256 address
          let callMap :=
            evmCallTransfer evm.accountMap evm.executionEnv.codeOwner
              target value
          let callGas :=
            EvmYul.EVM.Ccallgas target target value gas evm.accountMap
              evm.toMachineState evm.substate
          let accessedSubstate :=
            (EvmYul.State.addAccessedAccount evm.toState target).substate
          let childEnv :=
            EvmYul.EVM.thetaCallExecutionEnv
              yul.executionEnv.blobVersionedHashes
              evm.executionEnv.codeOwner evm.executionEnv.sender target
              (.Precompiled precompiled)
              (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice)
              value
              (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
              (evm.executionEnv.depth + 1) evm.executionEnv.header
              evm.executionEnv.perm
          (runPrecompiledContract precompiled callMap
            (EvmYul.UInt256.ofNat callGas) accessedSubstate childEnv).1 =
            false),
        let target := EvmYul.AccountAddress.ofUInt256 address
        let callMap :=
          evmCallTransfer evm.accountMap evm.executionEnv.codeOwner
            target value
        let callGas :=
          EvmYul.EVM.Ccallgas target target value gas evm.accountMap
            evm.toMachineState evm.substate
        let charged : EvmYul.EVM.State :=
          { evm with
            gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
        let accessedSubstate :=
          (EvmYul.State.addAccessedAccount charged.toState target).substate
        let childEnv :=
          EvmYul.EVM.thetaCallExecutionEnv
            yul.executionEnv.blobVersionedHashes
            evm.executionEnv.codeOwner evm.executionEnv.sender target
            (.Precompiled precompiled)
            (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice)
            value
            (charged.memory.readWithPadding inOffset.toNat inSize.toNat)
            (evm.executionEnv.depth + 1) evm.executionEnv.header
            evm.executionEnv.perm
        let precompileResult :=
          runPrecompiledContract precompiled callMap
            (EvmYul.UInt256.ofNat callGas) accessedSubstate childEnv
        let targetGas :=
          (charged.toMachineState.finishExternalCall
            precompileResult.2.2.2.2 inOffset inSize outOffset outSize).gasAvailable +
            precompileResult.2.2.1
        gasAvailableRel
          (yul.toMachineState.finishExternalCall ByteArray.empty
            inOffset inSize outOffset outSize).gasAvailable
          targetGas)
    (hOrdinaryBranch :
      ∀ {yulRecipient : EvmYul.Account .Yul}
        {yulCallMap : EvmYul.AccountMap .Yul}
        {evmRecipient : EvmYul.Account .EVM}
        {program : Program} {asm : Assembly.Program}
        {target : Assembly.TargetProgram}
        (_hEnough :
          value ≤
            (evm.accountMap.find? evm.executionEnv.codeOwner |>.option ⟨0⟩
              (·.balance)))
        (_hDepth : evm.executionEnv.depth < 1024)
        (_hNotPrecompile :
          EvmYul.PrecompiledContract.ofAddress?
            (EvmYul.AccountAddress.ofUInt256 address) = none)
        (_hFacts :
          OrdinaryCALLBranchFacts yul evm address value yulRecipient
            yulCallMap evmRecipient program asm target),
        ∃ sourceFuel evmFuel,
          CALLPrimitiveRel
            (stateRelConfig varStackRel terminalCfgRel revertCfgRel
              gasAvailableRel gasValueRel totalGasRel)
            sourceFuel evmFuel gasCost yul.executionEnv.blobVersionedHashes
            yul evm store gas address value inOffset inSize outOffset
            outSize) :
    ∃ sourceFuel evmFuel,
      CALLPrimitiveRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        sourceFuel evmFuel gasCost yul.executionEnv.blobVersionedHashes
        yul evm store gas address value inOffset inSize outOffset outSize := by
  cases hBranch with
  | insufficientFunds hNotEnough =>
      exact
        ⟨fuel.succ, fuel.succ,
          CALLPrimitiveRel.insufficientFunds_stateRelConfig
            (fuel := fuel) (gasCost := gasCost)
            (blobVersionedHashes := yul.executionEnv.blobVersionedHashes)
            hShared store hStaticAllowed hNotEnough hGasEmpty⟩
  | depthLimit hEnough hDepthLimit =>
      exact
        ⟨fuel.succ, fuel.succ,
          CALLPrimitiveRel.depthLimit_stateRelConfig
            (fuel := fuel) (gasCost := gasCost)
            (blobVersionedHashes := yul.executionEnv.blobVersionedHashes)
            hShared store hStaticAllowed hEnough hDepthLimit hGasEmpty⟩
  | noCode hEnough hDepth hNotPrecompile _hMissingYul hMissingEvm =>
      exact
        ⟨fuel.succ, fuel.succ.succ.succ.succ.succ,
          CALLPrimitiveRel.noCode_stateRelConfig
            (fuel := fuel) (gasCost := gasCost)
            (blobVersionedHashes := yul.executionEnv.blobVersionedHashes)
            hShared store hStaticAllowed hEnough hDepth hNotPrecompile
            hMissingEvm hGasEmpty⟩
  | precompiled precompiled hEnough hDepth hPrecompile =>
      by_cases hSuccess :
        (let target := EvmYul.AccountAddress.ofUInt256 address
         let callMap :=
          evmCallTransfer evm.accountMap evm.executionEnv.codeOwner
            target value
         let callGas :=
          EvmYul.EVM.Ccallgas target target value gas evm.accountMap
            evm.toMachineState evm.substate
         let accessedSubstate :=
          (EvmYul.State.addAccessedAccount evm.toState target).substate
         let childEnv :=
          EvmYul.EVM.thetaCallExecutionEnv
            yul.executionEnv.blobVersionedHashes
            evm.executionEnv.codeOwner evm.executionEnv.sender target
            (.Precompiled precompiled)
            (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice)
            value
            (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
            (evm.executionEnv.depth + 1) evm.executionEnv.header
            evm.executionEnv.perm
         (runPrecompiledContract precompiled callMap
          (EvmYul.UInt256.ofNat callGas) accessedSubstate childEnv).1 =
          true)
      · exact
          ⟨fuel.succ, fuel.succ.succ,
            CALLPrimitiveRel.precompiledSuccess_stateRelConfig
              (fuel := fuel) (gasCost := gasCost)
              (blobVersionedHashes := yul.executionEnv.blobVersionedHashes)
              hShared store hStaticAllowed hEnough hDepth hPrecompile
              hSuccess
              (hPrecompiledSuccessGas hPrecompile hSuccess)⟩
      · let target := EvmYul.AccountAddress.ofUInt256 address
        let callMap :=
          evmCallTransfer evm.accountMap evm.executionEnv.codeOwner
            target value
        let callGas :=
          EvmYul.EVM.Ccallgas target target value gas evm.accountMap
            evm.toMachineState evm.substate
        let accessedSubstate :=
          (EvmYul.State.addAccessedAccount evm.toState target).substate
        let childEnv :=
          EvmYul.EVM.thetaCallExecutionEnv
            yul.executionEnv.blobVersionedHashes
            evm.executionEnv.codeOwner evm.executionEnv.sender target
            (.Precompiled precompiled)
            (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice)
            value
            (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
            (evm.executionEnv.depth + 1) evm.executionEnv.header
            evm.executionEnv.perm
        have hNotSuccessRaw :
            ¬(runPrecompiledContract precompiled callMap
              (EvmYul.UInt256.ofNat callGas) accessedSubstate childEnv).1 =
              true := by
          intro hRaw
          exact hSuccess (by
            simpa [target, callMap, callGas, accessedSubstate, childEnv]
              using hRaw)
        have hFailureRaw :
            (runPrecompiledContract precompiled callMap
              (EvmYul.UInt256.ofNat callGas) accessedSubstate childEnv).1 =
              false := by
          cases hResult :
              (runPrecompiledContract precompiled callMap
                (EvmYul.UInt256.ofNat callGas) accessedSubstate childEnv).1 <;>
            simp [hResult] at hNotSuccessRaw ⊢
        have hFailure :
            (let target := EvmYul.AccountAddress.ofUInt256 address
             let callMap :=
              evmCallTransfer evm.accountMap evm.executionEnv.codeOwner
                target value
             let callGas :=
              EvmYul.EVM.Ccallgas target target value gas evm.accountMap
                evm.toMachineState evm.substate
             let accessedSubstate :=
              (EvmYul.State.addAccessedAccount evm.toState target).substate
             let childEnv :=
              EvmYul.EVM.thetaCallExecutionEnv
                yul.executionEnv.blobVersionedHashes
                evm.executionEnv.codeOwner evm.executionEnv.sender target
                (.Precompiled precompiled)
                (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice)
                value
                (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
                (evm.executionEnv.depth + 1) evm.executionEnv.header
                evm.executionEnv.perm
             (runPrecompiledContract precompiled callMap
              (EvmYul.UInt256.ofNat callGas) accessedSubstate childEnv).1 =
              false) := by
          simpa [target, callMap, callGas, accessedSubstate, childEnv]
            using hFailureRaw
        exact
          ⟨fuel.succ, fuel.succ.succ,
            CALLPrimitiveRel.precompiledFailure_stateRelConfig
              (fuel := fuel) (gasCost := gasCost)
              (blobVersionedHashes := yul.executionEnv.blobVersionedHashes)
              hShared store hStaticAllowed hEnough hDepth hPrecompile
              hFailure
              (hPrecompiledFailureGas hPrecompile hFailure)⟩
  | existingDefaultCode yulRecipient evmRecipient hEnough hDepth
      hNotPrecompile hFindYul hCodeDefault hFindEvm _hAccountRel
      hEvmCodeDefault =>
      exact
        ⟨fuel.succ.succ.succ.succ.succ.succ,
          fuel.succ.succ.succ.succ.succ.succ,
          CALLPrimitiveRel.existingDefaultCode_stateRelConfig
            (fuel := fuel) (gasCost := gasCost)
            (blobVersionedHashes := yul.executionEnv.blobVersionedHashes)
            hShared store hStaticAllowed hEnough hDepth hNotPrecompile
            hFindYul hCodeDefault hFindEvm hEvmCodeDefault hGasEmpty⟩
  | ordinary yulRecipient yulCallMap evmRecipient program asm target
      hEnough hDepth hNotPrecompile hFacts =>
      exact
        hOrdinaryBranch hEnough hDepth hNotPrecompile hFacts

theorem CALLPrimitiveRel.of_branchFacts_withOrdinaryChildTopEvidence_stateRelConfig
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {varStackRel : Reference.VarStackRel}
    {terminalCfgRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop}
    {revertCfgRel : Reference.State → EVMState → Prop}
    {gasAvailableRel : Word → Word → Prop}
    {gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm}
    {totalGasRel : Nat → Nat → Prop}
    {fuel gasCost : Nat}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.EVM.State}
    (hShared :
      Reference.SharedStateRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        yul evm.toSharedState)
    (store : EvmYul.Yul.VarStore)
    {gas address value inOffset inSize outOffset outSize : EvmYul.UInt256}
    (hStaticAllowed :
      ¬ (¬ yul.executionEnv.perm ∧ value ≠ ⟨0⟩))
    (hBranch : CALLBranchFacts yul evm address value)
    (hGasEmpty :
      let target := EvmYul.AccountAddress.ofUInt256 address
      let callGas :=
        EvmYul.EVM.Ccallgas target target value gas evm.accountMap
          evm.toMachineState evm.substate
      let charged : EvmYul.EVM.State :=
        { evm with
          gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
      let targetGas :=
        (charged.toMachineState.finishExternalCall ByteArray.empty
          inOffset inSize outOffset outSize).gasAvailable +
          EvmYul.UInt256.ofNat callGas
      gasAvailableRel
        (yul.toMachineState.finishExternalCall ByteArray.empty
          inOffset inSize outOffset outSize).gasAvailable
        targetGas)
    (hPrecompiledSuccessGas :
      ∀ {precompiled : EvmYul.PrecompiledContract}
        (_hPrecompile :
          EvmYul.PrecompiledContract.ofAddress?
            (EvmYul.AccountAddress.ofUInt256 address) = some precompiled)
        (_hSuccess :
          let target := EvmYul.AccountAddress.ofUInt256 address
          let callMap :=
            evmCallTransfer evm.accountMap evm.executionEnv.codeOwner
              target value
          let callGas :=
            EvmYul.EVM.Ccallgas target target value gas evm.accountMap
              evm.toMachineState evm.substate
          let accessedSubstate :=
            (EvmYul.State.addAccessedAccount evm.toState target).substate
          let childEnv :=
            EvmYul.EVM.thetaCallExecutionEnv
              yul.executionEnv.blobVersionedHashes
              evm.executionEnv.codeOwner evm.executionEnv.sender target
              (.Precompiled precompiled)
              (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice)
              value
              (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
              (evm.executionEnv.depth + 1) evm.executionEnv.header
              evm.executionEnv.perm
          (runPrecompiledContract precompiled callMap
            (EvmYul.UInt256.ofNat callGas) accessedSubstate childEnv).1 =
            true),
        let target := EvmYul.AccountAddress.ofUInt256 address
        let callMap :=
          evmCallTransfer evm.accountMap evm.executionEnv.codeOwner
            target value
        let callGas :=
          EvmYul.EVM.Ccallgas target target value gas evm.accountMap
            evm.toMachineState evm.substate
        let charged : EvmYul.EVM.State :=
          { evm with
            gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
        let accessedSubstate :=
          (EvmYul.State.addAccessedAccount charged.toState target).substate
        let childEnv :=
          EvmYul.EVM.thetaCallExecutionEnv
            yul.executionEnv.blobVersionedHashes
            evm.executionEnv.codeOwner evm.executionEnv.sender target
            (.Precompiled precompiled)
            (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice)
            value
            (charged.memory.readWithPadding inOffset.toNat inSize.toNat)
            (evm.executionEnv.depth + 1) evm.executionEnv.header
            evm.executionEnv.perm
        let precompileResult :=
          runPrecompiledContract precompiled callMap
            (EvmYul.UInt256.ofNat callGas) accessedSubstate childEnv
        let targetGas :=
          (charged.toMachineState.finishExternalCall
            precompileResult.2.2.2.2 inOffset inSize outOffset outSize).gasAvailable +
            precompileResult.2.2.1
        gasAvailableRel
          (yul.toMachineState.finishExternalCall
            precompileResult.2.2.2.2 inOffset inSize outOffset outSize).gasAvailable
          targetGas)
    (hPrecompiledFailureGas :
      ∀ {precompiled : EvmYul.PrecompiledContract}
        (_hPrecompile :
          EvmYul.PrecompiledContract.ofAddress?
            (EvmYul.AccountAddress.ofUInt256 address) = some precompiled)
        (_hFailure :
          let target := EvmYul.AccountAddress.ofUInt256 address
          let callMap :=
            evmCallTransfer evm.accountMap evm.executionEnv.codeOwner
              target value
          let callGas :=
            EvmYul.EVM.Ccallgas target target value gas evm.accountMap
              evm.toMachineState evm.substate
          let accessedSubstate :=
            (EvmYul.State.addAccessedAccount evm.toState target).substate
          let childEnv :=
            EvmYul.EVM.thetaCallExecutionEnv
              yul.executionEnv.blobVersionedHashes
              evm.executionEnv.codeOwner evm.executionEnv.sender target
              (.Precompiled precompiled)
              (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice)
              value
              (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
              (evm.executionEnv.depth + 1) evm.executionEnv.header
              evm.executionEnv.perm
          (runPrecompiledContract precompiled callMap
            (EvmYul.UInt256.ofNat callGas) accessedSubstate childEnv).1 =
            false),
        let target := EvmYul.AccountAddress.ofUInt256 address
        let callMap :=
          evmCallTransfer evm.accountMap evm.executionEnv.codeOwner
            target value
        let callGas :=
          EvmYul.EVM.Ccallgas target target value gas evm.accountMap
            evm.toMachineState evm.substate
        let charged : EvmYul.EVM.State :=
          { evm with
            gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
        let accessedSubstate :=
          (EvmYul.State.addAccessedAccount charged.toState target).substate
        let childEnv :=
          EvmYul.EVM.thetaCallExecutionEnv
            yul.executionEnv.blobVersionedHashes
            evm.executionEnv.codeOwner evm.executionEnv.sender target
            (.Precompiled precompiled)
            (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice)
            value
            (charged.memory.readWithPadding inOffset.toNat inSize.toNat)
            (evm.executionEnv.depth + 1) evm.executionEnv.header
            evm.executionEnv.perm
        let precompileResult :=
          runPrecompiledContract precompiled callMap
            (EvmYul.UInt256.ofNat callGas) accessedSubstate childEnv
        let targetGas :=
          (charged.toMachineState.finishExternalCall
            precompileResult.2.2.2.2 inOffset inSize outOffset outSize).gasAvailable +
            precompileResult.2.2.1
        gasAvailableRel
          (yul.toMachineState.finishExternalCall ByteArray.empty
            inOffset inSize outOffset outSize).gasAvailable
          targetGas)
    (hOrdinaryEvidence :
      ∀ {yulRecipient : EvmYul.Account .Yul}
        {yulCallMap : EvmYul.AccountMap .Yul}
        {evmRecipient : EvmYul.Account .EVM}
        {program : Program} {asm : Assembly.Program}
        {target : Assembly.TargetProgram}
        (_hEnough :
          value ≤
            (evm.accountMap.find? evm.executionEnv.codeOwner |>.option ⟨0⟩
              (·.balance)))
        (_hDepth : evm.executionEnv.depth < 1024)
        (_hNotPrecompile :
          EvmYul.PrecompiledContract.ofAddress?
            (EvmYul.AccountAddress.ofUInt256 address) = none)
        (_hFacts :
          OrdinaryCALLBranchFacts yul evm address value yulRecipient
            yulCallMap evmRecipient program asm target),
        OrdinaryCALLChildTopEvidence prim varStackRel terminalCfgRel
          revertCfgRel gasAvailableRel gasValueRel totalGasRel gasCost yul evm
          gas address value inOffset inSize outOffset outSize yulRecipient
          yulCallMap evmRecipient program asm target) :
    ∃ sourceFuel evmFuel,
      CALLPrimitiveRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        sourceFuel evmFuel gasCost yul.executionEnv.blobVersionedHashes
        yul evm store gas address value inOffset inSize outOffset outSize := by
  exact
    CALLPrimitiveRel.of_branchFacts_withOrdinaryBranchRel_stateRelConfig
      (fuel := fuel)
      hShared store hStaticAllowed hBranch hGasEmpty hPrecompiledSuccessGas
      hPrecompiledFailureGas
      (by
        intro yulRecipient yulCallMap evmRecipient program asm target
          hEnough hDepth hNotPrecompile hFacts
        exact
          CALLPrimitiveRel.ordinaryChildTopEvidence_stateRelConfig
            hPrim hShared store hStaticAllowed hEnough hDepth hNotPrecompile
            hFacts
            (hOrdinaryEvidence hEnough hDepth hNotPrecompile hFacts))

theorem CALLPrimitiveRel.of_stateRelConfig_withOrdinaryChildTopEvidence
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {varStackRel : Reference.VarStackRel}
    {terminalCfgRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop}
    {revertCfgRel : Reference.State → EVMState → Prop}
    {gasAvailableRel : Word → Word → Prop}
    {gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm}
    {totalGasRel : Nat → Nat → Prop}
    {fuel gasCost : Nat}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.EVM.State}
    (hShared :
      Reference.SharedStateRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        yul evm.toSharedState)
    (store : EvmYul.Yul.VarStore)
    {gas address value inOffset inSize outOffset outSize : EvmYul.UInt256}
    (hStaticAllowed :
      ¬ (¬ yul.executionEnv.perm ∧ value ≠ ⟨0⟩))
    (hGasEmpty :
      let target := EvmYul.AccountAddress.ofUInt256 address
      let callGas :=
        EvmYul.EVM.Ccallgas target target value gas evm.accountMap
          evm.toMachineState evm.substate
      let charged : EvmYul.EVM.State :=
        { evm with
          gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
      let targetGas :=
        (charged.toMachineState.finishExternalCall ByteArray.empty
          inOffset inSize outOffset outSize).gasAvailable +
          EvmYul.UInt256.ofNat callGas
      gasAvailableRel
        (yul.toMachineState.finishExternalCall ByteArray.empty
          inOffset inSize outOffset outSize).gasAvailable
        targetGas)
    (hPrecompiledSuccessGas :
      ∀ {precompiled : EvmYul.PrecompiledContract}
        (_hPrecompile :
          EvmYul.PrecompiledContract.ofAddress?
            (EvmYul.AccountAddress.ofUInt256 address) = some precompiled)
        (_hSuccess :
          let target := EvmYul.AccountAddress.ofUInt256 address
          let callMap :=
            evmCallTransfer evm.accountMap evm.executionEnv.codeOwner
              target value
          let callGas :=
            EvmYul.EVM.Ccallgas target target value gas evm.accountMap
              evm.toMachineState evm.substate
          let accessedSubstate :=
            (EvmYul.State.addAccessedAccount evm.toState target).substate
          let childEnv :=
            EvmYul.EVM.thetaCallExecutionEnv
              yul.executionEnv.blobVersionedHashes
              evm.executionEnv.codeOwner evm.executionEnv.sender target
              (.Precompiled precompiled)
              (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice)
              value
              (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
              (evm.executionEnv.depth + 1) evm.executionEnv.header
              evm.executionEnv.perm
          (runPrecompiledContract precompiled callMap
            (EvmYul.UInt256.ofNat callGas) accessedSubstate childEnv).1 =
            true),
        let target := EvmYul.AccountAddress.ofUInt256 address
        let callMap :=
          evmCallTransfer evm.accountMap evm.executionEnv.codeOwner
            target value
        let callGas :=
          EvmYul.EVM.Ccallgas target target value gas evm.accountMap
            evm.toMachineState evm.substate
        let charged : EvmYul.EVM.State :=
          { evm with
            gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
        let accessedSubstate :=
          (EvmYul.State.addAccessedAccount charged.toState target).substate
        let childEnv :=
          EvmYul.EVM.thetaCallExecutionEnv
            yul.executionEnv.blobVersionedHashes
            evm.executionEnv.codeOwner evm.executionEnv.sender target
            (.Precompiled precompiled)
            (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice)
            value
            (charged.memory.readWithPadding inOffset.toNat inSize.toNat)
            (evm.executionEnv.depth + 1) evm.executionEnv.header
            evm.executionEnv.perm
        let precompileResult :=
          runPrecompiledContract precompiled callMap
            (EvmYul.UInt256.ofNat callGas) accessedSubstate childEnv
        let targetGas :=
          (charged.toMachineState.finishExternalCall
            precompileResult.2.2.2.2 inOffset inSize outOffset outSize).gasAvailable +
            precompileResult.2.2.1
        gasAvailableRel
          (yul.toMachineState.finishExternalCall
            precompileResult.2.2.2.2 inOffset inSize outOffset outSize).gasAvailable
          targetGas)
    (hPrecompiledFailureGas :
      ∀ {precompiled : EvmYul.PrecompiledContract}
        (_hPrecompile :
          EvmYul.PrecompiledContract.ofAddress?
            (EvmYul.AccountAddress.ofUInt256 address) = some precompiled)
        (_hFailure :
          let target := EvmYul.AccountAddress.ofUInt256 address
          let callMap :=
            evmCallTransfer evm.accountMap evm.executionEnv.codeOwner
              target value
          let callGas :=
            EvmYul.EVM.Ccallgas target target value gas evm.accountMap
              evm.toMachineState evm.substate
          let accessedSubstate :=
            (EvmYul.State.addAccessedAccount evm.toState target).substate
          let childEnv :=
            EvmYul.EVM.thetaCallExecutionEnv
              yul.executionEnv.blobVersionedHashes
              evm.executionEnv.codeOwner evm.executionEnv.sender target
              (.Precompiled precompiled)
              (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice)
              value
              (evm.memory.readWithPadding inOffset.toNat inSize.toNat)
              (evm.executionEnv.depth + 1) evm.executionEnv.header
              evm.executionEnv.perm
          (runPrecompiledContract precompiled callMap
            (EvmYul.UInt256.ofNat callGas) accessedSubstate childEnv).1 =
            false),
        let target := EvmYul.AccountAddress.ofUInt256 address
        let callMap :=
          evmCallTransfer evm.accountMap evm.executionEnv.codeOwner
            target value
        let callGas :=
          EvmYul.EVM.Ccallgas target target value gas evm.accountMap
            evm.toMachineState evm.substate
        let charged : EvmYul.EVM.State :=
          { evm with
            gasAvailable := evm.gasAvailable - EvmYul.UInt256.ofNat gasCost }
        let accessedSubstate :=
          (EvmYul.State.addAccessedAccount charged.toState target).substate
        let childEnv :=
          EvmYul.EVM.thetaCallExecutionEnv
            yul.executionEnv.blobVersionedHashes
            evm.executionEnv.codeOwner evm.executionEnv.sender target
            (.Precompiled precompiled)
            (EvmYul.UInt256.ofNat evm.executionEnv.gasPrice)
            value
            (charged.memory.readWithPadding inOffset.toNat inSize.toNat)
            (evm.executionEnv.depth + 1) evm.executionEnv.header
            evm.executionEnv.perm
        let precompileResult :=
          runPrecompiledContract precompiled callMap
            (EvmYul.UInt256.ofNat callGas) accessedSubstate childEnv
        let targetGas :=
          (charged.toMachineState.finishExternalCall
            precompileResult.2.2.2.2 inOffset inSize outOffset outSize).gasAvailable +
            precompileResult.2.2.1
        gasAvailableRel
          (yul.toMachineState.finishExternalCall ByteArray.empty
            inOffset inSize outOffset outSize).gasAvailable
          targetGas)
    (hOrdinaryEvidence :
      ∀ {yulRecipient : EvmYul.Account .Yul}
        {yulCallMap : EvmYul.AccountMap .Yul}
        {evmRecipient : EvmYul.Account .EVM}
        {program : Program} {asm : Assembly.Program}
        {target : Assembly.TargetProgram}
        (_hEnough :
          value ≤
            (evm.accountMap.find? evm.executionEnv.codeOwner |>.option ⟨0⟩
              (·.balance)))
        (_hDepth : evm.executionEnv.depth < 1024)
        (_hNotPrecompile :
          EvmYul.PrecompiledContract.ofAddress?
            (EvmYul.AccountAddress.ofUInt256 address) = none)
        (_hFacts :
          OrdinaryCALLBranchFacts yul evm address value yulRecipient
            yulCallMap evmRecipient program asm target),
        OrdinaryCALLChildTopEvidence prim varStackRel terminalCfgRel
          revertCfgRel gasAvailableRel gasValueRel totalGasRel gasCost yul evm
          gas address value inOffset inSize outOffset outSize yulRecipient
          yulCallMap evmRecipient program asm target) :
    ∃ sourceFuel evmFuel,
      CALLPrimitiveRel
        (stateRelConfig varStackRel terminalCfgRel revertCfgRel
          gasAvailableRel gasValueRel totalGasRel)
        sourceFuel evmFuel gasCost yul.executionEnv.blobVersionedHashes
        yul evm store gas address value inOffset inSize outOffset outSize := by
  exact
    CALLPrimitiveRel.of_branchFacts_withOrdinaryChildTopEvidence_stateRelConfig
      (fuel := fuel)
      hPrim hShared store hStaticAllowed
      (CALLBranchFacts_stateRelConfig hShared address value)
      hGasEmpty hPrecompiledSuccessGas hPrecompiledFailureGas
      hOrdinaryEvidence

end World

end Yul
end EvmCompiler
