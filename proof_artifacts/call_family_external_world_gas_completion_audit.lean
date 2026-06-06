import EvmCompiler.LayerAudit

/-!
Completion audit for the external-world CALL gas liveness/safety endpoint.

This file is not a new proof route. It pins the current public theorem spine and
checks the key response-safety facts used by the final audit. The public spine
starts at the stronger top-assumption package, not at the lower unbundled
compiled endpoint names.
-/

namespace EvmCompiler

#check LayerAudit.ImportedYulOpenCALLBoundary.openXCallFamilyExternalWorldReadyFor
#check LayerAudit.ImportedYulOpenCALLBoundary.openXCallFamilyExternalWorldReadyForCommittedSafeOrAllForwardedGasOutOfGasTracks
#check LayerAudit.ImportedYulOpenCALLBoundary.openXCallFamilyExternalWorldReadyForAllForwardedGasOutOfGasAndOutcomeTracksOfNotCommittedSafeForCall

#check LayerAudit.ImportedYulOpenCALLBoundary.recursiveBridgeCALLFamilyRegularOpenAssemblyInferredBoundStackSafeNoReturnDataCopyTopAssumptionsOpenXContractLivenessAndSafetyFinalObservation
#check LayerAudit.ImportedYulOpenCALLBoundary.recursiveBridgeCALLFamilyRegularOpenAssemblyInferredBoundStackSafeNoReturnDataCopyTopAssumptionsOpenXContractLivenessAndSafetyAtGas
#check LayerAudit.ImportedYulOpenCALLBoundary.recursiveBridgeCALLFamilyRegularOpenAssemblyInferredBoundStackSafeNoReturnDataCopyTopAssumptionsOpenXContractLivenessAndSafetyOutcomeSafetyAtGas
#check LayerAudit.ImportedYulOpenCALLBoundary.recursiveBridgeCALLFamilyRegularOpenAssemblyInferredBoundStackSafeNoReturnDataCopyTopAssumptionsOpenXContractLivenessAndSafetyResultOrFailureAtGas

example
    {left right : Yul.OpenExternal.CallResponse}
    (hSafe :
      Yul.Program.OpenCallResponsesCommittedSafeEquivalent left right) :
    left.success = right.success ∧
      left.returnData = right.returnData ∧
      Yul.Program.OpenCallReentrantMutationEquivalent
        left.internalMutation right.internalMutation := by
  exact
    ⟨hSafe.success_eq, hSafe.returnData_eq,
      fun state => hSafe.internalMutation_apply_eq state⟩

example
    {left right : Yul.OpenExternal.CallResponse}
    (hNe : left.success ≠ right.success) :
    ¬ Yul.Program.OpenCallResponsesCommittedSafeEquivalent left right := by
  intro hSafe
  exact hNe hSafe.success_eq

example
    {candidateForwardedGas candidateAvailableGas candidatePostCallGas : Nat}
    {candidateStatus : Yul.Program.OpenCallChildGasStatus}
    {candidateResponse : Yul.OpenExternal.CallResponse}
    (hOOG :
      Yul.Program.OpenCallAllForwardedGasOutOfGas
        candidateForwardedGas candidateAvailableGas candidatePostCallGas
        candidateStatus candidateResponse) :
    candidateResponse.success = false :=
  hOOG.success_false

#print axioms Yul.Program.OpenCallResponsesCommittedSafeEquivalent.evmOpenCall_resume_eq
#print axioms Yul.Program.OpenXCallFamilyExternalWorldReadyFor.allForwardedGasOutOfGas_and_outcomeTracks_of_not_committedSafe_for_call
#print axioms Yul.OpenGasAware.OpenXCommittedSafeAt.to_outcome_safety
#print axioms Yul.Program.RecursiveBridgeCALLFamilyRegularOpenAssemblyInferredBoundStackSafeNoReturnDataCopyTopAssumptions.openXContractLivenessAndSafetyOutcomeSafetyAtGas
#print axioms Yul.Program.RecursiveBridgeCALLFamilyRegularOpenAssemblyInferredBoundStackSafeNoReturnDataCopyTopAssumptions.openXContractLivenessAndSafetyResultOrFailureAtGas

end EvmCompiler
