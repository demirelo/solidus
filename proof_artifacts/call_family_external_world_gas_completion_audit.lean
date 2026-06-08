import EvmCompiler.LayerAudit

/-!
Completion audit for the external-world CALL/CREATE boundary-family gas
liveness/safety endpoint.

This file is not a new proof route. It pins the current public theorem spine and
checks the key response-safety facts used by the final audit. The public spine
starts at direct checked imported-Yul CALL/CREATE wrappers, not at a raw
canonical-entry package or lower unbundled compiled endpoint names.
-/

namespace EvmCompiler

#check LayerAudit.ImportedYulOpenCALLBoundary.openXBoundaryFamilySharedResponseExternalWorldReadyFor
#check LayerAudit.ImportedYulOpenCALLBoundary.sourceOpenTraceExternalResponsesAdmissible
#check LayerAudit.sourceOpenTargetCommittedObservationRelStorageEq
#check LayerAudit.sourceOpenTargetCommittedObservationRelTransientStorageEq
#check LayerAudit.sourceOpenTargetCommittedObservationRelExternalCodeEq
#check LayerAudit.sourceOpenTargetCommittedObservationRelBalanceEq
#check LayerAudit.sourceOpenTargetCommittedObservationRelTransactionReceiptsEq
#check LayerAudit.sourceOpenTargetCommittedObservationRelSubstateEq
#check LayerAudit.FunctionsOpenCALLBoundary.openExternalCallKindCallSiteEqOfArgs
#check LayerAudit.FunctionsOpenCALLBoundary.openExternalCreateKindCreateSiteEqOfArgs
#check LayerAudit.FunctionsOpenCALLBoundary.openExternalOpenCallRel
#check LayerAudit.FunctionsOpenCALLBoundary.openExternalOpenCallRelPreservesResponse
#check LayerAudit.FunctionsOpenCALLBoundary.openExternalOpenCreateRel
#check LayerAudit.FunctionsOpenCALLBoundary.openExternalOpenCreateRelPreservesResponse
#check LayerAudit.sourceStateRelOpenExternalPrimitiveCallSiteEqOfArgs
#check LayerAudit.sourceStateRelOpenExternalPrimitiveCreateSiteEqOfArgs

#check LayerAudit.ImportedYulOpenCALLBoundary.checkedCALLFamilyRegularOpenAssemblyInferredBoundStackSafeReturnDataCopyBoundsTargetCurrentNoCallReturnDataCopyBoundsReady
#check LayerAudit.ImportedYulOpenCALLBoundary.checkedImportedYulCallCreateCurrentNoCallReturnDataCopyBoundsReady

#check LayerAudit.ImportedYulOpenCALLBoundary.checkedImportedYulCallCreateFinalObservation
#check LayerAudit.ImportedYulOpenCALLBoundary.checkedImportedYulCallCreateAtGas
#check LayerAudit.ImportedYulOpenCALLBoundary.checkedImportedYulCallCreateOutcomeSafetyAtGas
#check LayerAudit.ImportedYulOpenCALLBoundary.checkedImportedYulCallCreateResultOrFailureAtGas

example
    {cfg : Yul.Reference.StateRelConfig}
    {initialShared : EvmYul.SharedState .Yul}
    {initial : Yul.EVMState}
    {sourceResult : Except Yul.Reference.Exception Yul.Reference.State}
    {targetResult : Assembly.StepResult}
    (hRel :
      Yul.Program.SourceOpenTargetCommittedObservationRel cfg initialShared
        initial sourceResult targetResult)
    (address : EvmYul.AccountAddress) :
    (Yul.Program.SourceOpenCommittedAccountMap? initialShared sourceResult).bind
        (fun accounts => Yul.Reference.AccountStorage? accounts address) =
      (Yul.Program.TargetCommittedAccountMap? initial targetResult).bind
        (fun accounts => Yul.Reference.AccountStorage? accounts address) :=
  Yul.Program.SourceOpenTargetCommittedObservationRel.storage_eq hRel address

example
    {cfg : Yul.Reference.StateRelConfig}
    {initialShared : EvmYul.SharedState .Yul}
    {initial : Yul.EVMState}
    {sourceResult : Except Yul.Reference.Exception Yul.Reference.State}
    {targetResult : Assembly.StepResult}
    {sourceState : EvmYul.State .Yul}
    {targetState : EvmYul.State .EVM}
    (hRel :
      Yul.Program.SourceOpenTargetCommittedObservationRel cfg initialShared
        initial sourceResult targetResult)
    (hSource :
      Yul.Program.SourceOpenCommittedState? initialShared sourceResult =
        some sourceState)
    (hTarget :
      Yul.Program.TargetCommittedState? initial targetResult = some targetState)
    (balanceAddress : EvmYul.UInt256)
    (accountAddress : EvmYul.AccountAddress) :
    (EvmYul.State.balance sourceState balanceAddress).2 =
        (EvmYul.State.balance targetState balanceAddress).2 ∧
      Yul.Reference.AccountTransientStorage? sourceState.accountMap accountAddress =
        Yul.Reference.AccountTransientStorage? targetState.accountMap accountAddress ∧
      Yul.Reference.AccountCodeImage sourceState.accountMap accountAddress =
        Yul.Reference.AccountCodeImage targetState.accountMap accountAddress ∧
      sourceState.transactionReceipts = targetState.transactionReceipts ∧
      sourceState.substate = targetState.substate := by
  exact
    ⟨Yul.Program.SourceOpenTargetCommittedObservationRel.balance_eq
        hRel hSource hTarget balanceAddress,
      Yul.Program.SourceOpenTargetCommittedObservationRel.transientStorage_eq
        hRel hSource hTarget accountAddress,
      Yul.Program.SourceOpenTargetCommittedObservationRel.externalCode_eq
        hRel hSource hTarget accountAddress,
      Yul.Program.SourceOpenTargetCommittedObservationRel.transactionReceipts_eq
        hRel hSource hTarget,
      Yul.Program.SourceOpenTargetCommittedObservationRel.substate_eq
        hRel hSource hTarget⟩

example
    {yulState : EvmYul.Yul.State}
    {evmState : EvmYul.EVM.State}
    (hRel :
      Yul.OpenExternal.CallContextRel
        (Yul.OpenExternal.CallContext.ofYulState yulState)
        (Yul.OpenExternal.CallContext.ofEVMState evmState))
    (kind : Yul.OpenExternal.CallKind)
    (operands : Yul.OpenExternal.CallOperands)
    (stackRest : Yul.OpenExternal.Stack) :
    kind.yulCallSite? yulState (kind.args operands) =
        some
          ((Yul.OpenExternal.CallContext.ofEVMState evmState).callSite kind
            (kind.canonicalOperands operands)) ∧
      kind.evmCallSite?
          ({ evmState with stack := kind.args operands ++ stackRest }
            : EvmYul.EVM.State) =
        some
          (stackRest,
            (Yul.OpenExternal.CallContext.ofEVMState evmState).callSite kind
              (kind.canonicalOperands operands)) :=
  Yul.OpenExternal.CallKind.callSite_eq_of_args hRel kind operands stackRest

example
    {yulState : EvmYul.Yul.State}
    {evmState : EvmYul.EVM.State}
    (hRel :
      Yul.OpenExternal.CallContextRel
        (Yul.OpenExternal.CallContext.ofYulState yulState)
        (Yul.OpenExternal.CallContext.ofEVMState evmState))
    (kind : Yul.OpenExternal.CreateKind)
    (operands : Yul.OpenExternal.CreateOperands)
    (stackRest : Yul.OpenExternal.Stack) :
    kind.yulCreateSite? yulState (kind.args operands) =
        some
          ((Yul.OpenExternal.CallContext.ofEVMState evmState).createSite kind
            (kind.canonicalOperands operands)) ∧
      kind.evmCreateSite?
          ({ evmState with stack := kind.args operands ++ stackRest }
            : EvmYul.EVM.State) =
        some
          (stackRest,
            (Yul.OpenExternal.CallContext.ofEVMState evmState).createSite kind
              (kind.canonicalOperands operands)) :=
  Yul.OpenExternal.CreateKind.createSite_eq_of_args hRel kind operands
    stackRest

example
    {cfg : Yul.Reference.StateRelConfig}
    {layout : List Yul.Name}
    {source : Yul.Reference.State}
    {compiler : Objects.Source.State}
    (hRel :
      Yul.Reference.SourceBridgeFacts.SourceStateRel cfg layout source
        compiler)
    (kind : Yul.OpenExternal.CallKind)
    (operands : Yul.OpenExternal.CallOperands) :
    kind.yulCallSite? source (kind.args operands) =
      Yul.OpenExternal.CallKind.primitiveCallSite? compiler.shared kind
        (kind.args operands).reverse :=
  Yul.Reference.SourceBridgeFacts.SourceStateRel.openExternalPrimitiveCallSite_eq_of_args
    hRel kind operands

example
    {cfg : Yul.Reference.StateRelConfig}
    {layout : List Yul.Name}
    {source : Yul.Reference.State}
    {compiler : Objects.Source.State}
    (hRel :
      Yul.Reference.SourceBridgeFacts.SourceStateRel cfg layout source
        compiler)
    (kind : Yul.OpenExternal.CreateKind)
    (operands : Yul.OpenExternal.CreateOperands) :
    kind.yulCreateSite? source (kind.args operands) =
      Yul.OpenExternal.CreateKind.primitiveCreateSite? compiler.shared kind
        (kind.args operands).reverse :=
  Yul.Reference.SourceBridgeFacts.SourceStateRel.openExternalPrimitiveCreateSite_eq_of_args
    hRel kind operands

example
    {SourceState TargetState : Type}
    {responseRel : Yul.OpenExternal.CallResponse → Prop}
    {stateRel : SourceState → TargetState → Prop}
    {source : Yul.OpenExternal.OpenCall SourceState}
    {target : Yul.OpenExternal.OpenCall TargetState}
    (hRel :
      Yul.OpenExternal.OpenCallRel responseRel stateRel source target) :
    source.site = target.site :=
  hRel.sameSite

example
    {SourceState TargetState : Type}
    {responseRel : Yul.OpenExternal.CallResponse → Prop}
    {stateRel : SourceState → TargetState → Prop}
    {source : Yul.OpenExternal.OpenCall SourceState}
    {target : Yul.OpenExternal.OpenCall TargetState}
    (hRel :
      Yul.OpenExternal.OpenCallRel responseRel stateRel source target)
    (response : Yul.OpenExternal.CallResponse)
    (hResponse : responseRel response) :
    stateRel (source.resume response) (target.resume response) :=
  Yul.OpenExternal.OpenCallRel.preserves_response hRel response hResponse

example
    {SourceState TargetState : Type}
    {responseRel : Yul.OpenExternal.CreateResponse → Prop}
    {stateRel : SourceState → TargetState → Prop}
    {source : Yul.OpenExternal.OpenCreate SourceState}
    {target : Yul.OpenExternal.OpenCreate TargetState}
    (hRel :
      Yul.OpenExternal.OpenCreateRel responseRel stateRel source target) :
    source.site = target.site :=
  hRel.sameSite

example
    {SourceState TargetState : Type}
    {responseRel : Yul.OpenExternal.CreateResponse → Prop}
    {stateRel : SourceState → TargetState → Prop}
    {source : Yul.OpenExternal.OpenCreate SourceState}
    {target : Yul.OpenExternal.OpenCreate TargetState}
    (hRel :
      Yul.OpenExternal.OpenCreateRel responseRel stateRel source target)
    (response : Yul.OpenExternal.CreateResponse)
    (hResponse : responseRel response) :
    stateRel (source.resume response) (target.resume response) :=
  Yul.OpenExternal.OpenCreateRel.preserves_response hRel response hResponse

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
    {left right : Yul.OpenExternal.CreateResponse}
    (hSafe :
      Yul.Program.OpenCreateResponsesCommittedSafeEquivalent left right) :
    left.address = right.address ∧
      left.returnData = right.returnData ∧
      Yul.Program.OpenCallReentrantMutationEquivalent
        left.internalMutation right.internalMutation := by
  exact
    ⟨hSafe.address_eq, hSafe.returnData_eq,
      fun state => hSafe.internalMutation_apply_eq state⟩

example
    {left right : Yul.OpenExternal.CreateResponse}
    (hNe : left.address ≠ right.address) :
    ¬ Yul.Program.OpenCreateResponsesCommittedSafeEquivalent left right := by
  intro hSafe
  exact hNe hSafe.address_eq

#print axioms Yul.Program.compileCheckedAssemblyTargetBytecodeResourcesCALLFamilyFeaturesSourceStaticRegularOpenAssemblyInferredBoundStackSafe?_currentNoCallReturnDataCopyBoundsReady
#print axioms LayerAudit.ImportedYulOpenCALLBoundary.checkedImportedYulCallCreateOutcomeSafetyAtGas
#print axioms LayerAudit.ImportedYulOpenCALLBoundary.checkedImportedYulCallCreateResultOrFailureAtGas

end EvmCompiler
