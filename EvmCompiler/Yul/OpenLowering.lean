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
