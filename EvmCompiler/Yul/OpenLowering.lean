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
