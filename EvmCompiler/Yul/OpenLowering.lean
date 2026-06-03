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
