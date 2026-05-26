import EvmCompiler.TypedCfg.Lower
import EvmCompiler.Assembly.Semantics

namespace EvmCompiler
namespace TypedCfg
namespace Preservation

/-!
Preservation boundary for the `TypedCfg -> Assembly` pass.

This is the adjacent proof boundary where typed stack shapes, symbolic labels,
and hidden typed return frames are allowed to meet the concrete labeled
assembly stack.  No higher layer should import the relations in this file
directly.

The source semantics is `TypedCfg.Program.run`; it does not execute by lowering
to assembly.  The target semantics is `Assembly.Source.runNResult` over the
labeled assembly program produced by `TypedCfg.Program.lower?`.
-/

abbrev SourceResult :=
  Except EVMException Outcome

abbrev TargetResult :=
  Except Assembly.EVMException Assembly.StepResult

structure CompilesTo (program : CheckedProgram) (asm : Assembly.Program) :
    Prop where
  lower_eq : program.lower? = some asm

namespace ReturnEncoding

def frameToken? (program : Program) (sites : List CallSite)
    (frame : ReturnFrame) : Option Word := do
  let site ← sites.find?
    (fun site =>
      site.procName == frame.procName &&
        site.returnLabel == frame.returnLabel)
  let proc ← program.findProc? frame.procName
  if proc.retc = frame.retc then
    some site.token
  else
    none

def stack? (program : Program) (sites : List CallSite) :
    List ReturnFrame → EvmYul.Stack Word → Option (EvmYul.Stack Word)
  | [], current => some current
  | frame :: rest, current => do
      let token ← frameToken? program sites frame
      let caller ← stack? program sites rest frame.callerStack
      some (current ++ token :: caller)

@[simp] theorem stack?_nil (program : Program) (sites : List CallSite)
    (current : EvmYul.Stack Word) :
    stack? program sites [] current = some current := rfl

end ReturnEncoding

def withPcAndStack (state : EVMState) (pc : Nat)
    (stack : EvmYul.Stack Word) : Assembly.EVMState :=
  { state with pc := EvmYul.UInt256.ofNat pc, stack := stack }

structure PayloadRel (program : Program) (sites : List CallSite)
    (source : RunState) (target : Assembly.EVMState) : Prop where
  shared_eq : target.toSharedState = source.evm.toSharedState
  stack_eq :
    ReturnEncoding.stack? program sites source.returns source.evm.stack =
      some target.stack

/--
Relation between a typed CFG suspension point and a labeled-assembly machine
state.

The assembly stack materializes the typed current stack plus the hidden
defunctionalized return-token stack used by the lowering pass.  The assembly
program counter points at the label corresponding to the typed CFG label.
-/
structure StateRel (program : Program) (asm : Assembly.Program)
    (sites : List CallSite) (label : Label) (source : RunState)
    (target : Assembly.EVMState) : Prop where
  source_suspended : program.suspendedAt? label source = true
  label_pc : ∃ pc, Assembly.Program.labelPc asm label = some pc ∧
    ∃ stack,
      ReturnEncoding.stack? program sites source.returns source.evm.stack =
        some stack ∧
      target = withPcAndStack source.evm pc stack

theorem payloadRel_of_stateRel {program : Program} {asm : Assembly.Program}
    {sites : List CallSite} {label : Label} {source : RunState}
    {target : Assembly.EVMState}
    (h : StateRel program asm sites label source target) :
    PayloadRel program sites source target := by
  rcases h.label_pc with ⟨pc, _hPc, stack, hStack, hTarget⟩
  constructor
  · simp [hTarget, withPcAndStack]
  · simp [hTarget, withPcAndStack, hStack]

def InitialRel (program : Program) (asm : Assembly.Program)
    (source : EVMState) (target : Assembly.EVMState) : Prop :=
  StateRel program asm (Program.collectCallSites program) program.entry
    (RunState.initial source) target

/--
Result relation for the adjacent lowering theorem.

Typed `fallthrough` is realized as an assembly `STOP`, because assembly is a
flat instruction stream and cannot otherwise distinguish semantic completion
from physically falling into the next emitted block.
-/
inductive ResultRel (program : Program) (asm : Assembly.Program)
    (sites : List CallSite) : SourceResult → TargetResult → Prop where
  | fallthroughStop {source : RunState} {halt : Assembly.Halt}
      (hKind : halt.kind = .stop)
      (hPayload : PayloadRel program sites source halt.state) :
      ResultRel program asm sites
        (.ok (.fallthrough source)) (.ok (.halted halt))
  | halt {kind : Assembly.HaltKind} {source : RunState}
      {halt : Assembly.Halt}
      (hKind : halt.kind = kind)
      (hPayload : PayloadRel program sites source halt.state) :
      ResultRel program asm sites
        (.ok (.halt kind source)) (.ok (.halted halt))
  | invalid {source : RunState} :
      ResultRel program asm sites
        (.ok (.invalid source)) (.error .InvalidInstruction)
  | outOfFuel {label : Label} {source : RunState}
      {target : Assembly.EVMState}
      (hState : StateRel program asm sites label source target) :
      ResultRel program asm sites
        (.ok (.outOfFuel label source)) (.ok (.running target))
  | error {err : EVMException} :
      ResultRel program asm sites (.error err) (.error err)

/--
Whole-program preservation target for one successfully lowered checked typed
CFG.

This statement deliberately exposes no replay certificate, label table,
return-token table, per-procedure oracle, or generated-code evidence.  Those
facts must be constructed inside the proof from `program.lower? = some asm`.
-/
def PreservesLowered (program : CheckedProgram) (asm : Assembly.Program) :
    Prop :=
  ∀ fuel sourceInitial targetInitial sourceResult,
    InitialRel program.program asm sourceInitial targetInitial →
      Program.run fuel program.program sourceInitial = sourceResult →
        ∃ targetFuel targetResult,
          Assembly.Source.runNResult asm targetFuel targetInitial =
            targetResult ∧
          ResultRel program.program asm (Program.collectCallSites program.program)
            sourceResult targetResult

/--
Public theorem target for this pass.

The final proof should prove assembly acceptedness and semantic preservation
from checked typed-CFG lowering alone.
-/
def CompilePreserves : Prop :=
  ∀ program asm,
    CompilesTo program asm →
      Assembly.Accepted asm ∧ PreservesLowered program asm

namespace Terminator

theorem lower?_fallthrough {program : Program} {sites : List CallSite}
    {label : Label} :
    TypedCfg.Terminator.lower? program sites label .fallthrough =
      some [.prim .stop] := rfl

end Terminator

namespace Program

theorem runFrom_zero_resultRel {program : Program} {asm : Assembly.Program}
    {sites : List CallSite} {label : Label} {source : RunState}
    {target : Assembly.EVMState}
    (hRel : StateRel program asm sites label source target) :
    ResultRel program asm sites
      (TypedCfg.Program.runFrom 0 program label source)
      (Assembly.Source.runNResult asm 0 target) := by
  simp [TypedCfg.Program.runFrom, Assembly.Source.runNResult,
    hRel.source_suspended]
  exact ResultRel.outOfFuel hRel

theorem run_zero_resultRel {program : CheckedProgram}
    {asm : Assembly.Program} {sourceInitial targetInitial}
    (hRel : InitialRel program.program asm sourceInitial targetInitial) :
    ResultRel program.program asm (TypedCfg.Program.collectCallSites program.program)
      (TypedCfg.Program.run 0 program.program sourceInitial)
      (Assembly.Source.runNResult asm 0 targetInitial) := by
  simpa [TypedCfg.Program.run, InitialRel] using
    runFrom_zero_resultRel
      (program := program.program)
      (asm := asm)
      (sites := TypedCfg.Program.collectCallSites program.program)
      (label := program.program.entry)
      (source := RunState.initial sourceInitial)
      (target := targetInitial)
      hRel

theorem preservesLowered_zero {program : CheckedProgram}
    {asm : Assembly.Program} {sourceInitial targetInitial sourceResult}
    (hRel : InitialRel program.program asm sourceInitial targetInitial)
    (hRun : TypedCfg.Program.run 0 program.program sourceInitial = sourceResult) :
    ∃ targetFuel targetResult,
      Assembly.Source.runNResult asm targetFuel targetInitial = targetResult ∧
        ResultRel program.program asm
          (TypedCfg.Program.collectCallSites program.program)
          sourceResult targetResult := by
  refine ⟨0, Assembly.Source.runNResult asm 0 targetInitial, rfl, ?_⟩
  rw [← hRun]
  exact run_zero_resultRel (program := program) (asm := asm) hRel

end Program

end Preservation
end TypedCfg
end EvmCompiler
