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

theorem stack?_push_current {program : Program} {sites : List CallSite}
    {returns : List ReturnFrame} {current target : EvmYul.Stack Word}
    {value : Word}
    (hStack : stack? program sites returns current = some target) :
    stack? program sites returns (value :: current) =
      some (value :: target) := by
  induction returns generalizing current target with
  | nil =>
      simp at hStack ⊢
      exact hStack
  | cons frame rest ih =>
      simp [stack?] at hStack ⊢
      cases hToken : frameToken? program sites frame with
      | none =>
          simp [hToken] at hStack
      | some token =>
          simp [hToken] at hStack
          cases hCaller :
              stack? program sites rest frame.callerStack with
          | none =>
              simp [hCaller] at hStack
          | some caller =>
              simp [hCaller] at hStack
              cases hStack
              simp

theorem stack?_suffix {program : Program} {sites : List CallSite}
    {returns : List ReturnFrame} {current target : EvmYul.Stack Word}
    (hStack : stack? program sites returns current = some target) :
    ∃ suffix,
      target = current ++ suffix ∧
        ∀ newCurrent : EvmYul.Stack Word,
          stack? program sites returns newCurrent =
            some (newCurrent ++ suffix) := by
  cases returns with
  | nil =>
      simp at hStack
      cases hStack
      refine ⟨[], ?_, ?_⟩
      · simp
      · intro newCurrent
        simp [stack?]
  | cons frame rest =>
      simp [stack?] at hStack
      cases hToken : frameToken? program sites frame with
      | none =>
          simp [hToken] at hStack
      | some token =>
          simp [hToken] at hStack
          cases hCaller :
              stack? program sites rest frame.callerStack with
          | none =>
              simp [hCaller] at hStack
          | some caller =>
              simp [hCaller] at hStack
              cases hStack
              refine ⟨token :: caller, ?_, ?_⟩
              · simp
              · intro newCurrent
                simp [stack?, hToken, hCaller]

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

namespace PayloadRel

theorem hidden_suffix {program : Program} {sites : List CallSite}
    {source : RunState} {target : Assembly.EVMState}
    (h : PayloadRel program sites source target) :
    ∃ suffix,
      target.stack = source.evm.stack ++ suffix ∧
        ∀ newVisible : EvmYul.Stack Word,
          ReturnEncoding.stack? program sites source.returns newVisible =
            some (newVisible ++ suffix) := by
  exact ReturnEncoding.stack?_suffix h.stack_eq

theorem replace_visible_stack {program : Program} {sites : List CallSite}
    {source : RunState} {target : Assembly.EVMState}
    (h : PayloadRel program sites source target)
    (newVisible : EvmYul.Stack Word) :
    ∃ suffix,
      target.stack = source.evm.stack ++ suffix ∧
        PayloadRel program sites
          (source.withEVM { source.evm with stack := newVisible })
          { target with stack := newVisible ++ suffix } := by
  rcases h.hidden_suffix with ⟨suffix, hTargetStack, hMaterialize⟩
  refine ⟨suffix, hTargetStack, ?_⟩
  constructor
  · simp [RunState.withEVM, h.shared_eq]
  · simpa [RunState.withEVM] using hMaterialize newVisible

theorem with_visible_evm_from_suffix {program : Program}
    {sites : List CallSite} {source : RunState}
    {sourceEVM' : EVMState} {target' : Assembly.EVMState}
    {suffix : EvmYul.Stack Word}
    (hSuffix :
      ∀ newVisible : EvmYul.Stack Word,
        ReturnEncoding.stack? program sites source.returns newVisible =
          some (newVisible ++ suffix))
    (hShared : target'.toSharedState = sourceEVM'.toSharedState)
    (hStack : target'.stack = sourceEVM'.stack ++ suffix) :
    PayloadRel program sites (source.withEVM sourceEVM') target' := by
  constructor
  · simpa [RunState.withEVM] using hShared
  · simpa [RunState.withEVM, hStack] using hSuffix sourceEVM'.stack

theorem push {program : Program} {sites : List CallSite}
    {source : RunState} {target : Assembly.EVMState} {value : Word}
    (h : PayloadRel program sites source target) :
    PayloadRel program sites
      (source.withEVM
        (source.evm.replaceStackAndIncrPC
          (source.evm.stack.push value) (pcΔ := Assembly.Instr.push32Size)))
      (target.replaceStackAndIncrPC
        (target.stack.push value) (pcΔ := Assembly.Instr.push32Size)) := by
  constructor
  · simp [RunState.withEVM, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, h.shared_eq]
  · simp [RunState.withEVM, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, EvmYul.Stack.push]
    exact ReturnEncoding.stack?_push_current h.stack_eq

theorem pop_step_target {program : Program} {sites : List CallSite}
    {source : RunState} {target : Assembly.EVMState} {sourceEVM' : EVMState}
    (hRel : PayloadRel program sites source target)
    (hStep : Assembly.PrimOp.pop.step source.evm = .ok sourceEVM') :
    ∃ target',
      Assembly.Target.runList [.prim .pop] target = .ok target' ∧
        PayloadRel program sites (source.withEVM sourceEVM') target' := by
  rcases hRel.hidden_suffix with ⟨suffix, hTargetStack, hSuffix⟩
  cases hSourceStack : source.evm.stack with
  | nil =>
      simp [Assembly.PrimOp.step, Assembly.PrimOp.continuingStep?,
        Assembly.PrimStep.run, EvmYul.Stack.pop, hSourceStack] at hStep
  | cons value rest =>
      simp [Assembly.PrimOp.step, Assembly.PrimOp.continuingStep?,
        Assembly.PrimStep.run, EvmYul.Stack.pop, hSourceStack,
        EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC] at hStep
      cases hStep
      let target' := target.replaceStackAndIncrPC (rest ++ suffix)
      refine ⟨target', ?_, ?_⟩
      · simp [Assembly.Target.runList, Assembly.Target.stepInstr,
          Assembly.PrimOp.step, Assembly.PrimOp.continuingStep?,
          Assembly.PrimStep.run, EvmYul.Stack.pop, hTargetStack,
          hSourceStack, target',
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC]
        rfl
      · exact
          PayloadRel.with_visible_evm_from_suffix
            (program := program) (sites := sites) (source := source)
            (sourceEVM' :=
              { source.evm with
                pc := source.evm.pc + EvmYul.UInt256.ofNat 1
                stack := rest })
            (target' := target') (suffix := suffix) hSuffix
            (by
              simp [target',
                EvmYul.EVM.State.replaceStackAndIncrPC,
                EvmYul.EVM.State.incrPC, hRel.shared_eq])
            (by
              simp [target',
                EvmYul.EVM.State.replaceStackAndIncrPC,
                EvmYul.EVM.State.incrPC])

end PayloadRel

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

namespace Shape

theorem matchesStack_length {shape : Shape} {stack : EvmYul.Stack Word}
    (hMatches : shape.matchesStack stack = true) :
    shape.length = stack.length := by
  induction shape generalizing stack with
  | nil =>
      cases stack <;> simp [TypedCfg.Shape.matchesStack] at hMatches ⊢
  | cons slot rest ih =>
      cases stack with
      | nil =>
          simp [TypedCfg.Shape.matchesStack] at hMatches
      | cons value values =>
          have hTail : TypedCfg.Shape.matchesStack rest values = true := by
            have hSplit :
                slot.matchesValue value = true ∧
                  TypedCfg.Shape.matchesStack rest values = true := by
              simpa [TypedCfg.Shape.matchesStack] using hMatches
            exact hSplit.2
          simp [ih hTail]

theorem matchesStack_drop (n : Nat) {shape : Shape}
    {stack : EvmYul.Stack Word}
    (hMatches : TypedCfg.Shape.matchesStack shape stack = true) :
    TypedCfg.Shape.matchesStack (shape.drop n) (stack.drop n) = true := by
  induction n generalizing shape stack with
  | zero =>
      simpa using hMatches
  | succ n ih =>
      cases shape with
      | nil =>
          cases stack <;> simp [TypedCfg.Shape.matchesStack] at hMatches ⊢
      | cons slot rest =>
          cases stack with
          | nil =>
              simp [TypedCfg.Shape.matchesStack] at hMatches
          | cons value values =>
              have hTail : TypedCfg.Shape.matchesStack rest values = true := by
                have hSplit :
                    slot.matchesValue value = true ∧
                      TypedCfg.Shape.matchesStack rest values = true := by
                  simpa [TypedCfg.Shape.matchesStack] using hMatches
                exact hSplit.2
              simpa using ih hTail

theorem matchesStack_drop_of_unwindTo {target current : Shape}
    {stack : EvmYul.Stack Word}
    (hUnwind : Shape.unwindTo target current = some target)
    (hMatches : TypedCfg.Shape.matchesStack current stack = true) :
    TypedCfg.Shape.matchesStack target
      (stack.drop (current.length - target.length)) = true := by
  unfold Shape.unwindTo at hUnwind
  by_cases hCond :
      target.length ≤ current.length ∧
        current.drop (current.length - target.length) = target
  · simp [hCond] at hUnwind
    have hDrop :=
      matchesStack_drop (current.length - target.length) hMatches
    simpa [hCond.2] using hDrop
  · simp [hCond] at hUnwind

end Shape

namespace Terminator

theorem lower?_fallthrough {program : Program} {sites : List CallSite}
    {label : Label} :
    TypedCfg.Terminator.lower? program sites label .fallthrough =
      some [.prim .stop] := rfl

end Terminator

namespace Instr

theorem lowerWithShape?_type? {instr : TypedCfg.Instr} {shape : Shape}
    {code : Assembly.Program} {output : Shape}
    (hLower : instr.lowerWithShape? shape = some (code, output)) :
    instr.type? shape = some output := by
  unfold TypedCfg.Instr.lowerWithShape? at hLower
  cases hType : instr.type? shape with
  | none =>
      simp [hType] at hLower
  | some typedOutput =>
      cases instr <;> simp [hType, TypedCfg.Instr.lower?] at hLower
      case push value =>
        rcases hLower with ⟨_hCode, hOutput⟩
        rw [hOutput]
      case prim op =>
        rcases hLower with ⟨_hCode, hOutput⟩
        rw [hOutput]
      case pop =>
        rcases hLower with ⟨_hCode, hOutput⟩
        rw [hOutput]
      case dup depth =>
        cases hCode : TypedCfg.Instr.dup? depth with
        | none =>
            simp [hCode] at hLower
        | some lowered =>
            simp [hCode] at hLower
            rcases hLower with ⟨_hCode, hOutput⟩
            rw [hOutput]
      case swap depth =>
        cases hCode : TypedCfg.Instr.swap? depth with
        | none =>
            simp [hCode] at hLower
        | some lowered =>
            simp [hCode] at hLower
            rcases hLower with ⟨_hCode, hOutput⟩
            rw [hOutput]
      case declareLocal name =>
        rcases hLower with ⟨_hCode, hOutput⟩
        rw [hOutput]
      case declareLocals names =>
        rcases hLower with ⟨_hCode, hOutput⟩
        rw [hOutput]
      case initLocals names =>
        rcases hLower with ⟨_hCode, hOutput⟩
        rw [hOutput]
      case loadLocal name depth =>
        cases hCode : TypedCfg.Instr.dup? depth with
        | none =>
            simp [hCode] at hLower
        | some lowered =>
            simp [hCode] at hLower
            rcases hLower with ⟨_hCode, hOutput⟩
            rw [hOutput]
      case storeLocal name depth =>
        cases hCode : TypedCfg.Instr.storeLocalCode? depth with
        | none =>
            simp [hCode] at hLower
        | some lowered =>
            simp [hCode] at hLower
            rcases hLower with ⟨_hCode, hOutput⟩
            rw [hOutput]
      case assignLocals names =>
        cases hAssign :
            TypedCfg.Instr.lowerAssignLocalsWithShape? names shape with
        | none =>
            simp [hAssign] at hLower
        | some result =>
            cases result with
            | mk assignCode assignOutput =>
                by_cases hEq : assignOutput = typedOutput
                · simp [hAssign, hEq] at hLower
                  rcases hLower with ⟨_hCode, hOutput⟩
                  rw [hOutput]
                · simp [hAssign, hEq] at hLower
      case returnLocals names =>
        cases hReturn :
            TypedCfg.Instr.lowerReturnLocalsWithShape? names shape with
        | none =>
            simp [hReturn] at hLower
        | some returnCode =>
            simp [hReturn] at hLower
            rcases hLower with ⟨_hCode, hOutput⟩
            rw [hOutput]
      case unwind target =>
        rcases hLower with ⟨_hCode, hOutput⟩
        rw [hOutput]

end Instr

namespace InstrSemantics

def targetPopMany : Nat → List Assembly.TargetInstr
  | 0 => []
  | n + 1 => .prim .pop :: targetPopMany n

theorem sourceStepAt_pop_eq_targetRunList
    (full : Assembly.Program) (pc : Nat) (state : Assembly.EVMState) :
    Assembly.Source.stepAt full pc (.prim .pop) state =
      Assembly.Target.runList [.prim .pop] state := by
  change Assembly.Target.stepInstr (Assembly.TargetInstr.prim .pop) state =
    Assembly.Target.runList [.prim .pop] state
  unfold Assembly.Target.runList
  cases hStep :
      Assembly.Target.stepInstr (Assembly.TargetInstr.prim .pop) state with
  | error err =>
      rfl
  | ok state' =>
      rfl

theorem sourceStepAt_push_eq_targetRunList
    (full : Assembly.Program) (pc : Nat) (state : Assembly.EVMState)
    (value : Word) :
    Assembly.Source.stepAt full pc (.push value) state =
      Assembly.Target.runList [.push32 value] state := by
  change Assembly.Target.stepInstr (Assembly.TargetInstr.push32 value) state =
    Assembly.Target.runList [.push32 value] state
  unfold Assembly.Target.runList
  cases hStep :
      Assembly.Target.stepInstr (Assembly.TargetInstr.push32 value) state with
  | error err =>
      rfl
  | ok state' =>
      rfl

theorem pop_step_sourceAt {program : Program} {sites : List CallSite}
    {source : RunState} {target : Assembly.EVMState} {sourceEVM' : EVMState}
    {full : Assembly.Program} {pc : Nat}
    (hRel : PayloadRel program sites source target)
    (hStep : Assembly.PrimOp.pop.step source.evm = .ok sourceEVM') :
    ∃ target',
      Assembly.Source.stepAt full pc (.prim .pop) target = .ok target' ∧
        PayloadRel program sites (source.withEVM sourceEVM') target' := by
  rcases PayloadRel.pop_step_target hRel hStep with
    ⟨target', hRun, hRel'⟩
  refine ⟨target', ?_, hRel'⟩
  rw [sourceStepAt_pop_eq_targetRunList]
  exact hRun

theorem push_step_sourceAt {program : Program} {sites : List CallSite}
    {source : RunState} {target : Assembly.EVMState}
    {full : Assembly.Program} {pc : Nat} {value : Word} :
    let sourceEVM' :=
      source.evm.replaceStackAndIncrPC
        (source.evm.stack.push value) (pcΔ := Assembly.Instr.push32Size)
    let target' :=
      target.replaceStackAndIncrPC
        (target.stack.push value) (pcΔ := Assembly.Instr.push32Size)
    PayloadRel program sites source target →
      Assembly.Source.stepAt full pc (.push value) target = .ok target' ∧
        PayloadRel program sites (source.withEVM sourceEVM') target' := by
  intro sourceEVM' target' hRel
  constructor
  · rw [sourceStepAt_push_eq_targetRunList]
    rfl
  · exact PayloadRel.push hRel

theorem push_runWithShape?_target {program : Program} {sites : List CallSite}
    {source : RunState} {target : Assembly.EVMState}
    {shape : Shape} {value : Word}
    (hMatches : shape.matchesStack source.evm.stack = true)
    (hRel : PayloadRel program sites source target) :
    let sourceEVM' :=
      source.evm.replaceStackAndIncrPC
        (source.evm.stack.push value) (pcΔ := Assembly.Instr.push32Size)
    let target' :=
      target.replaceStackAndIncrPC
        (target.stack.push value) (pcΔ := Assembly.Instr.push32Size)
    TypedCfg.Instr.runWithShape? (.push value) shape source.evm =
        .ok (sourceEVM', .word :: shape) ∧
      Assembly.Target.runList [.push32 value] target = .ok target' ∧
      PayloadRel program sites (source.withEVM sourceEVM') target' := by
  let sourceEVM' :=
      source.evm.replaceStackAndIncrPC
        (source.evm.stack.push value) (pcΔ := Assembly.Instr.push32Size)
  have hOutputMatches :
      Shape.matchesStack (Slot.word :: shape) (value :: source.evm.stack) =
        true := by
    simp [Shape.matchesStack, Slot.matchesValue, hMatches]
  constructor
  · change
      (if Shape.matchesStack (Slot.word :: shape) sourceEVM'.stack = true then
          Except.ok (sourceEVM', Slot.word :: shape)
        else
          Except.error EvmYul.EVM.ExecutionException.InvalidInstruction) =
        Except.ok (sourceEVM', Slot.word :: shape)
    have hSourceStack : sourceEVM'.stack = value :: source.evm.stack := by
      simp [sourceEVM', EvmYul.Stack.push,
        EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC, Assembly.Instr.push32Size]
    rw [hSourceStack, hOutputMatches]
    simp
  · constructor
    · rfl
    · exact PayloadRel.push hRel

theorem push_runWithShape?_sourceAt {program : Program}
    {sites : List CallSite} {source : RunState}
    {target : Assembly.EVMState} {shape : Shape} {value : Word}
    {full : Assembly.Program} {pc : Nat}
    (hMatches : shape.matchesStack source.evm.stack = true)
    (hRel : PayloadRel program sites source target) :
    let sourceEVM' :=
      source.evm.replaceStackAndIncrPC
        (source.evm.stack.push value) (pcΔ := Assembly.Instr.push32Size)
    let target' :=
      target.replaceStackAndIncrPC
        (target.stack.push value) (pcΔ := Assembly.Instr.push32Size)
    TypedCfg.Instr.runWithShape? (.push value) shape source.evm =
        .ok (sourceEVM', .word :: shape) ∧
      Assembly.Source.stepAt full pc (.push value) target = .ok target' ∧
      PayloadRel program sites (source.withEVM sourceEVM') target' := by
  rcases push_runWithShape?_target
      (program := program) (sites := sites) (source := source)
      (target := target) (shape := shape) (value := value)
      hMatches hRel with ⟨hSourceRun, hTargetRun, hRel'⟩
  refine ⟨hSourceRun, ?_, hRel'⟩
  rw [sourceStepAt_push_eq_targetRunList]
  exact hTargetRun

theorem pop_runWithShape?_target {program : Program} {sites : List CallSite}
    {source : RunState} {target : Assembly.EVMState}
    {shape : Shape} {slot : Slot}
    (hMatches : Shape.matchesStack (slot :: shape) source.evm.stack = true)
    (hRel : PayloadRel program sites source target) :
    ∃ sourceEVM' target',
      TypedCfg.Instr.runWithShape? .pop (slot :: shape) source.evm =
          .ok (sourceEVM', shape) ∧
        Assembly.Target.runList [.prim .pop] target = .ok target' ∧
          PayloadRel program sites (source.withEVM sourceEVM') target' := by
  cases hSourceStack : source.evm.stack with
  | nil =>
      simp [Shape.matchesStack, hSourceStack] at hMatches
  | cons value rest =>
      have hRestMatches : Shape.matchesStack shape rest = true := by
        have hSplit :
            slot.matchesValue value = true ∧
              Shape.matchesStack shape rest = true := by
          simpa [Shape.matchesStack, hSourceStack] using hMatches
        exact hSplit.2
      let sourceEVM' := source.evm.replaceStackAndIncrPC rest
      have hSourceStep :
          Assembly.PrimOp.pop.step source.evm = .ok sourceEVM' := by
        simp [Assembly.PrimOp.step, Assembly.PrimOp.continuingStep?,
          Assembly.PrimStep.run, EvmYul.Stack.pop, hSourceStack,
          sourceEVM', EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC]
      rcases PayloadRel.pop_step_target hRel hSourceStep with
        ⟨target', hTargetRun, hTargetRel⟩
      refine ⟨sourceEVM', target', ?_, hTargetRun, hTargetRel⟩
      · simp [TypedCfg.Instr.runWithShape?, TypedCfg.Instr.type?,
          TypedCfg.Instr.run, Assembly.PrimOp.step,
          Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
          EvmYul.Stack.pop, hSourceStack, sourceEVM',
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC]
        change
          (if Shape.matchesStack shape rest = true then
              Except.ok
                ({ source.evm with
                    pc := source.evm.pc + EvmYul.UInt256.ofNat 1
                    stack := rest }, shape)
            else
              Except.error EvmYul.EVM.ExecutionException.InvalidInstruction) =
            Except.ok
              ({ source.evm with
                  pc := source.evm.pc + EvmYul.UInt256.ofNat 1
                  stack := rest }, shape)
        rw [hRestMatches]
        simp

theorem pop_runWithShape?_sourceAt {program : Program}
    {sites : List CallSite} {source : RunState}
    {target : Assembly.EVMState} {shape : Shape} {slot : Slot}
    {full : Assembly.Program} {pc : Nat}
    (hMatches : Shape.matchesStack (slot :: shape) source.evm.stack = true)
    (hRel : PayloadRel program sites source target) :
    ∃ sourceEVM' target',
      TypedCfg.Instr.runWithShape? .pop (slot :: shape) source.evm =
          .ok (sourceEVM', shape) ∧
        Assembly.Source.stepAt full pc (.prim .pop) target = .ok target' ∧
          PayloadRel program sites (source.withEVM sourceEVM') target' := by
  rcases pop_runWithShape?_target
      (program := program) (sites := sites) (source := source)
      (target := target) (shape := shape) (slot := slot)
      hMatches hRel with
    ⟨sourceEVM', target', hSourceRun, hTargetRun, hRel'⟩
  refine ⟨sourceEVM', target', hSourceRun, ?_, hRel'⟩
  rw [sourceStepAt_pop_eq_targetRunList]
  exact hTargetRun

theorem runPopMany_target {program : Program} {sites : List CallSite}
    {source : RunState} {target : Assembly.EVMState}
    {sourceEVM' : EVMState} {n : Nat}
    (hRel : PayloadRel program sites source target)
    (hRun : TypedCfg.Instr.runPopMany n source.evm = .ok sourceEVM') :
    ∃ target',
      Assembly.Target.runList (targetPopMany n) target = .ok target' ∧
        PayloadRel program sites (source.withEVM sourceEVM') target' := by
  induction n generalizing source target sourceEVM' with
  | zero =>
      simp [TypedCfg.Instr.runPopMany] at hRun
      cases hRun
      refine ⟨target, rfl, ?_⟩
      constructor
      · simpa [RunState.withEVM] using hRel.shared_eq
      · simpa [RunState.withEVM] using hRel.stack_eq
  | succ n ih =>
      simp [TypedCfg.Instr.runPopMany] at hRun
      cases hStep : Assembly.PrimOp.pop.step source.evm with
      | error err =>
          simp [hStep] at hRun
          change (Except.error err : Except EVMException EVMState) =
            Except.ok sourceEVM' at hRun
          cases hRun
      | ok mid =>
          simp [hStep] at hRun
          change TypedCfg.Instr.runPopMany n mid = .ok sourceEVM' at hRun
          rcases PayloadRel.pop_step_target hRel hStep with
            ⟨targetMid, hTargetHead, hRelMid⟩
          rcases ih hRelMid hRun with
            ⟨targetFinal, hTargetTail, hRelFinal⟩
          have hTargetHeadStep :
              Assembly.Target.stepInstr (.prim .pop) target =
                .ok targetMid := by
            cases hStepTarget :
                Assembly.Target.stepInstr (.prim .pop) target with
            | error err =>
                simp [Assembly.Target.runList, hStepTarget] at hTargetHead
                change (Except.error err : Except EVMException EVMState) =
                  Except.ok targetMid at hTargetHead
                cases hTargetHead
            | ok stepped =>
                simp [Assembly.Target.runList, hStepTarget] at hTargetHead
                cases hTargetHead
                rfl
          refine ⟨targetFinal, ?_, ?_⟩
          · simpa [targetPopMany, Assembly.Target.runList, hTargetHeadStep]
              using hTargetTail
          · simpa [RunState.withEVM] using hRelFinal

theorem popMany_emitFrom_targetPopMany
    (full : Assembly.Program) (n pc : Nat) :
    ∃ located,
      Assembly.emitFrom? full (TypedCfg.Instr.popMany n) pc = some located ∧
        located.map Assembly.LocatedTarget.instr = targetPopMany n := by
  induction n generalizing pc with
  | zero =>
      refine ⟨[], ?_, ?_⟩
      · simp [TypedCfg.Instr.popMany, Assembly.emitFrom?]
      · simp [targetPopMany]
  | succ n ih =>
      rcases ih (pc + Assembly.Instr.byteSize (.prim .pop)) with
        ⟨tail, hTailEmit, hTailMap⟩
      refine
        ⟨{ pc := pc, instr := Assembly.TargetInstr.prim .pop } :: tail,
          ?_, ?_⟩
      · simp [TypedCfg.Instr.popMany, Assembly.emitFrom?, Assembly.emitInstr?,
          hTailEmit]
      · simp [targetPopMany, hTailMap]

theorem popMany_emitFrom_targetPopMany_of_some
    {full : Assembly.Program} {n pc : Nat}
    {located : List Assembly.LocatedTarget}
    (hEmit :
      Assembly.emitFrom? full (TypedCfg.Instr.popMany n) pc = some located) :
    located.map Assembly.LocatedTarget.instr = targetPopMany n := by
  induction n generalizing pc located with
  | zero =>
      simp [TypedCfg.Instr.popMany, Assembly.emitFrom?] at hEmit
      cases hEmit
      simp [targetPopMany]
  | succ n ih =>
      simp [TypedCfg.Instr.popMany, Assembly.emitFrom?, Assembly.emitInstr?] at hEmit
      cases hTail :
          Assembly.emitFrom? full (TypedCfg.Instr.popMany n)
            (pc + Assembly.Instr.byteSize (.prim .pop)) with
      | none =>
          simp [hTail] at hEmit
      | some tail =>
          simp [hTail] at hEmit
          cases hEmit
          simp [targetPopMany, ih hTail]

theorem runPopMany_emitted_target {program : Program} {sites : List CallSite}
    {source : RunState} {target : Assembly.EVMState}
    {sourceEVM' : EVMState} {n : Nat}
    {full : Assembly.Program} {pc : Nat}
    {located : List Assembly.LocatedTarget}
    (hRel : PayloadRel program sites source target)
    (hRun : TypedCfg.Instr.runPopMany n source.evm = .ok sourceEVM')
    (hEmit :
      Assembly.emitFrom? full (TypedCfg.Instr.popMany n) pc = some located) :
    ∃ target',
      Assembly.Target.runList (located.map Assembly.LocatedTarget.instr)
          target = .ok target' ∧
        PayloadRel program sites (source.withEVM sourceEVM') target' := by
  have hMap := popMany_emitFrom_targetPopMany_of_some hEmit
  rcases runPopMany_target hRel hRun with ⟨target', hTarget, hRel'⟩
  refine ⟨target', ?_, hRel'⟩
  simpa [hMap] using hTarget

theorem runPopMany_stack_drop {n : Nat} {state state' : EVMState}
    (hRun : TypedCfg.Instr.runPopMany n state = .ok state') :
    state'.stack = state.stack.drop n := by
  induction n generalizing state state' with
  | zero =>
      simp [TypedCfg.Instr.runPopMany] at hRun
      cases hRun
      simp
  | succ n ih =>
      simp [TypedCfg.Instr.runPopMany] at hRun
      cases hStep : Assembly.PrimOp.pop.step state with
      | error err =>
          simp [hStep] at hRun
          change (Except.error err : Except EVMException EVMState) =
            Except.ok state' at hRun
          cases hRun
      | ok mid =>
          simp [hStep] at hRun
          change TypedCfg.Instr.runPopMany n mid = .ok state' at hRun
          have hMidStack : mid.stack = state.stack.drop 1 := by
            cases hStack : state.stack with
            | nil =>
                simp [Assembly.PrimOp.step, Assembly.PrimOp.continuingStep?,
                  Assembly.PrimStep.run, EvmYul.Stack.pop, hStack] at hStep
            | cons value rest =>
                simp [Assembly.PrimOp.step, Assembly.PrimOp.continuingStep?,
                  Assembly.PrimStep.run, EvmYul.Stack.pop, hStack,
                  EvmYul.EVM.State.replaceStackAndIncrPC,
                  EvmYul.EVM.State.incrPC] at hStep
                cases hStep
                simp [hStack]
          rw [ih hRun, hMidStack]
          simp [List.drop_drop, Nat.add_comm, Nat.add_left_comm,
            Nat.add_assoc]

theorem runPopMany_success_of_le (n : Nat) (state : EVMState)
    (hLe : n ≤ state.stack.length) :
    ∃ state', TypedCfg.Instr.runPopMany n state = .ok state' := by
  induction n generalizing state with
  | zero =>
      exact ⟨state, rfl⟩
  | succ n ih =>
      cases hStack : state.stack with
      | nil =>
          simp [hStack] at hLe
      | cons value rest =>
          let mid := state.replaceStackAndIncrPC rest
          have hStep :
              Assembly.PrimOp.pop.step state = .ok mid := by
            simp [Assembly.PrimOp.step, Assembly.PrimOp.continuingStep?,
              Assembly.PrimStep.run, EvmYul.Stack.pop, hStack, mid,
              EvmYul.EVM.State.replaceStackAndIncrPC,
              EvmYul.EVM.State.incrPC]
          have hTailLe : n ≤ mid.stack.length := by
            simp [mid, EvmYul.EVM.State.replaceStackAndIncrPC,
              EvmYul.EVM.State.incrPC]
            have hLeRest : n + 1 ≤ (value :: rest).length := by
              simpa [hStack] using hLe
            exact Nat.succ_le_succ_iff.mp hLeRest
          rcases ih mid hTailLe with ⟨state', hRunTail⟩
          refine ⟨state', ?_⟩
          simp [TypedCfg.Instr.runPopMany, hStep]
          change TypedCfg.Instr.runPopMany n mid = .ok state'
          exact hRunTail

theorem unwind_runWithShape?_target {program : Program} {sites : List CallSite}
    {source : RunState} {target : Assembly.EVMState}
    {shape targetShape : Shape}
    (hMatches : Shape.matchesStack shape source.evm.stack = true)
    (hUnwind : Shape.unwindTo targetShape shape = some targetShape)
    (hRel : PayloadRel program sites source target) :
    ∃ sourceEVM' target',
      TypedCfg.Instr.runWithShape? (.unwind targetShape) shape source.evm =
          .ok (sourceEVM', targetShape) ∧
        Assembly.Target.runList
            (targetPopMany (shape.length - targetShape.length)) target =
          .ok target' ∧
        PayloadRel program sites (source.withEVM sourceEVM') target' := by
  have hLen := Shape.matchesStack_length hMatches
  have hLe : shape.length - targetShape.length ≤ source.evm.stack.length := by
    rw [← hLen]
    exact Nat.sub_le shape.length targetShape.length
  rcases runPopMany_success_of_le
      (shape.length - targetShape.length) source.evm hLe with
    ⟨sourceEVM', hRunPop⟩
  rcases runPopMany_target hRel hRunPop with
    ⟨target', hTargetRun, hTargetRel⟩
  refine ⟨sourceEVM', target', ?_, hTargetRun, hTargetRel⟩
  have hStackDrop := runPopMany_stack_drop hRunPop
  have hTargetMatches :=
    Shape.matchesStack_drop_of_unwindTo hUnwind hMatches
  simp [TypedCfg.Instr.runWithShape?, TypedCfg.Instr.type?, hUnwind,
    hRunPop]
  change
    (if Shape.matchesStack targetShape sourceEVM'.stack = true then
        Except.ok (sourceEVM', targetShape)
      else
        Except.error EvmYul.EVM.ExecutionException.InvalidInstruction) =
      Except.ok (sourceEVM', targetShape)
  rw [hStackDrop]
  rw [hTargetMatches]
  simp

end InstrSemantics

namespace Block

theorem lowerBodyWithShape?_type? {body : List TypedCfg.Instr}
    {shape : Shape} {code : Assembly.Program} {output : Shape}
    (hLower : TypedCfg.Block.lowerBodyWithShape? body shape =
      some (code, output)) :
    TypedCfg.Block.bodyType? body shape = some output := by
  induction body generalizing shape code output with
  | nil =>
      simp [TypedCfg.Block.lowerBodyWithShape?] at hLower
      rcases hLower with ⟨_hCode, hOutput⟩
      rw [hOutput]
      simp [TypedCfg.Block.bodyType?]
  | cons instr rest ih =>
      unfold TypedCfg.Block.lowerBodyWithShape? at hLower
      cases hHead : instr.lowerWithShape? shape with
      | none =>
          simp [hHead] at hLower
      | some headResult =>
          cases headResult with
          | mk headCode headShape =>
              cases hTail :
                  TypedCfg.Block.lowerBodyWithShape? rest headShape with
              | none =>
                  simp [hHead, hTail] at hLower
              | some tailResult =>
                  cases tailResult with
                  | mk tailCode tailShape =>
                      simp [hHead, hTail] at hLower
                      rcases hLower with ⟨_hCode, hOutput⟩
                      rw [← hOutput]
                      simp [TypedCfg.Block.bodyType?,
                        Instr.lowerWithShape?_type? hHead, ih hTail]

end Block

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
