import EvmCompiler.Structured.Compiler
import EvmCompiler.Assembly.GasAware

namespace EvmCompiler
namespace Structured

def SameData (assemblyState sourceState : EVMState) : Prop :=
  eraseControl assemblyState = eraseControl sourceState

structure RelAt (pc : Word) (assemblyState sourceState : EVMState) : Prop where
  pc_eq : assemblyState.pc = pc
  sameData : SameData assemblyState sourceState

def ARun (program : Assembly.Program) (state : EVMState)
    (post : EVMState → Prop) : Prop :=
  ∃ fuel final,
    Assembly.Source.runN program fuel state = .ok final ∧
      post final

def PCFits (program : Assembly.Program) : Prop :=
  (Assembly.Program.pcAfter program).toNat = Assembly.Program.byteLength program

namespace AssemblySource

theorem runN_append_ok {program : Assembly.Program}
    {firstFuel secondFuel : Nat} {state mid final : EVMState}
    (hFirst : Assembly.Source.runN program firstFuel state = .ok mid)
    (hSecond : Assembly.Source.runN program secondFuel mid = .ok final) :
    Assembly.Source.runN program (firstFuel + secondFuel) state = .ok final := by
  induction firstFuel generalizing state with
  | zero =>
      simp [Assembly.Source.runN] at hFirst
      cases hFirst
      simpa [Assembly.Source.runN] using hSecond
  | succ firstFuel ih =>
      unfold Assembly.Source.runN at hFirst
      cases hStep : Assembly.Source.step program state with
      | error err =>
          rw [hStep] at hFirst
          cases hFirst
      | ok state' =>
          rw [hStep] at hFirst
          change
            Assembly.Source.runN program firstFuel state' = Except.ok mid at hFirst
          have hFuel :
              firstFuel + 1 + secondFuel = firstFuel + secondFuel + 1 := by
            rw [Nat.add_assoc]
            rw [Nat.add_comm 1 secondFuel]
            rw [← Nat.add_assoc]
          rw [hFuel]
          unfold Assembly.Source.runN
          rw [hStep]
          exact ih hFirst

end AssemblySource

namespace ARun

theorem pure {program : Assembly.Program} {state : EVMState}
    {post : EVMState → Prop}
    (hPost : post state) :
    ARun program state post := by
  exact ⟨0, state, by simp [Assembly.Source.runN], hPost⟩

theorem bind {program : Assembly.Program} {state : EVMState}
    {middle post : EVMState → Prop}
    (hRun : ARun program state middle)
    (hNext : ∀ state', middle state' → ARun program state' post) :
    ARun program state post := by
  rcases hRun with ⟨firstFuel, mid, hFirst, hMiddle⟩
  rcases hNext mid hMiddle with ⟨secondFuel, final, hSecond, hPost⟩
  exact
    ⟨firstFuel + secondFuel, final,
      AssemblySource.runN_append_ok hFirst hSecond, hPost⟩

end ARun

namespace RelAt

theorem entry {state : EVMState}
    (hPc : state.pc = Assembly.Program.pcAfter ([] : Assembly.Program)) :
    RelAt (Assembly.Program.pcAfter ([] : Assembly.Program)) state state := by
  exact ⟨hPc, rfl⟩

end RelAt

namespace BasicInstr

theorem source_stepAt_projected_of_eraseControl_eq {instr : BasicInstr}
    {program : Assembly.Program} {pc : Nat}
    {source target source' : EVMState}
    (hEq : eraseControl target = eraseControl source)
    (hStep : instr.step source = .ok source') :
    ∃ target',
      Assembly.Source.stepAt program pc instr.toAssembly target = .ok target' ∧
        eraseControl target' = eraseControl source' := by
  cases instr with
  | push value =>
      exact
        BasicInstr.step_projected_of_eraseControl_eq
          (instr := BasicInstr.push value) hEq hStep
  | op op =>
      exact
        BasicInstr.step_projected_of_eraseControl_eq
          (instr := BasicInstr.op op) hEq hStep

theorem source_step_ctx_projected_of_relAt {instr : BasicInstr}
    {pre post : Assembly.Program}
    {source target source' : EVMState}
    (hFit : PCFits pre)
    (hRel : RelAt (Assembly.Program.pcAfter pre) target source)
    (hStep : instr.step source = .ok source') :
    ∃ target',
      Assembly.Source.step (pre ++ instr.toAssembly :: post) target =
          .ok target' ∧
        eraseControl target' = eraseControl source' := by
  unfold Assembly.Source.step
  have hAt :
      Assembly.Program.instrAtPc (pre ++ instr.toAssembly :: post)
          target.pc.toNat =
        some (Assembly.Program.byteLength pre, instr.toAssembly) := by
    unfold Assembly.Program.instrAtPc
    rw [hRel.pc_eq, hFit]
    simpa using
      Assembly.Program.instrAtPcFrom_append_boundary_cons
        pre post instr.toAssembly 0
  rw [hAt]
  exact
    source_stepAt_projected_of_eraseControl_eq
      (instr := instr) (program := pre ++ instr.toAssembly :: post)
      (pc := Assembly.Program.byteLength pre) hRel.sameData hStep

end BasicInstr

namespace BasicInstr

theorem source_step_projected_at_prefix {instr : BasicInstr}
    {pre post : Assembly.Program}
    {source target source' : EVMState}
    (hPc : target.pc.toNat = Assembly.Program.byteLength pre)
    (hEq : eraseControl target = eraseControl source)
    (hStep : instr.step source = .ok source') :
    ∃ target',
      Assembly.Source.step (pre ++ instr.toAssembly :: post) target =
        .ok target' ∧
        eraseControl target' = eraseControl source' := by
  unfold Assembly.Source.step Assembly.Program.instrAtPc
  rw [hPc]
  have hAt :
      Assembly.Program.instrAtPcFrom (pre ++ instr.toAssembly :: post) 0
          (Assembly.Program.byteLength pre) =
        some (Assembly.Program.byteLength pre, instr.toAssembly) := by
    simpa using
      Assembly.Program.instrAtPcFrom_append_boundary_cons
        pre post instr.toAssembly 0
  rw [hAt]
  exact
    source_stepAt_projected_of_eraseControl_eq
      (instr := instr) (program := pre ++ instr.toAssembly :: post)
      (pc := Assembly.Program.byteLength pre) hEq hStep

end BasicInstr

/--
Concrete witness that a compiled structured program has replayed a structured
source run through the labeled-assembly semantics.

The long-term proof target is to derive this certificate by induction over the
structured evaluator.  Keeping it as a named proposition now makes the public
top theorem honest about exactly what the structured-control layer must supply
to compose with the existing assembler/bytecode bridge.
-/
structure AssemblyReplay
    (program : Program) (fuel : Nat) (initial sourceFinal : EVMState) where
  assemblyFuel : Nat
  assemblyFinal : EVMState
  sourceRun :
    Program.run fuel program initial = .ok sourceFinal
  assemblyRun :
    Assembly.Source.runN program.compile assemblyFuel initial = .ok assemblyFinal
  projected :
    eraseControl assemblyFinal = eraseControl sourceFinal

namespace AssemblyReplay

theorem exists_assembly_run {program : Program} {fuel : Nat}
    {initial sourceFinal : EVMState}
    (replay : AssemblyReplay program fuel initial sourceFinal) :
    ∃ assemblyFuel assemblyFinal,
      Assembly.Source.runN program.compile assemblyFuel initial = .ok assemblyFinal ∧
        eraseControl assemblyFinal = eraseControl sourceFinal := by
  exact
    ⟨replay.assemblyFuel, replay.assemblyFinal,
      replay.assemblyRun, replay.projected⟩

end AssemblyReplay

/--
Structured-to-labeled preservation theorem, stated at the reusable boundary.

This theorem does not yet derive the replay witness; it checks and packages it.
The witness is deliberately an explicit certificate value rather than a hidden
trusted fact, so the next hardening step can replace the caller-provided
certificate with a recursive proof over `Program.run`.
-/
theorem compile_preserves_from_replay {program : Program} {fuel : Nat}
    {initial sourceFinal : EVMState}
    (replay : AssemblyReplay program fuel initial sourceFinal) :
    Program.run fuel program initial = .ok sourceFinal ∧
      ∃ assemblyFuel assemblyFinal,
        Assembly.Source.runN program.compile assemblyFuel initial = .ok assemblyFinal ∧
          eraseControl assemblyFinal = eraseControl sourceFinal := by
  exact ⟨replay.sourceRun, replay.exists_assembly_run⟩

/--
Whole-program theorem composing the structured compiler with the existing
accepted labeled-assembly-to-bytecode theorem.

The final observable comparison erases both gas/execution counters and the
control PC introduced by lowering structured control into labels and jumps.
-/
theorem compile_whole_program_sound {program : Program}
    {target : Assembly.TargetProgram} {fuel : Nat}
    {initial structuredFinal : EVMState}
    (hCompile : Assembly.compile? program.compile = some target)
    (hRuntime : Assembly.RuntimeAssumptions program.compile target initial)
    (replay : AssemblyReplay program fuel initial structuredFinal) :
    Assembly.Accepted program.compile ∧
      Assembly.Bytecode.compileBytes? program.compile =
        some (Assembly.Bytecode.encodeTarget target) ∧
        Assembly.Bytecode.EncodingCorrect target (Assembly.Bytecode.encodeTarget target) ∧
          target.GasOpcodeAbsent ∧
            target.ExternalInteractionAbsent ∧
              Assembly.GasOracleAssumption program.compile initial ∧
                Assembly.OutsideWorldOracleAssumption program.compile initial ∧
                  Assembly.OutOfGasPolicyAssumption program.compile initial ∧
                    Assembly.CurrentContractProjectionAssumption program.compile initial ∧
                      ∃ assemblyFinal targetFinal,
                        Assembly.Preservation.BlockTrace program.compile target
                          replay.assemblyFuel initial targetFinal ∧
                          Assembly.eraseGas targetFinal =
                            Assembly.eraseGas assemblyFinal ∧
                          eraseControl assemblyFinal = eraseControl structuredFinal := by
  obtain
    ⟨hAccepted, hBytes, hEncoding, hNoGas, hNoExternal,
      hGasOracle, hOutsideWorld, hOutOfGas, hProjection,
      targetFinal, hTrace, hErase⟩ :=
    Assembly.compile_whole_program_sound hCompile hRuntime replay.assemblyRun
  exact
    ⟨hAccepted, hBytes, hEncoding, hNoGas, hNoExternal,
      hGasOracle, hOutsideWorld, hOutOfGas, hProjection,
      replay.assemblyFinal, targetFinal, hTrace, hErase, replay.projected⟩

/--
Gas-aware composition theorem for EVMYulLean `X`.

This is the structured-control analogue of
`Assembly.GasAware.compile_whole_program_X_bridge`: it adds only the structured
replay certificate on top of the existing bytecode/runtime/gas preconditions.
-/
theorem compile_whole_program_X_bridge {program : Program}
    {target : Assembly.TargetProgram} {fuel : Nat}
    {initial structuredFinal : EVMState}
    (hCompile : Assembly.compile? program.compile = some target)
    (hRuntime : Assembly.RuntimeAssumptions program.compile target initial)
    (replay : AssemblyReplay program fuel initial structuredFinal)
    (hPreconditions :
      Assembly.GasAware.XPreconditionAssumptions target initial replay.assemblyFinal) :
    Assembly.GasAware.XBridgeCertificate program.compile target
      replay.assemblyFuel initial replay.assemblyFinal ∧
      eraseControl replay.assemblyFinal = eraseControl structuredFinal := by
  exact
    ⟨Assembly.GasAware.compile_whole_program_X_bridge
        hCompile hRuntime replay.assemblyRun hPreconditions,
      replay.projected⟩

end Structured
end EvmCompiler
