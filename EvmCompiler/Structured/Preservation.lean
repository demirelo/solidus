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

theorem mono {program : Assembly.Program} {state : EVMState}
    {post₁ post₂ : EVMState → Prop}
    (hRun : ARun program state post₁)
    (hPost : ∀ final, post₁ final → post₂ final) :
    ARun program state post₂ := by
  rcases hRun with ⟨fuel, final, hRun, hFinal⟩
  exact ⟨fuel, final, hRun, hPost final hFinal⟩

end ARun

namespace RelAt

theorem entry {state : EVMState}
    (hPc : state.pc = Assembly.Program.pcAfter ([] : Assembly.Program)) :
    RelAt (Assembly.Program.pcAfter ([] : Assembly.Program)) state state := by
  exact ⟨hPc, rfl⟩

theorem cast_pc {oldPc newPc : Word} {target source : EVMState}
    (hEq : oldPc = newPc)
    (hRel : RelAt oldPc target source) :
    RelAt newPc target source := by
  cases hEq
  exact hRel

end RelAt

namespace AssemblyProgram

def PCFitsFrom : Assembly.Program → Assembly.Program → Prop
  | pre, [] => PCFits pre
  | pre, instr :: rest =>
      PCFits pre ∧ PCFitsFrom (pre ++ [instr]) rest

theorem PCFitsFrom.start {pre code : Assembly.Program}
    (hFits : PCFitsFrom pre code) :
    PCFits pre := by
  cases code with
  | nil =>
      simpa [PCFitsFrom] using hFits
  | cons instr rest =>
      exact hFits.1

theorem PCFitsFrom.end {pre code : Assembly.Program}
    (hFits : PCFitsFrom pre code) :
    PCFits (pre ++ code) := by
  induction code generalizing pre with
  | nil =>
      simpa [PCFitsFrom] using hFits
  | cons instr rest ih =>
      simpa [PCFitsFrom, List.append_assoc] using ih hFits.2

theorem PCFitsFrom.left {pre first second : Assembly.Program}
    (hFits : PCFitsFrom pre (first ++ second)) :
    PCFitsFrom pre first := by
  induction first generalizing pre with
  | nil =>
      exact PCFitsFrom.start hFits
  | cons instr rest ih =>
      rcases hFits with ⟨hHere, hRest⟩
      exact ⟨hHere, ih hRest⟩

theorem PCFitsFrom.right {pre first second : Assembly.Program}
    (hFits : PCFitsFrom pre (first ++ second)) :
    PCFitsFrom (pre ++ first) second := by
  induction first generalizing pre with
  | nil =>
      simpa using hFits
  | cons instr rest ih =>
      rcases hFits with ⟨_hHere, hRest⟩
      simpa [List.append_assoc] using ih hRest

end AssemblyProgram

namespace BasicInstr

theorem execBinOp_pc (f : EvmYul.Primop.Binary)
    {state final : EVMState}
    (hStep : EvmYul.EVM.execBinOp f state = .ok final) :
    final.pc = state.pc + EvmYul.UInt256.ofNat 1 := by
  unfold EvmYul.EVM.execBinOp at hStep
  cases hPop : state.stack.pop2 with
  | none =>
      rw [hPop] at hStep
      cases hStep
  | some popped =>
      rcases popped with ⟨rest, a, b⟩
      rw [hPop] at hStep
      simp at hStep
      cases hStep
      simp [EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]

theorem execUnOp_pc (f : EvmYul.Primop.Unary)
    {state final : EVMState}
    (hStep : EvmYul.EVM.execUnOp f state = .ok final) :
    final.pc = state.pc + EvmYul.UInt256.ofNat 1 := by
  unfold EvmYul.EVM.execUnOp at hStep
  cases hPop : state.stack.pop with
  | none =>
      rw [hPop] at hStep
      cases hStep
  | some popped =>
      rcases popped with ⟨rest, a⟩
      rw [hPop] at hStep
      simp at hStep
      cases hStep
      simp [EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]

theorem execTriOp_pc (f : EvmYul.Primop.Ternary)
    {state final : EVMState}
    (hStep : EvmYul.EVM.execTriOp f state = .ok final) :
    final.pc = state.pc + EvmYul.UInt256.ofNat 1 := by
  unfold EvmYul.EVM.execTriOp at hStep
  cases hPop : state.stack.pop3 with
  | none =>
      rw [hPop] at hStep
      cases hStep
  | some popped =>
      rcases popped with ⟨rest, a, b, c⟩
      rw [hPop] at hStep
      simp at hStep
      cases hStep
      simp [EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]

theorem executionEnvOp_pc
    (f : EvmYul.ExecutionEnv EvmYul.OperationType.EVM → Word)
    {state final : EVMState}
    (hStep : EvmYul.EVM.executionEnvOp f state = .ok final) :
    final.pc = state.pc + EvmYul.UInt256.ofNat 1 := by
  unfold EvmYul.EVM.executionEnvOp at hStep
  cases hStep
  simp [EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC]

theorem unaryExecutionEnvOp_pc
    (f : EvmYul.ExecutionEnv EvmYul.OperationType.EVM → Word → Word)
    {state final : EVMState}
    (hStep : EvmYul.EVM.unaryExecutionEnvOp f state = .ok final) :
    final.pc = state.pc + EvmYul.UInt256.ofNat 1 := by
  unfold EvmYul.EVM.unaryExecutionEnvOp at hStep
  cases hPop : state.stack.pop with
  | none =>
      rw [hPop] at hStep
      cases hStep
  | some popped =>
      rcases popped with ⟨rest, a⟩
      rw [hPop] at hStep
      simp at hStep
      cases hStep
      simp [EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]

theorem machineStateOp_pc (f : EvmYul.MachineState → Word)
    {state final : EVMState}
    (hStep : EvmYul.EVM.machineStateOp f state = .ok final) :
    final.pc = state.pc + EvmYul.UInt256.ofNat 1 := by
  unfold EvmYul.EVM.machineStateOp at hStep
  cases hStep
  simp [EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC]

theorem binaryMachineStateOp_pc
    (f : EvmYul.MachineState → Word → Word → EvmYul.MachineState)
    {state final : EVMState}
    (hStep : EvmYul.EVM.binaryMachineStateOp f state = .ok final) :
    final.pc = state.pc + EvmYul.UInt256.ofNat 1 := by
  unfold EvmYul.EVM.binaryMachineStateOp at hStep
  cases hPop : state.stack.pop2 with
  | none =>
      rw [hPop] at hStep
      cases hStep
  | some popped =>
      rcases popped with ⟨rest, a, b⟩
      rw [hPop] at hStep
      simp at hStep
      cases hStep
      simp [EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]

theorem binaryMachineStateOp'_pc
    (f : EvmYul.MachineState → Word → Word → Word × EvmYul.MachineState)
    {state final : EVMState}
    (hStep : EvmYul.EVM.binaryMachineStateOp' f state = .ok final) :
    final.pc = state.pc + EvmYul.UInt256.ofNat 1 := by
  unfold EvmYul.EVM.binaryMachineStateOp' at hStep
  cases hPop : state.stack.pop2 with
  | none =>
      rw [hPop] at hStep
      cases hStep
  | some popped =>
      rcases popped with ⟨rest, a, b⟩
      rw [hPop] at hStep
      simp at hStep
      cases hStep
      simp [EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]

theorem ternaryMachineStateOp_pc
    (f : EvmYul.MachineState → Word → Word → Word → EvmYul.MachineState)
    {state final : EVMState}
    (hStep : EvmYul.EVM.ternaryMachineStateOp f state = .ok final) :
    final.pc = state.pc + EvmYul.UInt256.ofNat 1 := by
  unfold EvmYul.EVM.ternaryMachineStateOp at hStep
  cases hPop : state.stack.pop3 with
  | none =>
      rw [hPop] at hStep
      cases hStep
  | some popped =>
      rcases popped with ⟨rest, a, b, c⟩
      rw [hPop] at hStep
      simp at hStep
      cases hStep
      simp [EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]

theorem stateOp_pc
    (f : EvmYul.State EvmYul.OperationType.EVM → Word)
    {state final : EVMState}
    (hStep : EvmYul.EVM.stateOp f state = .ok final) :
    final.pc = state.pc + EvmYul.UInt256.ofNat 1 := by
  unfold EvmYul.EVM.stateOp at hStep
  cases hStep
  simp [EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC]

theorem unaryStateOp_pc
    (f : EvmYul.State EvmYul.OperationType.EVM → Word →
      EvmYul.State EvmYul.OperationType.EVM × Word)
    {state final : EVMState}
    (hStep : EvmYul.EVM.unaryStateOp f state = .ok final) :
    final.pc = state.pc + EvmYul.UInt256.ofNat 1 := by
  unfold EvmYul.EVM.unaryStateOp at hStep
  cases hPop : state.stack.pop with
  | none =>
      rw [hPop] at hStep
      cases hStep
  | some popped =>
      rcases popped with ⟨rest, a⟩
      rw [hPop] at hStep
      simp at hStep
      cases hStep
      simp [EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]

theorem binaryStateOp_pc
    (f : EvmYul.State EvmYul.OperationType.EVM → Word → Word →
      EvmYul.State EvmYul.OperationType.EVM)
    {state final : EVMState}
    (hStep : EvmYul.EVM.binaryStateOp f state = .ok final) :
    final.pc = state.pc + EvmYul.UInt256.ofNat 1 := by
  unfold EvmYul.EVM.binaryStateOp at hStep
  cases hPop : state.stack.pop2 with
  | none =>
      rw [hPop] at hStep
      cases hStep
  | some popped =>
      rcases popped with ⟨rest, a, b⟩
      rw [hPop] at hStep
      simp at hStep
      cases hStep
      simp [EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]

theorem ternaryCopyOp_pc
    (f : EvmYul.SharedState EvmYul.OperationType.EVM → Word → Word →
      Word → EvmYul.SharedState EvmYul.OperationType.EVM)
    {state final : EVMState}
    (hStep : EvmYul.EVM.ternaryCopyOp f state = .ok final) :
    final.pc = state.pc + EvmYul.UInt256.ofNat 1 := by
  unfold EvmYul.EVM.ternaryCopyOp at hStep
  cases hPop : state.stack.pop3 with
  | none =>
      rw [hPop] at hStep
      cases hStep
  | some popped =>
      rcases popped with ⟨rest, a, b, c⟩
      rw [hPop] at hStep
      simp at hStep
      cases hStep
      simp [EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]

theorem quaternaryCopyOp_pc
    (f : EvmYul.SharedState EvmYul.OperationType.EVM → Word → Word →
      Word → Word → EvmYul.SharedState EvmYul.OperationType.EVM)
    {state final : EVMState}
    (hStep : EvmYul.EVM.quaternaryCopyOp f state = .ok final) :
    final.pc = state.pc + EvmYul.UInt256.ofNat 1 := by
  unfold EvmYul.EVM.quaternaryCopyOp at hStep
  cases hPop : state.stack.pop4 with
  | none =>
      rw [hPop] at hStep
      cases hStep
  | some popped =>
      rcases popped with ⟨rest, a, b, c, d⟩
      rw [hPop] at hStep
      simp at hStep
      cases hStep
      simp [EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]

theorem primStep_run_pc (step : Assembly.PrimStep)
    {state final : EVMState}
    (hStep : step.run state = .ok final) :
    final.pc = state.pc + EvmYul.UInt256.ofNat 1 := by
  cases step with
  | bin f =>
      exact execBinOp_pc f hStep
  | un f =>
      exact execUnOp_pc f hStep
  | tri f =>
      exact execTriOp_pc f hStep
  | executionEnv f =>
      exact executionEnvOp_pc f hStep
  | unaryExecutionEnv f =>
      exact unaryExecutionEnvOp_pc f hStep
  | machineState f =>
      exact machineStateOp_pc f hStep
  | binaryMachineState f =>
      exact binaryMachineStateOp_pc f hStep
  | binaryMachineStateWithResult f =>
      exact binaryMachineStateOp'_pc f hStep
  | ternaryMachineState f =>
      exact ternaryMachineStateOp_pc f hStep
  | state f =>
      exact stateOp_pc f hStep
  | unaryState f =>
      exact unaryStateOp_pc f hStep
  | binaryState f =>
      exact binaryStateOp_pc f hStep
  | ternaryCopy f =>
      exact ternaryCopyOp_pc f hStep
  | quaternaryCopy f =>
      exact quaternaryCopyOp_pc f hStep
  | pop =>
      unfold Assembly.PrimStep.run at hStep
      cases hPop : state.stack.pop with
      | none =>
          rw [hPop] at hStep
          cases hStep
      | some popped =>
          rcases popped with ⟨rest, a⟩
          rw [hPop] at hStep
          cases hStep
          simp [EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
  | mload =>
      unfold Assembly.PrimStep.run at hStep
      cases hPop : state.stack.pop with
      | none =>
          rw [hPop] at hStep
          cases hStep
      | some popped =>
          rcases popped with ⟨rest, a⟩
          rw [hPop] at hStep
          simp at hStep
          cases hStep
          simp [EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
  | returndatacopy =>
      unfold Assembly.PrimStep.run at hStep
      cases hPop : state.stack.pop3 with
      | none =>
          rw [hPop] at hStep
          cases hStep
      | some popped =>
          rcases popped with ⟨rest, a, b, c⟩
          rw [hPop] at hStep
          simp at hStep
          cases hStep
          simp [EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
  | dup n =>
      unfold Assembly.PrimStep.run EvmYul.dup at hStep
      by_cases hLen : n ≤ state.stack.length
      · simp [hLen] at hStep
        cases hStep
        simp [EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC]
      · simp [hLen] at hStep
  | swap n =>
      unfold Assembly.PrimStep.run EvmYul.swap at hStep
      by_cases hLen : n + 1 ≤ state.stack.length
      · simp [hLen] at hStep
        cases hStep
        simp [EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC]
      · simp [hLen] at hStep
  | log0 =>
      unfold Assembly.PrimStep.run at hStep
      cases hPop : state.stack.pop2 with
      | none =>
          rw [hPop] at hStep
          cases hStep
      | some popped =>
          rcases popped with ⟨rest, a, b⟩
          rw [hPop] at hStep
          simp at hStep
          cases hStep
          simp [EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
  | log1 =>
      unfold Assembly.PrimStep.run at hStep
      cases hPop : state.stack.pop3 with
      | none =>
          rw [hPop] at hStep
          cases hStep
      | some popped =>
          rcases popped with ⟨rest, a, b, c⟩
          rw [hPop] at hStep
          simp at hStep
          cases hStep
          simp [EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
  | log2 =>
      unfold Assembly.PrimStep.run at hStep
      cases hPop : state.stack.pop4 with
      | none =>
          rw [hPop] at hStep
          cases hStep
      | some popped =>
          rcases popped with ⟨rest, a, b, c, d⟩
          rw [hPop] at hStep
          simp at hStep
          cases hStep
          simp [EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
  | log3 =>
      unfold Assembly.PrimStep.run at hStep
      cases hPop : state.stack.pop5 with
      | none =>
          rw [hPop] at hStep
          cases hStep
      | some popped =>
          rcases popped with ⟨rest, a, b, c, d, e⟩
          rw [hPop] at hStep
          simp at hStep
          cases hStep
          simp [EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
  | log4 =>
      unfold Assembly.PrimStep.run at hStep
      cases hPop : state.stack.pop6 with
      | none =>
          rw [hPop] at hStep
          cases hStep
      | some popped =>
          rcases popped with ⟨rest, a, b, c, d, e, g⟩
          rw [hPop] at hStep
          simp at hStep
          cases hStep
          simp [EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
  | invalid =>
      unfold Assembly.PrimStep.run at hStep
      cases hStep

theorem step_pc {instr : BasicInstr} {state final : EVMState}
    (hStep : instr.step state = .ok final) :
    final.pc = state.pc + EvmYul.UInt256.ofNat instr.toAssembly.byteSize := by
  cases instr with
  | push value =>
      unfold BasicInstr.step at hStep
      simp [Assembly.Target.stepInstr] at hStep
      cases hStep
      simp [BasicInstr.toAssembly, Assembly.Instr.byteSize,
        Assembly.Instr.push32Size, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]
  | op op =>
      unfold BasicInstr.step BasicOp.step at hStep
      change Assembly.PrimOp.step op.toPrimOp state = .ok final at hStep
      cases hCont : op.toPrimOp.continuingStep? with
      | none =>
          cases op <;>
            simp [BasicOp.toPrimOp, Assembly.PrimOp.continuingStep?] at hCont
      | some step =>
          rw [Assembly.PrimOp.step_eq_continuingStep_run hCont] at hStep
          simpa [BasicInstr.toAssembly, Assembly.Instr.byteSize] using
            primStep_run_pc step hStep

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

theorem source_stepAt_eq_step {instr : BasicInstr}
    {program : Assembly.Program} {pc : Nat} {state : EVMState} :
    Assembly.Source.stepAt program pc instr.toAssembly state =
      instr.step state := by
  cases instr with
  | push value =>
      rfl
  | op op =>
      rfl

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

theorem source_step_ctx_relAt_of_relAt {instr : BasicInstr}
    {pre post : Assembly.Program}
    {source target source' : EVMState}
    (hFit : PCFits pre)
    (hRel : RelAt (Assembly.Program.pcAfter pre) target source)
    (hStep : instr.step source = .ok source') :
    ∃ target',
      Assembly.Source.step (pre ++ instr.toAssembly :: post) target =
          .ok target' ∧
        RelAt (Assembly.Program.pcAfter (pre ++ [instr.toAssembly]))
          target' source' := by
  obtain ⟨target', hTargetStep, hEq⟩ :=
    BasicInstr.step_projected_of_eraseControl_eq hRel.sameData hStep
  refine ⟨target', ?_, ?_, hEq⟩
  · unfold Assembly.Source.step
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
    change
      Assembly.Source.stepAt (pre ++ instr.toAssembly :: post)
          (Assembly.Program.byteLength pre) instr.toAssembly target =
        Except.ok target'
    rw [source_stepAt_eq_step]
    exact hTargetStep
  · calc
      target'.pc
          = target.pc + EvmYul.UInt256.ofNat instr.toAssembly.byteSize :=
              step_pc hTargetStep
      _ = Assembly.Program.pcAfter pre +
            EvmYul.UInt256.ofNat instr.toAssembly.byteSize := by
              rw [hRel.pc_eq]
      _ = EvmYul.UInt256.ofNat (Assembly.Program.byteLength pre) +
            EvmYul.UInt256.ofNat instr.toAssembly.byteSize := by
              rfl
      _ = EvmYul.UInt256.ofNat
            (Assembly.Program.byteLength pre + instr.toAssembly.byteSize) := by
              rw [Assembly.UInt256_ofNat_add]
      _ = Assembly.Program.pcAfter (pre ++ [instr.toAssembly]) := by
              simp [Assembly.Program.pcAfter, Assembly.Program.byteLength_append,
                Assembly.Program.byteLength]

end BasicInstr

namespace AssemblyControl

theorem label_step_ctx_relAt_of_relAt {label : Assembly.Label}
    {pre post : Assembly.Program} {source target : EVMState}
    (hFit : PCFits pre)
    (hRel : RelAt (Assembly.Program.pcAfter pre) target source) :
    ∃ target',
      Assembly.Source.step (pre ++ [Assembly.Instr.label label] ++ post)
          target = .ok target' ∧
        RelAt (Assembly.Program.pcAfter (pre ++ [Assembly.Instr.label label]))
          target' source := by
  refine ⟨target.incrPC, ?_, ?_, ?_⟩
  · unfold Assembly.Source.step
    have hAt :
        Assembly.Program.instrAtPc (pre ++ [Assembly.Instr.label label] ++ post)
            target.pc.toNat =
          some (Assembly.Program.byteLength pre, Assembly.Instr.label label) := by
      unfold Assembly.Program.instrAtPc
      rw [hRel.pc_eq, hFit]
      simpa using
        Assembly.Program.instrAtPcFrom_append_boundary_cons
          pre post (Assembly.Instr.label label) 0
    rw [hAt]
    rfl
  · calc
      target.incrPC.pc
          = target.pc + EvmYul.UInt256.ofNat 1 := rfl
      _ = Assembly.Program.pcAfter pre + EvmYul.UInt256.ofNat 1 := by
            rw [hRel.pc_eq]
      _ = EvmYul.UInt256.ofNat (Assembly.Program.byteLength pre) +
            EvmYul.UInt256.ofNat 1 := by
            rfl
      _ = EvmYul.UInt256.ofNat (Assembly.Program.byteLength pre + 1) := by
            rw [Assembly.UInt256_ofNat_add]
      _ = Assembly.Program.pcAfter (pre ++ [Assembly.Instr.label label]) := by
            simp [Assembly.Program.pcAfter, Assembly.Program.byteLength_append,
              Assembly.Program.byteLength, Assembly.Instr.byteSize]
  · simpa [SameData, eraseControl, Assembly.eraseGas,
      EvmYul.EVM.State.incrPC] using hRel.sameData

theorem jump_step_ctx_relAt_of_relAt {label : Assembly.Label} {dest : Nat}
    {pre post : Assembly.Program} {source target : EVMState}
    (hFit : PCFits pre)
    (hRel : RelAt (Assembly.Program.pcAfter pre) target source)
    (hLabel :
      Assembly.Program.labelPc (pre ++ [Assembly.Instr.jump label] ++ post)
        label = some dest) :
    ∃ target',
      Assembly.Source.step (pre ++ [Assembly.Instr.jump label] ++ post)
          target = .ok target' ∧
        RelAt (EvmYul.UInt256.ofNat dest) target' source := by
  refine ⟨Assembly.Source.jumpPc dest target, ?_, ?_, ?_⟩
  · unfold Assembly.Source.step
    have hAt :
        Assembly.Program.instrAtPc (pre ++ [Assembly.Instr.jump label] ++ post)
            target.pc.toNat =
          some (Assembly.Program.byteLength pre, Assembly.Instr.jump label) := by
      unfold Assembly.Program.instrAtPc
      rw [hRel.pc_eq, hFit]
      simpa using
        Assembly.Program.instrAtPcFrom_append_boundary_cons
          pre post (Assembly.Instr.jump label) 0
    rw [hAt]
    have hLabel' :
        Assembly.Program.labelPc (pre ++ Assembly.Instr.jump label :: post)
          label = some dest := by
      simpa using hLabel
    unfold Assembly.Source.stepAt
    simp [hLabel', Assembly.Source.invalid, Assembly.Source.jumpPc]
    rfl
  · rfl
  · simpa [SameData, Assembly.Source.jumpPc, eraseControl_with_pc] using
      hRel.sameData

end AssemblyControl

namespace Code

def PCFitsFrom : Assembly.Program → Code → Prop
  | pre, [] => PCFits pre
  | pre, instr :: rest =>
      PCFits pre ∧ PCFitsFrom (pre ++ [instr.toAssembly]) rest

theorem PCFitsFrom.end {pre : Assembly.Program} {code : Code}
    (hFits : PCFitsFrom pre code) :
    PCFits (pre ++ code.toAssembly) := by
  induction code generalizing pre with
  | nil =>
      simpa [PCFitsFrom, Code.toAssembly] using hFits
  | cons instr rest ih =>
      simpa [Code.toAssembly, List.append_assoc] using ih hFits.2

theorem PCFitsFrom.of_assembly {pre : Assembly.Program} {code : Code}
    (hFits : AssemblyProgram.PCFitsFrom pre code.toAssembly) :
    PCFitsFrom pre code := by
  induction code generalizing pre with
  | nil =>
      simpa [PCFitsFrom, Code.toAssembly] using hFits
  | cons instr rest ih =>
      change
        PCFits pre ∧
          PCFitsFrom (pre ++ [instr.toAssembly]) rest
      constructor
      · exact hFits.1
      · exact ih hFits.2

theorem source_run_ctx_relAt_of_relAt {code : Code}
    {pre post : Assembly.Program}
    {source target source' : EVMState}
    (hFits : PCFitsFrom pre code)
    (hRel : RelAt (Assembly.Program.pcAfter pre) target source)
    (hRun : Code.run code source = .ok source') :
    ARun (pre ++ code.toAssembly ++ post) target
      (fun target' =>
        RelAt (Assembly.Program.pcAfter (pre ++ code.toAssembly))
          target' source') := by
  induction code generalizing pre source target with
  | nil =>
      simp [Code.run] at hRun
      cases hRun
      refine ARun.pure ?_
      simpa [Code.toAssembly, Assembly.Program.byteLength_append,
        Assembly.Program.pcAfter] using hRel
  | cons instr rest ih =>
      unfold Code.run at hRun
      cases hStep : instr.step source with
      | error err =>
          rw [hStep] at hRun
          cases hRun
      | ok sourceMid =>
          rw [hStep] at hRun
          rcases hFits with ⟨hFitHere, hFitsRest⟩
          obtain ⟨targetMid, hAssemblyStep, hRelMid⟩ :=
            BasicInstr.source_step_ctx_relAt_of_relAt
              (instr := instr) (pre := pre)
              (post := Code.toAssembly rest ++ post)
              hFitHere hRel hStep
          refine
            ARun.bind
              (program := pre ++ Code.toAssembly (instr :: rest) ++ post)
              (middle := fun stateAfterInstr =>
                RelAt (Assembly.Program.pcAfter (pre ++ [instr.toAssembly]))
                  stateAfterInstr sourceMid)
              ?_ ?_
          · refine ⟨1, targetMid, ?_, hRelMid⟩
            change
              Assembly.Source.runN
                  (pre ++ Code.toAssembly (instr :: rest) ++ post)
                  1 target =
                Except.ok targetMid
            rw [show
                pre ++ Code.toAssembly (instr :: rest) ++ post =
                  pre ++ instr.toAssembly :: (Code.toAssembly rest ++ post) by
                  simp [Code.toAssembly, List.append_assoc]]
            unfold Assembly.Source.runN
            rw [hAssemblyStep]
            rfl
          · intro stateAfterInstr hStateAfterInstr
            change Code.run rest sourceMid = Except.ok source' at hRun
            have hRest :=
              ih (pre := pre ++ [instr.toAssembly])
                hFitsRest hStateAfterInstr hRun
            simpa [Code.toAssembly, List.append_assoc] using hRest

theorem jumpi_step_ctx_relAt_of_popCondition
    {label : Assembly.Label} {dest : Nat}
    {pre post : Assembly.Program}
    {source target source' : EVMState} {condTrue : Bool}
    (hFit : PCFits pre)
    (hRel : RelAt (Assembly.Program.pcAfter pre) target source)
    (hLabel :
      Assembly.Program.labelPc (pre ++ [Assembly.Instr.jumpi label] ++ post)
        label = some dest)
    (hPop : popCondition source = .ok (source', condTrue)) :
    ∃ target',
      Assembly.Source.step (pre ++ [Assembly.Instr.jumpi label] ++ post) target =
          .ok target' ∧
        RelAt
          (if condTrue then
            EvmYul.UInt256.ofNat dest
          else
            Assembly.Program.pcAfter (pre ++ [Assembly.Instr.jumpi label]))
          target' source' := by
  unfold popCondition at hPop
  have hStack := stack_eq_of_eraseControl_eq hRel.sameData
  cases hSourcePop : source.stack.pop with
  | none =>
      rw [hSourcePop] at hPop
      cases hPop
  | some popped =>
      rcases popped with ⟨rest, cond⟩
      have hTargetPop : target.stack.pop = some (rest, cond) := by
        rw [hStack, hSourcePop]
      rw [hSourcePop] at hPop
      simp at hPop
      cases hPop.1
      cases hPop.2
      unfold Assembly.Source.step
      have hAt :
          Assembly.Program.instrAtPc
              (pre ++ [Assembly.Instr.jumpi label] ++ post)
              target.pc.toNat =
            some (Assembly.Program.byteLength pre, Assembly.Instr.jumpi label) := by
        unfold Assembly.Program.instrAtPc
        rw [hRel.pc_eq, hFit]
        simpa using
          Assembly.Program.instrAtPcFrom_append_boundary_cons
            pre post (Assembly.Instr.jumpi label) 0
      rw [hAt]
      have hLabel' :
          Assembly.Program.labelPc (pre ++ Assembly.Instr.jumpi label :: post)
            label = some dest := by
        simpa using hLabel
      change
        ∃ target',
          Assembly.Source.stepAt (pre ++ [Assembly.Instr.jumpi label] ++ post)
              (Assembly.Program.byteLength pre) (Assembly.Instr.jumpi label)
              target =
            Except.ok target' ∧
              RelAt
                (if (cond != EvmYul.UInt256.ofNat 0) then
                  EvmYul.UInt256.ofNat dest
                else
                  Assembly.Program.pcAfter (pre ++ [Assembly.Instr.jumpi label]))
                target'
                { source with stack := rest }
      unfold Assembly.Source.stepAt
      simp [hLabel', Assembly.Source.invalid, hTargetPop]
      by_cases hCond : cond != EvmYul.UInt256.ofNat 0
      · simp [hCond]
        refine
          ⟨{ target with pc := EvmYul.UInt256.ofNat dest, stack := rest },
            rfl, ?_, ?_⟩
        · rfl
        calc
          eraseControl { target with pc := EvmYul.UInt256.ofNat dest, stack := rest }
              = eraseControl { target with stack := rest } := by
                  simpa using
                    (eraseControl_with_pc { target with stack := rest }
                      (EvmYul.UInt256.ofNat dest))
          _ = { eraseControl target with stack := rest } :=
                  eraseControl_with_stack target rest
          _ = { eraseControl source with stack := rest } := by
                  rw [hRel.sameData]
          _ = eraseControl { source with stack := rest } :=
                  (eraseControl_with_stack source rest).symm
      · simp [hCond]
        refine
          ⟨{ target with pc := (Assembly.Source.jumpiFallthroughPc target), stack := rest },
            rfl, ?_, ?_⟩
        · unfold Assembly.Source.jumpiFallthroughPc Assembly.Program.pcAfter
          calc
            target.pc + EvmYul.UInt256.ofNat Assembly.Instr.push32Size +
                EvmYul.UInt256.ofNat 1
                = EvmYul.UInt256.ofNat (Assembly.Program.byteLength pre) +
                    EvmYul.UInt256.ofNat Assembly.Instr.push32Size +
                      EvmYul.UInt256.ofNat 1 := by
                        rw [hRel.pc_eq]
                        rfl
            _ = EvmYul.UInt256.ofNat
                  (Assembly.Program.byteLength pre +
                    Assembly.Instr.push32Size) +
                    EvmYul.UInt256.ofNat 1 := by
                      rw [Assembly.UInt256_ofNat_add]
            _ = EvmYul.UInt256.ofNat
                  (Assembly.Program.byteLength pre +
                    Assembly.Instr.push32Size + 1) := by
                      rw [Assembly.UInt256_ofNat_add]
            _ = EvmYul.UInt256.ofNat
                  (Assembly.Program.byteLength
                    (pre ++ [Assembly.Instr.jumpi label])) := by
                      simp [Assembly.Program.byteLength_append,
                        Assembly.Program.byteLength, Assembly.Instr.byteSize,
                        Assembly.Instr.jumpSize]
                      rw [Nat.add_assoc]
        calc
          eraseControl { target with
                pc := (Assembly.Source.jumpiFallthroughPc target), stack := rest }
              = eraseControl { target with stack := rest } := by
                  simpa using
                    (eraseControl_with_pc { target with stack := rest }
                      (Assembly.Source.jumpiFallthroughPc target))
          _ = { eraseControl target with stack := rest } :=
                  eraseControl_with_stack target rest
          _ = { eraseControl source with stack := rest } := by
                  rw [hRel.sameData]
          _ = eraseControl { source with stack := rest } :=
                  (eraseControl_with_stack source rest).symm

theorem runCondition_jumpi_ctx_relAt_of_relAt
    {cond : Code} {label : Assembly.Label} {dest : Nat}
    {pre post : Assembly.Program}
    {source target source' : EVMState} {condTrue : Bool}
    (hFits : PCFitsFrom pre cond)
    (hRel : RelAt (Assembly.Program.pcAfter pre) target source)
    (hLabel :
      Assembly.Program.labelPc
          (pre ++ cond.toAssembly ++ [Assembly.Instr.jumpi label] ++ post)
          label = some dest)
    (hRun : runCondition cond source = .ok (source', condTrue)) :
    ARun (pre ++ cond.toAssembly ++ [Assembly.Instr.jumpi label] ++ post)
      target
      (fun target' =>
        RelAt
          (if condTrue then
            EvmYul.UInt256.ofNat dest
          else
            Assembly.Program.pcAfter
              (pre ++ cond.toAssembly ++ [Assembly.Instr.jumpi label]))
          target' source') := by
  unfold runCondition at hRun
  cases hCode : run cond source with
  | error err =>
      rw [hCode] at hRun
      cases hRun
  | ok sourceAfterCode =>
      rw [hCode] at hRun
      refine
        ARun.bind
          (program := pre ++ cond.toAssembly ++ [Assembly.Instr.jumpi label] ++ post)
          (middle := fun targetAfterCode =>
            RelAt (Assembly.Program.pcAfter (pre ++ cond.toAssembly))
              targetAfterCode sourceAfterCode)
          ?_ ?_
      · have hCodeRun :=
          source_run_ctx_relAt_of_relAt
            (code := cond) (pre := pre)
            (post := [Assembly.Instr.jumpi label] ++ post)
            hFits hRel hCode
        simpa [List.append_assoc] using hCodeRun
      · intro targetAfterCode hRelAfterCode
        have hLabel' :
            Assembly.Program.labelPc
                ((pre ++ cond.toAssembly) ++
                  [Assembly.Instr.jumpi label] ++ post) label =
              some dest := by
          simpa [List.append_assoc] using hLabel
        obtain ⟨targetAfterJump, hJumpStep, hRelAfterJump⟩ :=
          jumpi_step_ctx_relAt_of_popCondition
            (label := label) (dest := dest)
            (pre := pre ++ cond.toAssembly) (post := post)
            (PCFitsFrom.end hFits) hRelAfterCode hLabel' hRun
        refine ⟨1, targetAfterJump, ?_, ?_⟩
        · change
            Assembly.Source.runN
                (pre ++ cond.toAssembly ++
                  [Assembly.Instr.jumpi label] ++ post)
                1 targetAfterCode =
              Except.ok targetAfterJump
          rw [show
              pre ++ cond.toAssembly ++ [Assembly.Instr.jumpi label] ++ post =
                (pre ++ cond.toAssembly) ++ [Assembly.Instr.jumpi label] ++ post by
                simp [List.append_assoc]]
          unfold Assembly.Source.runN
          rw [hJumpStep]
          rfl
        · simpa [List.append_assoc] using hRelAfterJump

end Code

def BlockPreserves (supply : LabelSupply) (block : Block) : Prop :=
  ∀ {pre post : Assembly.Program} {fuel : Nat}
    {source target final : EVMState},
    AssemblyProgram.labelsLt supply pre →
    AssemblyProgram.PCFitsFrom pre (Block.compileFrom supply block).code →
    RelAt (Assembly.Program.pcAfter pre) target source →
    Block.Eval fuel block source final →
    ARun (pre ++ (Block.compileFrom supply block).code ++ post) target
      (fun target' =>
        RelAt
          (Assembly.Program.pcAfter
            (pre ++ (Block.compileFrom supply block).code))
          target' final)

def StmtPreserves (supply : LabelSupply) (stmt : Stmt) : Prop :=
  ∀ {pre post : Assembly.Program} {fuel : Nat}
    {source target final : EVMState},
    AssemblyProgram.labelsLt supply pre →
    AssemblyProgram.PCFitsFrom pre (Stmt.compileFrom supply stmt).code →
    RelAt (Assembly.Program.pcAfter pre) target source →
    Stmt.Eval fuel stmt source final →
    ARun (pre ++ (Stmt.compileFrom supply stmt).code ++ post) target
      (fun target' =>
        RelAt
          (Assembly.Program.pcAfter
            (pre ++ (Stmt.compileFrom supply stmt).code))
          target' final)

namespace StmtPreserves

theorem code (supply : LabelSupply) (code : Code) :
    StmtPreserves supply (.code code) := by
  intro pre post fuel source target final _hLabels hFits hRel hEval
  cases hEval with
  | code hCode =>
      have hCodeFits :
          Code.PCFitsFrom pre code :=
        Code.PCFitsFrom.of_assembly (by
          simpa [Stmt.compileFrom] using hFits)
      have hRun :=
        Code.source_run_ctx_relAt_of_relAt
          (code := code) (pre := pre) (post := post)
          hCodeFits hRel hCode
      simpa [Stmt.compileFrom] using hRun

theorem ifElse_false {supply : LabelSupply} {cond : Code}
    {thenBody elseBody : Block}
    (hElse : BlockPreserves (LabelSupply.next supply) elseBody) :
    ∀ {pre post : Assembly.Program} {fuel : Nat}
      {source target stateAfterCond final : EVMState},
      AssemblyProgram.labelsLt supply pre →
      AssemblyProgram.PCFitsFrom pre
        (Stmt.compileFrom supply (.ifElse cond thenBody elseBody)).code →
      RelAt (Assembly.Program.pcAfter pre) target source →
      Code.runCondition cond source = .ok (stateAfterCond, false) →
      Block.Eval fuel elseBody stateAfterCond final →
      ARun
        (pre ++ (Stmt.compileFrom supply (.ifElse cond thenBody elseBody)).code ++
          post)
        target
        (fun target' =>
          RelAt
            (Assembly.Program.pcAfter
              (pre ++
                (Stmt.compileFrom supply
                  (.ifElse cond thenBody elseBody)).code))
            target' final) := by
  intro pre post fuel source target stateAfterCond final
    hLabels hFits hRel hCond hElseEval
  let thenLabel := LabelSupply.label supply 0
  let endLabel := LabelSupply.label supply 1
  let compiledElse := Block.compileFrom (LabelSupply.next supply) elseBody
  let compiledThen := Block.compileFrom compiledElse.next thenBody
  let afterJumpi : Assembly.Program := [Assembly.Instr.jumpi thenLabel]
  let afterElse : Assembly.Program :=
    [Assembly.Instr.jump endLabel, Assembly.Instr.label thenLabel] ++
      compiledThen.code ++ [Assembly.Instr.label endLabel]
  have hFitsFull :
      AssemblyProgram.PCFitsFrom pre
        (cond.toAssembly ++ afterJumpi ++ compiledElse.code ++
          [Assembly.Instr.jump endLabel, Assembly.Instr.label thenLabel] ++
          compiledThen.code ++ [Assembly.Instr.label endLabel]) := by
    simpa [Stmt.compileFrom, thenLabel, endLabel, compiledElse,
      compiledThen, afterJumpi, List.append_assoc] using hFits
  have hCondFitsAsm :
      AssemblyProgram.PCFitsFrom pre cond.toAssembly :=
    AssemblyProgram.PCFitsFrom.left
      (pre := pre) (first := cond.toAssembly)
      (second := afterJumpi ++ compiledElse.code ++ afterElse)
      (by
        simpa [afterJumpi, afterElse, List.append_assoc] using hFitsFull)
  have hCondFits : Code.PCFitsFrom pre cond :=
    Code.PCFitsFrom.of_assembly hCondFitsAsm
  have hThenLabel :
      Assembly.Program.labelPc
        (pre ++ cond.toAssembly ++ [Assembly.Instr.jumpi thenLabel] ++
          (compiledElse.code ++
            [Assembly.Instr.jump endLabel, Assembly.Instr.label thenLabel] ++
            compiledThen.code ++ [Assembly.Instr.label endLabel] ++ post))
        thenLabel =
          some (Assembly.Program.byteLength
            (pre ++ cond.toAssembly ++ [Assembly.Instr.jumpi thenLabel] ++
              compiledElse.code ++ [Assembly.Instr.jump endLabel])) := by
    have hPc :=
      CompilerFacts.ifElse_then_labelPc
        (pre := pre) (post := post) (supply := supply)
        (cond := cond) (thenBody := thenBody) (elseBody := elseBody)
        hLabels
    simpa [thenLabel, endLabel, compiledElse, compiledThen,
      LabelSupply.next, Stmt.compileFrom, List.append_assoc] using hPc
  have hCondRun :=
    Code.runCondition_jumpi_ctx_relAt_of_relAt
      (cond := cond) (label := thenLabel)
      (dest := Assembly.Program.byteLength
        (pre ++ cond.toAssembly ++ [Assembly.Instr.jumpi thenLabel] ++
          compiledElse.code ++ [Assembly.Instr.jump endLabel]))
      (pre := pre)
      (post :=
        compiledElse.code ++
          [Assembly.Instr.jump endLabel, Assembly.Instr.label thenLabel] ++
          compiledThen.code ++ [Assembly.Instr.label endLabel] ++ post)
      hCondFits hRel hThenLabel hCond
  refine
    ARun.bind
      (program := pre ++
        (Stmt.compileFrom supply (.ifElse cond thenBody elseBody)).code ++ post)
      (middle := fun targetAfterCond =>
        RelAt
          (Assembly.Program.pcAfter
            (pre ++ cond.toAssembly ++ [Assembly.Instr.jumpi thenLabel]))
          targetAfterCond stateAfterCond)
      ?_ ?_
  · simpa [Stmt.compileFrom, thenLabel, endLabel, compiledElse,
      compiledThen, List.append_assoc] using hCondRun
  · intro targetAfterCond hRelAfterCond
    let elsePre : Assembly.Program :=
      pre ++ cond.toAssembly ++ [Assembly.Instr.jumpi thenLabel]
    have hAfterJumpiFits :
        AssemblyProgram.PCFitsFrom elsePre
          (compiledElse.code ++ afterElse) :=
      by
        simpa [elsePre, afterJumpi, afterElse, List.append_assoc] using
          AssemblyProgram.PCFitsFrom.right
            (pre := pre) (first := cond.toAssembly ++ afterJumpi)
            (second := compiledElse.code ++ afterElse)
            (by
              simpa [afterJumpi, afterElse, List.append_assoc]
                using hFitsFull)
    have hElseFits :
        AssemblyProgram.PCFitsFrom elsePre compiledElse.code :=
      AssemblyProgram.PCFitsFrom.left
        (pre := elsePre) (first := compiledElse.code)
        (second := afterElse) hAfterJumpiFits
    have hElseLabels :
        AssemblyProgram.labelsLt (LabelSupply.next supply) elsePre := by
      unfold elsePre
      simpa [List.append_assoc] using
        AssemblyProgram.labelsLt_append
          (AssemblyProgram.labelsLt_append
            (AssemblyProgram.labelsLt_mono (Nat.le_succ supply) hLabels)
            (Code.toAssembly_labelsLt (LabelSupply.next supply) cond))
          (AssemblyProgram.labelsLt_single_nonlabel
            (instr := Assembly.Instr.jumpi thenLabel)
            (by intro label h; cases h))
    have hElseRun :=
      hElse (pre := elsePre)
        (post :=
          [Assembly.Instr.jump endLabel, Assembly.Instr.label thenLabel] ++
            compiledThen.code ++ [Assembly.Instr.label endLabel] ++ post)
        hElseLabels hElseFits hRelAfterCond hElseEval
    refine
      ARun.bind
        (program := pre ++
          (Stmt.compileFrom supply (.ifElse cond thenBody elseBody)).code ++
            post)
        (middle := fun targetAfterElse =>
          RelAt (Assembly.Program.pcAfter (elsePre ++ compiledElse.code))
            targetAfterElse final)
        ?_ ?_
    · simpa [Stmt.compileFrom, thenLabel, endLabel, compiledElse,
        compiledThen, elsePre, afterElse, List.append_assoc] using hElseRun
    · intro targetAfterElse hRelAfterElse
      let endPrefix : Assembly.Program :=
        pre ++ cond.toAssembly ++ [Assembly.Instr.jumpi thenLabel] ++
          compiledElse.code ++
          [Assembly.Instr.jump endLabel, Assembly.Instr.label thenLabel] ++
          compiledThen.code
      have hEndLabel :
          Assembly.Program.labelPc
            ((elsePre ++ compiledElse.code) ++ [Assembly.Instr.jump endLabel] ++
              ([Assembly.Instr.label thenLabel] ++ compiledThen.code ++
                [Assembly.Instr.label endLabel] ++ post))
            endLabel =
              some (Assembly.Program.byteLength endPrefix) := by
        have hPc :=
          CompilerFacts.ifElse_end_labelPc
            (pre := pre) (post := post) (supply := supply)
            (cond := cond) (thenBody := thenBody) (elseBody := elseBody)
            hLabels
        simpa [thenLabel, endLabel, compiledElse, compiledThen,
          elsePre, endPrefix, LabelSupply.next, Stmt.compileFrom,
          List.append_assoc] using hPc
      have hJumpFit :
          PCFits (elsePre ++ compiledElse.code) :=
        AssemblyProgram.PCFitsFrom.end hElseFits
      obtain ⟨targetAfterJump, hJumpStep, hRelAfterJump⟩ :=
        AssemblyControl.jump_step_ctx_relAt_of_relAt
          (label := endLabel) (dest := Assembly.Program.byteLength endPrefix)
          (pre := elsePre ++ compiledElse.code)
          (post :=
            [Assembly.Instr.label thenLabel] ++ compiledThen.code ++
              [Assembly.Instr.label endLabel] ++ post)
          hJumpFit hRelAfterElse hEndLabel
      refine
        ARun.bind
          (program := pre ++
            (Stmt.compileFrom supply (.ifElse cond thenBody elseBody)).code ++
              post)
          (middle := fun targetAfterJump =>
            RelAt (Assembly.Program.pcAfter endPrefix)
              targetAfterJump final)
          ?_ ?_
      · refine ⟨1, targetAfterJump, ?_, ?_⟩
        · change
            Assembly.Source.runN
              (pre ++
                (Stmt.compileFrom supply
                  (.ifElse cond thenBody elseBody)).code ++ post)
              1 targetAfterElse = .ok targetAfterJump
          rw [show
              pre ++
                (Stmt.compileFrom supply
                  (.ifElse cond thenBody elseBody)).code ++ post =
                (elsePre ++ compiledElse.code) ++
                  [Assembly.Instr.jump endLabel] ++
                  ([Assembly.Instr.label thenLabel] ++ compiledThen.code ++
                    [Assembly.Instr.label endLabel] ++ post) by
                simp [Stmt.compileFrom, thenLabel, endLabel, compiledElse,
                  compiledThen, elsePre, List.append_assoc]]
          unfold Assembly.Source.runN
          rw [hJumpStep]
          rfl
        · simpa [Assembly.Program.pcAfter, endPrefix] using hRelAfterJump
      · intro targetAfterJump' hRelAfterJump'
        have hEndPrefixFits :
            AssemblyProgram.PCFitsFrom pre
              (cond.toAssembly ++ afterJumpi ++ compiledElse.code ++
                [Assembly.Instr.jump endLabel, Assembly.Instr.label thenLabel] ++
                compiledThen.code) :=
          AssemblyProgram.PCFitsFrom.left
            (pre := pre)
            (first :=
              cond.toAssembly ++ afterJumpi ++ compiledElse.code ++
                [Assembly.Instr.jump endLabel, Assembly.Instr.label thenLabel] ++
                compiledThen.code)
            (second := [Assembly.Instr.label endLabel])
            (by
              simpa [afterJumpi, afterElse, List.append_assoc] using hFitsFull)
        have hEndFit : PCFits endPrefix := by
          simpa [endPrefix, afterJumpi, List.append_assoc] using
            AssemblyProgram.PCFitsFrom.end hEndPrefixFits
        obtain ⟨targetAfterEnd, hEndStep, hRelAfterEnd⟩ :=
          AssemblyControl.label_step_ctx_relAt_of_relAt
            (label := endLabel) (pre := endPrefix) (post := post)
            hEndFit hRelAfterJump'
        refine ⟨1, targetAfterEnd, ?_, ?_⟩
        · change
            Assembly.Source.runN
              (pre ++
                (Stmt.compileFrom supply
                  (.ifElse cond thenBody elseBody)).code ++ post)
              1 targetAfterJump' = .ok targetAfterEnd
          rw [show
              pre ++
                (Stmt.compileFrom supply
                  (.ifElse cond thenBody elseBody)).code ++ post =
                endPrefix ++ [Assembly.Instr.label endLabel] ++ post by
                simp [Stmt.compileFrom, thenLabel, endLabel, compiledElse,
                  compiledThen, endPrefix, List.append_assoc]]
          unfold Assembly.Source.runN
          rw [hEndStep]
          rfl
        · simpa [Stmt.compileFrom, thenLabel, endLabel, compiledElse,
            compiledThen, endPrefix, List.append_assoc] using hRelAfterEnd

theorem ifElse_true {supply : LabelSupply} {cond : Code}
    {thenBody elseBody : Block}
    (hThen :
      BlockPreserves
        (Block.compileFrom (LabelSupply.next supply) elseBody).next
        thenBody) :
    ∀ {pre post : Assembly.Program} {fuel : Nat}
      {source target stateAfterCond final : EVMState},
      AssemblyProgram.labelsLt supply pre →
      AssemblyProgram.PCFitsFrom pre
        (Stmt.compileFrom supply (.ifElse cond thenBody elseBody)).code →
      RelAt (Assembly.Program.pcAfter pre) target source →
      Code.runCondition cond source = .ok (stateAfterCond, true) →
      Block.Eval fuel thenBody stateAfterCond final →
      ARun
        (pre ++ (Stmt.compileFrom supply (.ifElse cond thenBody elseBody)).code ++
          post)
        target
        (fun target' =>
          RelAt
            (Assembly.Program.pcAfter
              (pre ++
                (Stmt.compileFrom supply
                  (.ifElse cond thenBody elseBody)).code))
            target' final) := by
  intro pre post fuel source target stateAfterCond final
    hLabels hFits hRel hCond hThenEval
  let thenLabel := LabelSupply.label supply 0
  let endLabel := LabelSupply.label supply 1
  let compiledElse := Block.compileFrom (LabelSupply.next supply) elseBody
  let compiledThen := Block.compileFrom compiledElse.next thenBody
  let afterJumpi : Assembly.Program := [Assembly.Instr.jumpi thenLabel]
  let thenPrefix : Assembly.Program :=
    pre ++ cond.toAssembly ++ [Assembly.Instr.jumpi thenLabel] ++
      compiledElse.code ++ [Assembly.Instr.jump endLabel]
  let thenBodyPre : Assembly.Program :=
    thenPrefix ++ [Assembly.Instr.label thenLabel]
  have hSupplyLtElse : supply < compiledElse.next := by
    unfold compiledElse
    exact
      Nat.lt_of_lt_of_le (Nat.lt_succ_self supply)
        (CompilerFacts.block_compileFrom_next_ge elseBody
          (LabelSupply.next supply))
  have hFitsFull :
      AssemblyProgram.PCFitsFrom pre
        (cond.toAssembly ++ afterJumpi ++ compiledElse.code ++
          [Assembly.Instr.jump endLabel, Assembly.Instr.label thenLabel] ++
          compiledThen.code ++ [Assembly.Instr.label endLabel]) := by
    simpa [Stmt.compileFrom, thenLabel, endLabel, compiledElse,
      compiledThen, afterJumpi, List.append_assoc] using hFits
  have hCondFitsAsm :
      AssemblyProgram.PCFitsFrom pre cond.toAssembly :=
    AssemblyProgram.PCFitsFrom.left
      (pre := pre) (first := cond.toAssembly)
      (second :=
        afterJumpi ++ compiledElse.code ++
          [Assembly.Instr.jump endLabel, Assembly.Instr.label thenLabel] ++
          compiledThen.code ++ [Assembly.Instr.label endLabel])
      (by simpa [afterJumpi, List.append_assoc] using hFitsFull)
  have hCondFits : Code.PCFitsFrom pre cond :=
    Code.PCFitsFrom.of_assembly hCondFitsAsm
  have hThenLabel :
      Assembly.Program.labelPc
        (pre ++ cond.toAssembly ++ [Assembly.Instr.jumpi thenLabel] ++
          (compiledElse.code ++
            [Assembly.Instr.jump endLabel, Assembly.Instr.label thenLabel] ++
            compiledThen.code ++ [Assembly.Instr.label endLabel] ++ post))
        thenLabel =
          some (Assembly.Program.byteLength thenPrefix) := by
    have hPc :=
      CompilerFacts.ifElse_then_labelPc
        (pre := pre) (post := post) (supply := supply)
        (cond := cond) (thenBody := thenBody) (elseBody := elseBody)
        hLabels
    simpa [thenLabel, endLabel, compiledElse, compiledThen, thenPrefix,
      LabelSupply.next, Stmt.compileFrom, List.append_assoc] using hPc
  have hCondRun :=
    Code.runCondition_jumpi_ctx_relAt_of_relAt
      (cond := cond) (label := thenLabel)
      (dest := Assembly.Program.byteLength thenPrefix)
      (pre := pre)
      (post :=
        compiledElse.code ++
          [Assembly.Instr.jump endLabel, Assembly.Instr.label thenLabel] ++
          compiledThen.code ++ [Assembly.Instr.label endLabel] ++ post)
      hCondFits hRel hThenLabel hCond
  refine
    ARun.bind
      (program := pre ++
        (Stmt.compileFrom supply (.ifElse cond thenBody elseBody)).code ++ post)
      (middle := fun targetAfterCond =>
        RelAt (Assembly.Program.pcAfter thenPrefix)
          targetAfterCond stateAfterCond)
      ?_ ?_
  · simpa [Stmt.compileFrom, thenLabel, endLabel, compiledElse,
      compiledThen, thenPrefix, List.append_assoc] using hCondRun
  · intro targetAfterCond hRelAfterCond
    have hThenPrefixFitsFrom :
        AssemblyProgram.PCFitsFrom pre
          (cond.toAssembly ++ afterJumpi ++ compiledElse.code ++
            [Assembly.Instr.jump endLabel]) :=
      AssemblyProgram.PCFitsFrom.left
        (pre := pre)
        (first :=
          cond.toAssembly ++ afterJumpi ++ compiledElse.code ++
            [Assembly.Instr.jump endLabel])
        (second :=
          [Assembly.Instr.label thenLabel] ++ compiledThen.code ++
            [Assembly.Instr.label endLabel])
        (by simpa [afterJumpi, List.append_assoc] using hFitsFull)
    have hThenLabelFit : PCFits thenPrefix := by
      simpa [thenPrefix, afterJumpi, List.append_assoc] using
        AssemblyProgram.PCFitsFrom.end hThenPrefixFitsFrom
    obtain ⟨targetAfterThenLabel, hThenLabelStep, hRelAfterThenLabel⟩ :=
      AssemblyControl.label_step_ctx_relAt_of_relAt
        (label := thenLabel) (pre := thenPrefix)
        (post := compiledThen.code ++ [Assembly.Instr.label endLabel] ++ post)
        hThenLabelFit hRelAfterCond
    refine
      ARun.bind
        (program := pre ++
          (Stmt.compileFrom supply (.ifElse cond thenBody elseBody)).code ++
            post)
        (middle := fun targetAfterThenLabel =>
          RelAt (Assembly.Program.pcAfter thenBodyPre)
            targetAfterThenLabel stateAfterCond)
        ?_ ?_
    · refine ⟨1, targetAfterThenLabel, ?_, ?_⟩
      · change
          Assembly.Source.runN
            (pre ++
              (Stmt.compileFrom supply
                (.ifElse cond thenBody elseBody)).code ++ post)
            1 targetAfterCond = .ok targetAfterThenLabel
        rw [show
            pre ++
              (Stmt.compileFrom supply
                (.ifElse cond thenBody elseBody)).code ++ post =
              thenPrefix ++ [Assembly.Instr.label thenLabel] ++
                (compiledThen.code ++ [Assembly.Instr.label endLabel] ++ post) by
              simp [Stmt.compileFrom, thenLabel, endLabel, compiledElse,
                compiledThen, thenPrefix, List.append_assoc]]
        unfold Assembly.Source.runN
        rw [hThenLabelStep]
        rfl
      · simpa [thenBodyPre] using hRelAfterThenLabel
    · intro targetAfterThenLabel' hRelAfterThenLabel'
      have hAfterThenLabelFits :
          AssemblyProgram.PCFitsFrom thenBodyPre
            (compiledThen.code ++ [Assembly.Instr.label endLabel]) :=
        by
          simpa [thenPrefix, thenBodyPre, afterJumpi, List.append_assoc] using
            AssemblyProgram.PCFitsFrom.right
              (pre := pre)
              (first :=
                cond.toAssembly ++ afterJumpi ++ compiledElse.code ++
                  [Assembly.Instr.jump endLabel, Assembly.Instr.label thenLabel])
              (second := compiledThen.code ++ [Assembly.Instr.label endLabel])
              (by simpa [afterJumpi, List.append_assoc] using hFitsFull)
      have hThenFits :
          AssemblyProgram.PCFitsFrom thenBodyPre compiledThen.code :=
        AssemblyProgram.PCFitsFrom.left
          (pre := thenBodyPre) (first := compiledThen.code)
          (second := [Assembly.Instr.label endLabel])
          hAfterThenLabelFits
      have hThenLabels :
          AssemblyProgram.labelsLt compiledElse.next thenBodyPre := by
        unfold thenBodyPre thenPrefix
        simpa [List.append_assoc] using
          AssemblyProgram.labelsLt_append
            (AssemblyProgram.labelsLt_append
              (AssemblyProgram.labelsLt_append
                (AssemblyProgram.labelsLt_append
                  (AssemblyProgram.labelsLt_append
                    (AssemblyProgram.labelsLt_mono
                      (Nat.le_of_lt hSupplyLtElse) hLabels)
                    (Code.toAssembly_labelsLt compiledElse.next cond))
                  (AssemblyProgram.labelsLt_single_nonlabel
                    (instr := Assembly.Instr.jumpi thenLabel)
                    (by intro label h; cases h)))
                (CompilerFacts.block_compileFrom_labelsLt elseBody
                  (LabelSupply.next supply)))
              (AssemblyProgram.labelsLt_single_nonlabel
                (instr := Assembly.Instr.jump endLabel)
                (by intro label h; cases h)))
            (AssemblyProgram.labelsLt_single_label
              (by
                unfold thenLabel LabelSupply.label
                simp [Label.generatedScopeLt]
                exact hSupplyLtElse))
      have hThenRun :=
        hThen (pre := thenBodyPre)
          (post := [Assembly.Instr.label endLabel] ++ post)
          hThenLabels hThenFits hRelAfterThenLabel' hThenEval
      refine
        ARun.bind
          (program := pre ++
            (Stmt.compileFrom supply (.ifElse cond thenBody elseBody)).code ++
              post)
          (middle := fun targetAfterThen =>
            RelAt (Assembly.Program.pcAfter (thenBodyPre ++ compiledThen.code))
              targetAfterThen final)
          ?_ ?_
      · simpa [Stmt.compileFrom, thenLabel, endLabel, compiledElse,
          compiledThen, thenPrefix, thenBodyPre, List.append_assoc] using hThenRun
      · intro targetAfterThen hRelAfterThen
        let endPrefix : Assembly.Program :=
          thenBodyPre ++ compiledThen.code
        have hEndFit : PCFits endPrefix := by
          simpa [endPrefix] using
            AssemblyProgram.PCFitsFrom.end hThenFits
        obtain ⟨targetAfterEnd, hEndStep, hRelAfterEnd⟩ :=
          AssemblyControl.label_step_ctx_relAt_of_relAt
            (label := endLabel) (pre := endPrefix) (post := post)
            hEndFit hRelAfterThen
        refine ⟨1, targetAfterEnd, ?_, ?_⟩
        · change
            Assembly.Source.runN
              (pre ++
                (Stmt.compileFrom supply
                  (.ifElse cond thenBody elseBody)).code ++ post)
              1 targetAfterThen = .ok targetAfterEnd
          rw [show
              pre ++
                (Stmt.compileFrom supply
                  (.ifElse cond thenBody elseBody)).code ++ post =
                endPrefix ++ [Assembly.Instr.label endLabel] ++ post by
                simp [Stmt.compileFrom, thenLabel, endLabel, compiledElse,
                  compiledThen, thenPrefix, thenBodyPre, endPrefix,
                  List.append_assoc]]
          unfold Assembly.Source.runN
          rw [hEndStep]
          rfl
        · simpa [Stmt.compileFrom, thenLabel, endLabel, compiledElse,
            compiledThen, thenPrefix, thenBodyPre, endPrefix,
            List.append_assoc] using hRelAfterEnd

theorem ifElse {supply : LabelSupply} {cond : Code}
    {thenBody elseBody : Block}
    (hThen :
      BlockPreserves
        (Block.compileFrom (LabelSupply.next supply) elseBody).next
        thenBody)
    (hElse : BlockPreserves (LabelSupply.next supply) elseBody) :
    StmtPreserves supply (.ifElse cond thenBody elseBody) := by
  intro pre post fuel source target final hLabels hFits hRel hEval
  cases hEval with
  | ifTrue hCond hThenEval =>
      exact
        ifElse_true (supply := supply) (cond := cond)
          (thenBody := thenBody) (elseBody := elseBody) hThen
          hLabels hFits hRel hCond hThenEval
  | ifFalse hCond hElseEval =>
      exact
        ifElse_false (supply := supply) (cond := cond)
          (thenBody := thenBody) (elseBody := elseBody) hElse
          hLabels hFits hRel hCond hElseEval

theorem forLoop_false {supply : LabelSupply} {init postBlock body : Block}
    {cond : Code} :
    ∀ {pre suffix : Assembly.Program}
      {source target stateAfterCond : EVMState},
      AssemblyProgram.labelsLt supply pre →
      AssemblyProgram.PCFitsFrom pre
        (Stmt.compileFrom supply (.for_ init cond postBlock body)).code →
      RelAt
        (Assembly.Program.pcAfter
          (pre ++ (Block.compileFrom (LabelSupply.next supply) init).code))
        target source →
      Code.runCondition cond source = .ok (stateAfterCond, false) →
      ARun
        (pre ++ (Stmt.compileFrom supply (.for_ init cond postBlock body)).code ++
          suffix)
        target
        (fun target' =>
          RelAt
            (Assembly.Program.pcAfter
              (pre ++
                (Stmt.compileFrom supply
                  (.for_ init cond postBlock body)).code))
            target' stateAfterCond) := by
  intro pre suffix source target stateAfterCond hLabels hFits hRel hCond
  let loopLabel := LabelSupply.label supply 0
  let bodyLabel := LabelSupply.label supply 1
  let endLabel := LabelSupply.label supply 2
  let compiledInit := Block.compileFrom (LabelSupply.next supply) init
  let compiledBody := Block.compileFrom compiledInit.next body
  let compiledPost := Block.compileFrom compiledBody.next postBlock
  let loopPre : Assembly.Program := pre ++ compiledInit.code
  let condPre : Assembly.Program := loopPre ++ [Assembly.Instr.label loopLabel]
  let jumpEndPre : Assembly.Program :=
    condPre ++ cond.toAssembly ++ [Assembly.Instr.jumpi bodyLabel]
  let endPrefix : Assembly.Program :=
    condPre ++ cond.toAssembly ++
      [ Assembly.Instr.jumpi bodyLabel
      , Assembly.Instr.jump endLabel
      , Assembly.Instr.label bodyLabel
      ] ++
      compiledBody.code ++ compiledPost.code ++
      [Assembly.Instr.jump loopLabel]
  have hFitsFull :
      AssemblyProgram.PCFitsFrom pre
        (compiledInit.code ++ [Assembly.Instr.label loopLabel] ++
          cond.toAssembly ++
          [ Assembly.Instr.jumpi bodyLabel
          , Assembly.Instr.jump endLabel
          , Assembly.Instr.label bodyLabel
          ] ++
          compiledBody.code ++ compiledPost.code ++
          [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel]) := by
    simpa [Stmt.compileFrom, loopLabel, bodyLabel, endLabel, compiledInit,
      compiledBody, compiledPost, LabelSupply.next, List.append_assoc] using hFits
  have hInitFits :
      AssemblyProgram.PCFitsFrom pre compiledInit.code :=
    AssemblyProgram.PCFitsFrom.left
      (pre := pre) (first := compiledInit.code)
      (second :=
        [Assembly.Instr.label loopLabel] ++ cond.toAssembly ++
          [ Assembly.Instr.jumpi bodyLabel
          , Assembly.Instr.jump endLabel
          , Assembly.Instr.label bodyLabel
          ] ++
          compiledBody.code ++ compiledPost.code ++
          [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel])
      (by simpa [List.append_assoc] using hFitsFull)
  have hLoopFit : PCFits loopPre := by
    simpa [loopPre] using AssemblyProgram.PCFitsFrom.end hInitFits
  obtain ⟨targetAfterLoopLabel, hLoopStep, hRelAfterLoopLabel⟩ :=
    AssemblyControl.label_step_ctx_relAt_of_relAt
      (label := loopLabel) (pre := loopPre)
      (post :=
        cond.toAssembly ++
          [ Assembly.Instr.jumpi bodyLabel
          , Assembly.Instr.jump endLabel
          , Assembly.Instr.label bodyLabel
          ] ++
          compiledBody.code ++ compiledPost.code ++
          [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel] ++
          suffix)
      hLoopFit hRel
  refine
    ARun.bind
      (program := pre ++
        (Stmt.compileFrom supply (.for_ init cond postBlock body)).code ++ suffix)
      (middle := fun targetAfterLoopLabel =>
        RelAt (Assembly.Program.pcAfter condPre)
          targetAfterLoopLabel source)
      ?_ ?_
  · refine ⟨1, targetAfterLoopLabel, ?_, ?_⟩
    · change
        Assembly.Source.runN
          (pre ++
            (Stmt.compileFrom supply (.for_ init cond postBlock body)).code ++
              suffix)
          1 target = .ok targetAfterLoopLabel
      rw [show
          pre ++
            (Stmt.compileFrom supply (.for_ init cond postBlock body)).code ++
              suffix =
            loopPre ++ [Assembly.Instr.label loopLabel] ++
              (cond.toAssembly ++
                [ Assembly.Instr.jumpi bodyLabel
                , Assembly.Instr.jump endLabel
                , Assembly.Instr.label bodyLabel
                ] ++
                compiledBody.code ++ compiledPost.code ++
                [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel] ++
                suffix) by
            simp [Stmt.compileFrom, loopLabel, bodyLabel, endLabel,
              compiledInit, compiledBody, compiledPost, loopPre,
              LabelSupply.next, List.append_assoc]]
      unfold Assembly.Source.runN
      rw [hLoopStep]
      rfl
    · simpa [condPre] using hRelAfterLoopLabel
  · intro targetAfterLoopLabel' hRelAfterLoopLabel'
    have hAfterLoopFits :
        AssemblyProgram.PCFitsFrom condPre
          (cond.toAssembly ++
            [ Assembly.Instr.jumpi bodyLabel
            , Assembly.Instr.jump endLabel
            , Assembly.Instr.label bodyLabel
            ] ++
            compiledBody.code ++ compiledPost.code ++
            [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel]) :=
      by
        simpa [loopPre, condPre, List.append_assoc] using
          AssemblyProgram.PCFitsFrom.right
            (pre := pre)
            (first := compiledInit.code ++ [Assembly.Instr.label loopLabel])
            (second :=
              cond.toAssembly ++
                [ Assembly.Instr.jumpi bodyLabel
                , Assembly.Instr.jump endLabel
                , Assembly.Instr.label bodyLabel
                ] ++
                compiledBody.code ++ compiledPost.code ++
                [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel])
            (by simpa [List.append_assoc] using hFitsFull)
    have hCondFitsAsm :
        AssemblyProgram.PCFitsFrom condPre cond.toAssembly :=
      AssemblyProgram.PCFitsFrom.left
        (pre := condPre) (first := cond.toAssembly)
        (second :=
          [ Assembly.Instr.jumpi bodyLabel
          , Assembly.Instr.jump endLabel
          , Assembly.Instr.label bodyLabel
          ] ++
          compiledBody.code ++ compiledPost.code ++
          [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel])
        (by simpa [List.append_assoc] using hAfterLoopFits)
    have hCondFits : Code.PCFitsFrom condPre cond :=
      Code.PCFitsFrom.of_assembly hCondFitsAsm
    have hBodyLabelPc :
        Assembly.Program.labelPc
          (condPre ++ cond.toAssembly ++ [Assembly.Instr.jumpi bodyLabel] ++
            ([Assembly.Instr.jump endLabel, Assembly.Instr.label bodyLabel] ++
              compiledBody.code ++ compiledPost.code ++
              [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel] ++
              suffix))
          bodyLabel =
            some (Assembly.Program.byteLength
              (condPre ++ cond.toAssembly ++
                [Assembly.Instr.jumpi bodyLabel, Assembly.Instr.jump endLabel])) := by
      have hPc :=
        CompilerFacts.for_body_labelPc
          (pre := pre) (suffix := suffix) (supply := supply)
          (init := init) (post := postBlock) (body := body)
          (cond := cond) hLabels
      simpa [Stmt.compileFrom, loopLabel, bodyLabel, endLabel, compiledInit,
        compiledBody, compiledPost, condPre, loopPre, LabelSupply.next,
        List.append_assoc] using hPc
    have hCondRun :=
      Code.runCondition_jumpi_ctx_relAt_of_relAt
        (cond := cond) (label := bodyLabel)
        (dest := Assembly.Program.byteLength
          (condPre ++ cond.toAssembly ++
            [Assembly.Instr.jumpi bodyLabel, Assembly.Instr.jump endLabel]))
        (pre := condPre)
        (post :=
          [Assembly.Instr.jump endLabel, Assembly.Instr.label bodyLabel] ++
            compiledBody.code ++ compiledPost.code ++
            [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel] ++
            suffix)
        hCondFits hRelAfterLoopLabel' hBodyLabelPc hCond
    refine
      ARun.bind
        (program := pre ++
          (Stmt.compileFrom supply (.for_ init cond postBlock body)).code ++
            suffix)
        (middle := fun targetAfterCond =>
          RelAt (Assembly.Program.pcAfter jumpEndPre)
            targetAfterCond stateAfterCond)
        ?_ ?_
    · simpa [Stmt.compileFrom, loopLabel, bodyLabel, endLabel, compiledInit,
        compiledBody, compiledPost, condPre, jumpEndPre, loopPre,
        LabelSupply.next, List.append_assoc] using hCondRun
    · intro targetAfterCond hRelAfterCond
      have hJumpEndFitsFrom :
          AssemblyProgram.PCFitsFrom condPre
            (cond.toAssembly ++ [Assembly.Instr.jumpi bodyLabel]) :=
        AssemblyProgram.PCFitsFrom.left
          (pre := condPre)
          (first := cond.toAssembly ++ [Assembly.Instr.jumpi bodyLabel])
          (second :=
            [Assembly.Instr.jump endLabel, Assembly.Instr.label bodyLabel] ++
              compiledBody.code ++ compiledPost.code ++
              [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel])
          (by simpa [List.append_assoc] using hAfterLoopFits)
      have hJumpEndFit : PCFits jumpEndPre := by
        simpa [jumpEndPre, List.append_assoc] using
          AssemblyProgram.PCFitsFrom.end hJumpEndFitsFrom
      have hEndLabelPc :
          Assembly.Program.labelPc
            (jumpEndPre ++ [Assembly.Instr.jump endLabel] ++
              ([Assembly.Instr.label bodyLabel] ++ compiledBody.code ++
                compiledPost.code ++
                [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel] ++
                suffix))
            endLabel =
              some (Assembly.Program.byteLength endPrefix) := by
        have hPc :=
          CompilerFacts.for_end_labelPc
            (pre := pre) (suffix := suffix) (supply := supply)
            (init := init) (post := postBlock) (body := body)
            (cond := cond) hLabels
        simpa [Stmt.compileFrom, loopLabel, bodyLabel, endLabel,
          compiledInit, compiledBody, compiledPost, loopPre, condPre,
          jumpEndPre, endPrefix, LabelSupply.next, List.append_assoc] using hPc
      obtain ⟨targetAfterJumpEnd, hJumpEndStep, hRelAfterJumpEnd⟩ :=
        AssemblyControl.jump_step_ctx_relAt_of_relAt
          (label := endLabel) (dest := Assembly.Program.byteLength endPrefix)
          (pre := jumpEndPre)
          (post :=
            [Assembly.Instr.label bodyLabel] ++ compiledBody.code ++
              compiledPost.code ++
              [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel] ++
              suffix)
          hJumpEndFit hRelAfterCond hEndLabelPc
      refine
        ARun.bind
          (program := pre ++
            (Stmt.compileFrom supply (.for_ init cond postBlock body)).code ++
              suffix)
          (middle := fun targetAfterJumpEnd =>
            RelAt (Assembly.Program.pcAfter endPrefix)
              targetAfterJumpEnd stateAfterCond)
          ?_ ?_
      · refine ⟨1, targetAfterJumpEnd, ?_, ?_⟩
        · change
            Assembly.Source.runN
              (pre ++
                (Stmt.compileFrom supply (.for_ init cond postBlock body)).code ++
                  suffix)
              1 targetAfterCond = .ok targetAfterJumpEnd
          rw [show
              pre ++
                (Stmt.compileFrom supply (.for_ init cond postBlock body)).code ++
                  suffix =
                jumpEndPre ++ [Assembly.Instr.jump endLabel] ++
                  ([Assembly.Instr.label bodyLabel] ++ compiledBody.code ++
                    compiledPost.code ++
                    [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel] ++
                    suffix) by
                simp [Stmt.compileFrom, loopLabel, bodyLabel, endLabel,
                  compiledInit, compiledBody, compiledPost, loopPre, condPre,
                  jumpEndPre, LabelSupply.next, List.append_assoc]]
          unfold Assembly.Source.runN
          rw [hJumpEndStep]
          rfl
        · simpa [Assembly.Program.pcAfter, endPrefix] using hRelAfterJumpEnd
      · intro targetAfterJumpEnd' hRelAfterJumpEnd'
        have hEndPrefixFitsFrom :
            AssemblyProgram.PCFitsFrom pre
              (compiledInit.code ++ [Assembly.Instr.label loopLabel] ++
                cond.toAssembly ++
                [ Assembly.Instr.jumpi bodyLabel
                , Assembly.Instr.jump endLabel
                , Assembly.Instr.label bodyLabel
                ] ++
                compiledBody.code ++ compiledPost.code ++
                [Assembly.Instr.jump loopLabel]) :=
          AssemblyProgram.PCFitsFrom.left
            (pre := pre)
            (first :=
              compiledInit.code ++ [Assembly.Instr.label loopLabel] ++
                cond.toAssembly ++
                [ Assembly.Instr.jumpi bodyLabel
                , Assembly.Instr.jump endLabel
                , Assembly.Instr.label bodyLabel
                ] ++
                compiledBody.code ++ compiledPost.code ++
                [Assembly.Instr.jump loopLabel])
            (second := [Assembly.Instr.label endLabel])
            (by simpa [List.append_assoc] using hFitsFull)
        have hEndFit : PCFits endPrefix := by
          simpa [endPrefix, loopPre, condPre, List.append_assoc] using
            AssemblyProgram.PCFitsFrom.end hEndPrefixFitsFrom
        obtain ⟨targetAfterEnd, hEndStep, hRelAfterEnd⟩ :=
          AssemblyControl.label_step_ctx_relAt_of_relAt
            (label := endLabel) (pre := endPrefix) (post := suffix)
            hEndFit hRelAfterJumpEnd'
        refine ⟨1, targetAfterEnd, ?_, ?_⟩
        · change
            Assembly.Source.runN
              (pre ++
                (Stmt.compileFrom supply (.for_ init cond postBlock body)).code ++
                  suffix)
              1 targetAfterJumpEnd' = .ok targetAfterEnd
          rw [show
              pre ++
                (Stmt.compileFrom supply (.for_ init cond postBlock body)).code ++
                  suffix =
                endPrefix ++ [Assembly.Instr.label endLabel] ++ suffix by
                simp [Stmt.compileFrom, loopLabel, bodyLabel, endLabel,
                  compiledInit, compiledBody, compiledPost, loopPre, condPre,
                  endPrefix, LabelSupply.next, List.append_assoc]]
          unfold Assembly.Source.runN
          rw [hEndStep]
          rfl
        · simpa [Stmt.compileFrom, loopLabel, bodyLabel, endLabel,
            compiledInit, compiledBody, compiledPost, loopPre, condPre,
            endPrefix, LabelSupply.next, List.append_assoc] using hRelAfterEnd

theorem forLoop_true_step {supply : LabelSupply}
    {init postBlock body : Block} {cond : Code}
    (hBody : BlockPreserves
      (Block.compileFrom (LabelSupply.next supply) init).next body)
    (hPost :
      BlockPreserves
        (Block.compileFrom
          (Block.compileFrom (LabelSupply.next supply) init).next body).next
        postBlock) :
    ∀ {pre suffix : Assembly.Program}
      {source target stateAfterCond stateAfterBody stateAfterPost final : EVMState}
      {fuel : Nat},
      AssemblyProgram.labelsLt supply pre →
      AssemblyProgram.PCFitsFrom pre
        (Stmt.compileFrom supply (.for_ init cond postBlock body)).code →
      RelAt
        (Assembly.Program.pcAfter
          (pre ++ (Block.compileFrom (LabelSupply.next supply) init).code))
        target source →
      Code.runCondition cond source = .ok (stateAfterCond, true) →
      Block.Eval fuel body stateAfterCond stateAfterBody →
      Block.Eval fuel postBlock stateAfterBody stateAfterPost →
      (∀ targetAfterPost,
        RelAt
          (Assembly.Program.pcAfter
            (pre ++ (Block.compileFrom (LabelSupply.next supply) init).code))
          targetAfterPost stateAfterPost →
        ARun
          (pre ++
            (Stmt.compileFrom supply (.for_ init cond postBlock body)).code ++
            suffix)
          targetAfterPost
          (fun target' =>
            RelAt
              (Assembly.Program.pcAfter
                (pre ++
                  (Stmt.compileFrom supply
                    (.for_ init cond postBlock body)).code))
              target' final)) →
      ARun
        (pre ++
          (Stmt.compileFrom supply (.for_ init cond postBlock body)).code ++
          suffix)
        target
        (fun target' =>
          RelAt
            (Assembly.Program.pcAfter
              (pre ++
                (Stmt.compileFrom supply
                  (.for_ init cond postBlock body)).code))
            target' final) := by
  intro pre suffix source target stateAfterCond stateAfterBody stateAfterPost final
    fuel hLabels hFits hRel hCond hBodyEval hPostEval hLoop
  let loopLabel := LabelSupply.label supply 0
  let bodyLabel := LabelSupply.label supply 1
  let endLabel := LabelSupply.label supply 2
  let compiledInit := Block.compileFrom (LabelSupply.next supply) init
  let compiledBody := Block.compileFrom compiledInit.next body
  let compiledPost := Block.compileFrom compiledBody.next postBlock
  let loopPre : Assembly.Program := pre ++ compiledInit.code
  let condPre : Assembly.Program := loopPre ++ [Assembly.Instr.label loopLabel]
  let bodyPrefix : Assembly.Program :=
    condPre ++ cond.toAssembly ++
      [Assembly.Instr.jumpi bodyLabel, Assembly.Instr.jump endLabel]
  let bodyPre : Assembly.Program :=
    bodyPrefix ++ [Assembly.Instr.label bodyLabel]
  let postPre : Assembly.Program := bodyPre ++ compiledBody.code
  let jumpLoopPre : Assembly.Program := postPre ++ compiledPost.code
  have hSupplyLtInit : supply < compiledInit.next := by
    unfold compiledInit
    exact
      Nat.lt_of_lt_of_le (Nat.lt_succ_self supply)
        (CompilerFacts.block_compileFrom_next_ge init
          (LabelSupply.next supply))
  have hFitsFull :
      AssemblyProgram.PCFitsFrom pre
        (compiledInit.code ++ [Assembly.Instr.label loopLabel] ++
          cond.toAssembly ++
          [ Assembly.Instr.jumpi bodyLabel
          , Assembly.Instr.jump endLabel
          , Assembly.Instr.label bodyLabel
          ] ++
          compiledBody.code ++ compiledPost.code ++
          [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel]) := by
    simpa [Stmt.compileFrom, loopLabel, bodyLabel, endLabel, compiledInit,
      compiledBody, compiledPost, LabelSupply.next, List.append_assoc] using hFits
  have hInitFits :
      AssemblyProgram.PCFitsFrom pre compiledInit.code :=
    AssemblyProgram.PCFitsFrom.left
      (pre := pre) (first := compiledInit.code)
      (second :=
        [Assembly.Instr.label loopLabel] ++ cond.toAssembly ++
          [ Assembly.Instr.jumpi bodyLabel
          , Assembly.Instr.jump endLabel
          , Assembly.Instr.label bodyLabel
          ] ++
          compiledBody.code ++ compiledPost.code ++
          [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel])
      (by simpa [List.append_assoc] using hFitsFull)
  have hLoopFit : PCFits loopPre := by
    simpa [loopPre] using AssemblyProgram.PCFitsFrom.end hInitFits
  obtain ⟨targetAfterLoopLabel, hLoopStep, hRelAfterLoopLabel⟩ :=
    AssemblyControl.label_step_ctx_relAt_of_relAt
      (label := loopLabel) (pre := loopPre)
      (post :=
        cond.toAssembly ++
          [ Assembly.Instr.jumpi bodyLabel
          , Assembly.Instr.jump endLabel
          , Assembly.Instr.label bodyLabel
          ] ++
          compiledBody.code ++ compiledPost.code ++
          [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel] ++
          suffix)
      hLoopFit hRel
  refine
    ARun.bind
      (program := pre ++
        (Stmt.compileFrom supply (.for_ init cond postBlock body)).code ++
        suffix)
      (middle := fun targetAfterLoopLabel =>
        RelAt (Assembly.Program.pcAfter condPre)
          targetAfterLoopLabel source)
      ?_ ?_
  · refine ⟨1, targetAfterLoopLabel, ?_, ?_⟩
    · change
        Assembly.Source.runN
          (pre ++
            (Stmt.compileFrom supply (.for_ init cond postBlock body)).code ++
            suffix)
          1 target = .ok targetAfterLoopLabel
      rw [show
          pre ++
            (Stmt.compileFrom supply (.for_ init cond postBlock body)).code ++
            suffix =
            loopPre ++ [Assembly.Instr.label loopLabel] ++
              (cond.toAssembly ++
                [ Assembly.Instr.jumpi bodyLabel
                , Assembly.Instr.jump endLabel
                , Assembly.Instr.label bodyLabel
                ] ++
                compiledBody.code ++ compiledPost.code ++
                [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel] ++
                suffix) by
            simp [Stmt.compileFrom, loopLabel, bodyLabel, endLabel,
              compiledInit, compiledBody, compiledPost, loopPre,
              LabelSupply.next, List.append_assoc]]
      unfold Assembly.Source.runN
      rw [hLoopStep]
      rfl
    · simpa [condPre] using hRelAfterLoopLabel
  · intro targetAfterLoopLabel' hRelAfterLoopLabel'
    have hAfterLoopFits :
        AssemblyProgram.PCFitsFrom condPre
          (cond.toAssembly ++
            [ Assembly.Instr.jumpi bodyLabel
            , Assembly.Instr.jump endLabel
            , Assembly.Instr.label bodyLabel
            ] ++
            compiledBody.code ++ compiledPost.code ++
            [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel]) :=
      by
        simpa [loopPre, condPre, List.append_assoc] using
          AssemblyProgram.PCFitsFrom.right
            (pre := pre)
            (first := compiledInit.code ++ [Assembly.Instr.label loopLabel])
            (second :=
              cond.toAssembly ++
                [ Assembly.Instr.jumpi bodyLabel
                , Assembly.Instr.jump endLabel
                , Assembly.Instr.label bodyLabel
                ] ++
                compiledBody.code ++ compiledPost.code ++
                [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel])
            (by simpa [List.append_assoc] using hFitsFull)
    have hCondFitsAsm :
        AssemblyProgram.PCFitsFrom condPre cond.toAssembly :=
      AssemblyProgram.PCFitsFrom.left
        (pre := condPre) (first := cond.toAssembly)
        (second :=
          [ Assembly.Instr.jumpi bodyLabel
          , Assembly.Instr.jump endLabel
          , Assembly.Instr.label bodyLabel
          ] ++
          compiledBody.code ++ compiledPost.code ++
          [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel])
        (by simpa [List.append_assoc] using hAfterLoopFits)
    have hCondFits : Code.PCFitsFrom condPre cond :=
      Code.PCFitsFrom.of_assembly hCondFitsAsm
    have hBodyLabelPc :
        Assembly.Program.labelPc
          (condPre ++ cond.toAssembly ++ [Assembly.Instr.jumpi bodyLabel] ++
            ([Assembly.Instr.jump endLabel, Assembly.Instr.label bodyLabel] ++
              compiledBody.code ++ compiledPost.code ++
              [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel] ++
              suffix))
          bodyLabel =
            some (Assembly.Program.byteLength bodyPrefix) := by
      have hPc :=
        CompilerFacts.for_body_labelPc
          (pre := pre) (suffix := suffix) (supply := supply)
          (init := init) (post := postBlock) (body := body)
          (cond := cond) hLabels
      simpa [Stmt.compileFrom, loopLabel, bodyLabel, endLabel, compiledInit,
        compiledBody, compiledPost, condPre, loopPre, bodyPrefix,
        LabelSupply.next, List.append_assoc] using hPc
    have hCondRun :=
      Code.runCondition_jumpi_ctx_relAt_of_relAt
        (cond := cond) (label := bodyLabel)
        (dest := Assembly.Program.byteLength bodyPrefix)
        (pre := condPre)
        (post :=
          [Assembly.Instr.jump endLabel, Assembly.Instr.label bodyLabel] ++
            compiledBody.code ++ compiledPost.code ++
            [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel] ++
            suffix)
        hCondFits hRelAfterLoopLabel' hBodyLabelPc hCond
    refine
      ARun.bind
        (program := pre ++
          (Stmt.compileFrom supply (.for_ init cond postBlock body)).code ++
          suffix)
        (middle := fun targetAfterCond =>
          RelAt (Assembly.Program.pcAfter bodyPrefix)
            targetAfterCond stateAfterCond)
        ?_ ?_
    · simpa [Stmt.compileFrom, loopLabel, bodyLabel, endLabel, compiledInit,
        compiledBody, compiledPost, condPre, bodyPrefix, loopPre,
        LabelSupply.next, List.append_assoc] using hCondRun
    · intro targetAfterCond hRelAfterCond
      have hBodyPrefixFitsFrom :
          AssemblyProgram.PCFitsFrom condPre
            (cond.toAssembly ++
              [Assembly.Instr.jumpi bodyLabel, Assembly.Instr.jump endLabel]) :=
        AssemblyProgram.PCFitsFrom.left
          (pre := condPre)
          (first := cond.toAssembly ++
            [Assembly.Instr.jumpi bodyLabel, Assembly.Instr.jump endLabel])
          (second :=
            [Assembly.Instr.label bodyLabel] ++ compiledBody.code ++
              compiledPost.code ++
              [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel])
          (by simpa [List.append_assoc] using hAfterLoopFits)
      have hBodyLabelFit : PCFits bodyPrefix := by
        simpa [bodyPrefix, List.append_assoc] using
          AssemblyProgram.PCFitsFrom.end hBodyPrefixFitsFrom
      obtain ⟨targetAfterBodyLabel, hBodyLabelStep, hRelAfterBodyLabel⟩ :=
        AssemblyControl.label_step_ctx_relAt_of_relAt
          (label := bodyLabel) (pre := bodyPrefix)
          (post :=
            compiledBody.code ++ compiledPost.code ++
              [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel] ++
              suffix)
          hBodyLabelFit hRelAfterCond
      refine
        ARun.bind
          (program := pre ++
            (Stmt.compileFrom supply (.for_ init cond postBlock body)).code ++
            suffix)
          (middle := fun targetAfterBodyLabel =>
            RelAt (Assembly.Program.pcAfter bodyPre)
              targetAfterBodyLabel stateAfterCond)
          ?_ ?_
      · refine ⟨1, targetAfterBodyLabel, ?_, ?_⟩
        · change
            Assembly.Source.runN
              (pre ++
                (Stmt.compileFrom supply (.for_ init cond postBlock body)).code ++
                suffix)
              1 targetAfterCond = .ok targetAfterBodyLabel
          rw [show
              pre ++
                (Stmt.compileFrom supply (.for_ init cond postBlock body)).code ++
                suffix =
                bodyPrefix ++ [Assembly.Instr.label bodyLabel] ++
                  (compiledBody.code ++ compiledPost.code ++
                    [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel] ++
                    suffix) by
                simp [Stmt.compileFrom, loopLabel, bodyLabel, endLabel,
                  compiledInit, compiledBody, compiledPost, loopPre, condPre,
                  bodyPrefix, LabelSupply.next, List.append_assoc]]
          unfold Assembly.Source.runN
          rw [hBodyLabelStep]
          rfl
        · simpa [bodyPre] using hRelAfterBodyLabel
      · intro targetAfterBodyLabel' hRelAfterBodyLabel'
        have hAfterBodyLabelFits :
            AssemblyProgram.PCFitsFrom bodyPre
              (compiledBody.code ++ compiledPost.code ++
                [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel]) :=
          by
            simpa [bodyPrefix, bodyPre, loopPre, condPre, List.append_assoc] using
              AssemblyProgram.PCFitsFrom.right
                (pre := pre)
                (first :=
                  compiledInit.code ++ [Assembly.Instr.label loopLabel] ++
                    cond.toAssembly ++
                    [ Assembly.Instr.jumpi bodyLabel
                    , Assembly.Instr.jump endLabel
                    , Assembly.Instr.label bodyLabel
                    ])
                (second :=
                  compiledBody.code ++ compiledPost.code ++
                    [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel])
                (by simpa [List.append_assoc] using hFitsFull)
        have hBodyFits :
            AssemblyProgram.PCFitsFrom bodyPre compiledBody.code :=
          AssemblyProgram.PCFitsFrom.left
            (pre := bodyPre) (first := compiledBody.code)
            (second :=
              compiledPost.code ++
                [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel])
            (by simpa [List.append_assoc] using hAfterBodyLabelFits)
        have hBodyLabels : AssemblyProgram.labelsLt compiledInit.next bodyPre := by
          unfold bodyPre bodyPrefix condPre loopPre
          simpa [List.append_assoc] using
            AssemblyProgram.labelsLt_append
              (AssemblyProgram.labelsLt_append
                (AssemblyProgram.labelsLt_append
                  (AssemblyProgram.labelsLt_append
                    (AssemblyProgram.labelsLt_append
                      (AssemblyProgram.labelsLt_append
                        (AssemblyProgram.labelsLt_mono
                          (Nat.le_of_lt hSupplyLtInit) hLabels)
                        (CompilerFacts.block_compileFrom_labelsLt init
                          (LabelSupply.next supply)))
                      (AssemblyProgram.labelsLt_single_label
                        (by
                          unfold loopLabel LabelSupply.label
                          simp [Label.generatedScopeLt]
                          exact hSupplyLtInit)))
                    (Code.toAssembly_labelsLt compiledInit.next cond))
                  (AssemblyProgram.labelsLt_single_nonlabel
                    (instr := Assembly.Instr.jumpi bodyLabel)
                    (by intro label h; cases h)))
                (AssemblyProgram.labelsLt_single_nonlabel
                  (instr := Assembly.Instr.jump endLabel)
                  (by intro label h; cases h)))
              (AssemblyProgram.labelsLt_single_label
                (by
                  unfold bodyLabel LabelSupply.label
                  simp [Label.generatedScopeLt]
                  exact hSupplyLtInit))
        have hBodyRun :=
          hBody (pre := bodyPre)
            (post :=
              compiledPost.code ++
                [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel] ++
                suffix)
            hBodyLabels hBodyFits hRelAfterBodyLabel' hBodyEval
        refine
          ARun.bind
            (program := pre ++
              (Stmt.compileFrom supply (.for_ init cond postBlock body)).code ++
              suffix)
            (middle := fun targetAfterBody =>
              RelAt (Assembly.Program.pcAfter postPre)
                targetAfterBody stateAfterBody)
            ?_ ?_
        · simpa [Stmt.compileFrom, loopLabel, bodyLabel, endLabel,
            compiledInit, compiledBody, compiledPost, loopPre, condPre,
            bodyPrefix, bodyPre, postPre, LabelSupply.next, List.append_assoc]
            using hBodyRun
        · intro targetAfterBody hRelAfterBody
          have hPostFits :
              AssemblyProgram.PCFitsFrom postPre compiledPost.code :=
            by
              have hAfterBodyFits :
                  AssemblyProgram.PCFitsFrom postPre
                    (compiledPost.code ++
                      [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel]) :=
                AssemblyProgram.PCFitsFrom.right
                  (pre := bodyPre) (first := compiledBody.code)
                  (second :=
                    compiledPost.code ++
                      [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel])
                  (by simpa [List.append_assoc] using hAfterBodyLabelFits)
              exact
                AssemblyProgram.PCFitsFrom.left
                  (pre := postPre) (first := compiledPost.code)
                  (second :=
                    [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel])
                  (by simpa [postPre, List.append_assoc] using hAfterBodyFits)
          have hPostLabels :
              AssemblyProgram.labelsLt compiledBody.next postPre := by
            unfold postPre
            exact
              AssemblyProgram.labelsLt_append
                (AssemblyProgram.labelsLt_mono
                  (CompilerFacts.block_compileFrom_next_ge body compiledInit.next)
                  hBodyLabels)
                (CompilerFacts.block_compileFrom_labelsLt body compiledInit.next)
          have hPostRun :=
            hPost (pre := postPre)
              (post :=
                [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel] ++
                suffix)
              hPostLabels hPostFits hRelAfterBody hPostEval
          refine
            ARun.bind
              (program := pre ++
                (Stmt.compileFrom supply (.for_ init cond postBlock body)).code ++
                suffix)
              (middle := fun targetAfterPost =>
                RelAt (Assembly.Program.pcAfter jumpLoopPre)
                  targetAfterPost stateAfterPost)
              ?_ ?_
          · simpa [Stmt.compileFrom, loopLabel, bodyLabel, endLabel,
              compiledInit, compiledBody, compiledPost, loopPre, condPre,
              bodyPrefix, bodyPre, postPre, jumpLoopPre, LabelSupply.next,
              List.append_assoc] using hPostRun
          · intro targetAfterPost hRelAfterPost
            have hJumpLoopFitsFrom :
                AssemblyProgram.PCFitsFrom postPre
                  (compiledPost.code) := hPostFits
            have hJumpLoopFit : PCFits jumpLoopPre := by
              simpa [jumpLoopPre] using
                AssemblyProgram.PCFitsFrom.end hJumpLoopFitsFrom
            have hLoopLabelPc :
                Assembly.Program.labelPc
                  (jumpLoopPre ++ [Assembly.Instr.jump loopLabel] ++
                    ([Assembly.Instr.label endLabel] ++ suffix))
                  loopLabel =
                    some (Assembly.Program.byteLength loopPre) := by
              have hPc :=
                CompilerFacts.for_loop_labelPc
                  (pre := pre) (suffix := suffix) (supply := supply)
                  (init := init) (post := postBlock) (body := body)
                  (cond := cond) hLabels
              simpa [Stmt.compileFrom, loopLabel, bodyLabel, endLabel,
                compiledInit, compiledBody, compiledPost, loopPre, condPre,
                bodyPrefix, bodyPre, postPre, jumpLoopPre, LabelSupply.next,
                List.append_assoc] using hPc
            obtain ⟨targetAfterJumpLoop, hJumpLoopStep, hRelAfterJumpLoop⟩ :=
              AssemblyControl.jump_step_ctx_relAt_of_relAt
                (label := loopLabel)
                (dest := Assembly.Program.byteLength loopPre)
                (pre := jumpLoopPre)
                (post := [Assembly.Instr.label endLabel] ++ suffix)
                hJumpLoopFit hRelAfterPost hLoopLabelPc
            refine
              ARun.bind
                (program := pre ++
                  (Stmt.compileFrom supply (.for_ init cond postBlock body)).code ++
                  suffix)
                (middle := fun targetAfterJumpLoop =>
                  RelAt (Assembly.Program.pcAfter loopPre)
                    targetAfterJumpLoop stateAfterPost)
                ?_ ?_
            · refine ⟨1, targetAfterJumpLoop, ?_, ?_⟩
              · change
                  Assembly.Source.runN
                    (pre ++
                      (Stmt.compileFrom supply
                        (.for_ init cond postBlock body)).code ++
                      suffix)
                    1 targetAfterPost = .ok targetAfterJumpLoop
                rw [show
                    pre ++
                      (Stmt.compileFrom supply
                        (.for_ init cond postBlock body)).code ++
                      suffix =
                      jumpLoopPre ++ [Assembly.Instr.jump loopLabel] ++
                        ([Assembly.Instr.label endLabel] ++ suffix) by
                    simp [Stmt.compileFrom, loopLabel, bodyLabel, endLabel,
                      compiledInit, compiledBody, compiledPost, loopPre,
                      condPre, bodyPrefix, bodyPre, postPre, jumpLoopPre,
                      LabelSupply.next, List.append_assoc]]
                unfold Assembly.Source.runN
                rw [hJumpLoopStep]
                rfl
              · simpa [Assembly.Program.pcAfter, loopPre] using hRelAfterJumpLoop
            · intro targetAfterJumpLoop' hRelAfterJumpLoop'
              exact hLoop targetAfterJumpLoop' hRelAfterJumpLoop'

theorem forLoop {supply : LabelSupply}
    {init postBlock body : Block} {cond : Code}
    (hBody : BlockPreserves
      (Block.compileFrom (LabelSupply.next supply) init).next body)
    (hPost :
      BlockPreserves
        (Block.compileFrom
          (Block.compileFrom (LabelSupply.next supply) init).next body).next
        postBlock) :
    ∀ {pre suffix : Assembly.Program} {fuel : Nat}
      {source target final : EVMState},
      AssemblyProgram.labelsLt supply pre →
      AssemblyProgram.PCFitsFrom pre
        (Stmt.compileFrom supply (.for_ init cond postBlock body)).code →
      RelAt
        (Assembly.Program.pcAfter
          (pre ++ (Block.compileFrom (LabelSupply.next supply) init).code))
        target source →
      For.Eval fuel cond postBlock body source final →
      ARun
        (pre ++
          (Stmt.compileFrom supply (.for_ init cond postBlock body)).code ++
          suffix)
        target
        (fun target' =>
          RelAt
            (Assembly.Program.pcAfter
              (pre ++
                (Stmt.compileFrom supply
                  (.for_ init cond postBlock body)).code))
            target' final) := by
  intro pre suffix fuel source target final hLabels hFits hRel hEval
  induction fuel generalizing source target final with
  | zero =>
      cases hEval
  | succ fuel ih =>
      cases hEval with
      | false hCond =>
          exact
            forLoop_false (supply := supply) (init := init)
              (postBlock := postBlock) (body := body) (cond := cond)
              hLabels hFits hRel hCond
      | true hCond hBodyEval hPostEval hLoopEval =>
          exact
            forLoop_true_step (supply := supply) (init := init)
              (postBlock := postBlock) (body := body) (cond := cond)
              hBody hPost hLabels hFits hRel hCond hBodyEval hPostEval
              (fun targetAfterPost hRelAfterPost =>
                ih hRelAfterPost hLoopEval)

theorem for_ {supply : LabelSupply}
    {init postBlock body : Block} {cond : Code}
    (hInit : BlockPreserves (LabelSupply.next supply) init)
    (hBody : BlockPreserves
      (Block.compileFrom (LabelSupply.next supply) init).next body)
    (hPost :
      BlockPreserves
        (Block.compileFrom
          (Block.compileFrom (LabelSupply.next supply) init).next body).next
        postBlock) :
    StmtPreserves supply (.for_ init cond postBlock body) := by
  intro pre suffix fuel source target final hLabels hFits hRel hEval
  cases hEval with
  | for_ hInitEval hLoopEval =>
      rename_i _fuel stateAfterInit
      let loopLabel := LabelSupply.label supply 0
      let bodyLabel := LabelSupply.label supply 1
      let endLabel := LabelSupply.label supply 2
      let compiledInit := Block.compileFrom (LabelSupply.next supply) init
      let compiledBody := Block.compileFrom compiledInit.next body
      let compiledPost := Block.compileFrom compiledBody.next postBlock
      have hFitsFull :
          AssemblyProgram.PCFitsFrom pre
            (compiledInit.code ++ [Assembly.Instr.label loopLabel] ++
              cond.toAssembly ++
              [ Assembly.Instr.jumpi bodyLabel
              , Assembly.Instr.jump endLabel
              , Assembly.Instr.label bodyLabel
              ] ++
              compiledBody.code ++ compiledPost.code ++
              [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel]) := by
        simpa [Stmt.compileFrom, loopLabel, bodyLabel, endLabel,
          compiledInit, compiledBody, compiledPost, LabelSupply.next,
          List.append_assoc] using hFits
      have hInitFits :
          AssemblyProgram.PCFitsFrom pre compiledInit.code :=
        AssemblyProgram.PCFitsFrom.left
          (pre := pre) (first := compiledInit.code)
          (second :=
            [Assembly.Instr.label loopLabel] ++ cond.toAssembly ++
              [ Assembly.Instr.jumpi bodyLabel
              , Assembly.Instr.jump endLabel
              , Assembly.Instr.label bodyLabel
              ] ++
              compiledBody.code ++ compiledPost.code ++
              [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel])
          (by simpa [List.append_assoc] using hFitsFull)
      have hInitLabels :
          AssemblyProgram.labelsLt (LabelSupply.next supply) pre :=
        AssemblyProgram.labelsLt_mono (Nat.le_succ supply) hLabels
      have hInitRun :=
        hInit (pre := pre)
          (post :=
            [Assembly.Instr.label loopLabel] ++ cond.toAssembly ++
              [ Assembly.Instr.jumpi bodyLabel
              , Assembly.Instr.jump endLabel
              , Assembly.Instr.label bodyLabel
              ] ++
              compiledBody.code ++ compiledPost.code ++
              [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel] ++
              suffix)
          hInitLabels hInitFits hRel hInitEval
      refine
        ARun.bind
          (program := pre ++
            (Stmt.compileFrom supply (.for_ init cond postBlock body)).code ++
            suffix)
          (middle := fun targetAfterInit =>
            RelAt
              (Assembly.Program.pcAfter (pre ++ compiledInit.code))
              targetAfterInit stateAfterInit)
          ?_ ?_
      · simpa [Stmt.compileFrom, loopLabel, bodyLabel, endLabel,
          compiledInit, compiledBody, compiledPost, LabelSupply.next,
          List.append_assoc] using hInitRun
      · intro targetAfterInit hRelAfterInit
        have hLoopRun :=
          forLoop (supply := supply) (init := init)
            (postBlock := postBlock) (body := body) (cond := cond)
            hBody hPost
            (pre := pre) (suffix := suffix)
            hLabels hFits hRelAfterInit hLoopEval
        simpa [Stmt.compileFrom, loopLabel, bodyLabel, endLabel,
          compiledInit, compiledBody, compiledPost, LabelSupply.next,
          List.append_assoc] using hLoopRun

end StmtPreserves

namespace BlockPreserves

theorem nil (supply : LabelSupply) :
    BlockPreserves supply { stmts := [] } := by
  intro pre post fuel source target final _hLabels _hFits hRel hEval
  cases hEval with
  | nil =>
      refine ARun.pure ?_
      simpa [Block.compileFrom] using hRel

theorem cons {supply : LabelSupply} {stmt : Stmt} {rest : List Stmt}
    (hStmt : StmtPreserves supply stmt)
    (hRest :
      BlockPreserves (Stmt.compileFrom supply stmt).next { stmts := rest }) :
    BlockPreserves supply { stmts := stmt :: rest } := by
  intro pre post fuel source target final hLabels hFits hRel hEval
  cases hEval with
  | cons hStmtEval hRestEval =>
      rename_i _fuel mid
      let compiledStmt := Stmt.compileFrom supply stmt
      let compiledRest := Block.compileFrom compiledStmt.next { stmts := rest }
      have hFits' :
          AssemblyProgram.PCFitsFrom pre
            (compiledStmt.code ++ compiledRest.code) := by
        simpa [Block.compileFrom, CompileResult.append,
          compiledStmt, compiledRest] using hFits
      have hStmtFits :
          AssemblyProgram.PCFitsFrom pre compiledStmt.code :=
        AssemblyProgram.PCFitsFrom.left
          (pre := pre) (first := compiledStmt.code)
          (second := compiledRest.code) hFits'
      have hRestFits :
          AssemblyProgram.PCFitsFrom (pre ++ compiledStmt.code)
            compiledRest.code :=
        AssemblyProgram.PCFitsFrom.right
          (pre := pre) (first := compiledStmt.code)
          (second := compiledRest.code) hFits'
      have hRestLabels :
          AssemblyProgram.labelsLt compiledStmt.next
            (pre ++ compiledStmt.code) := by
        apply AssemblyProgram.labelsLt_append
        · exact
            AssemblyProgram.labelsLt_mono
              (CompilerFacts.stmt_compileFrom_next_ge stmt supply)
              hLabels
        · simpa [compiledStmt] using
            CompilerFacts.stmt_compileFrom_labelsLt stmt supply
      refine
        ARun.bind
          (program := pre ++ (Block.compileFrom supply { stmts := stmt :: rest }).code ++ post)
          (middle := fun targetAfterStmt =>
            RelAt (Assembly.Program.pcAfter (pre ++ compiledStmt.code))
              targetAfterStmt mid)
          ?_ ?_
      · have hStmtRun :=
          hStmt (pre := pre) (post := compiledRest.code ++ post)
            hLabels hStmtFits hRel hStmtEval
        simpa [Block.compileFrom, CompileResult.append,
          compiledStmt, compiledRest, List.append_assoc] using hStmtRun
      · intro targetAfterStmt hRelAfterStmt
        have hRestRun :=
          hRest (pre := pre ++ compiledStmt.code) (post := post)
            hRestLabels hRestFits hRelAfterStmt hRestEval
        simpa [Block.compileFrom, CompileResult.append,
          compiledStmt, compiledRest, List.append_assoc] using hRestRun

end BlockPreserves

namespace CompilerPreservation

theorem block :
    ∀ block supply, BlockPreserves supply block :=
  Block.rec
    (motive_1 := fun block => ∀ supply, BlockPreserves supply block)
    (motive_2 := fun stmt => ∀ supply, StmtPreserves supply stmt)
    (motive_3 := fun stmts =>
      ∀ supply, BlockPreserves supply { stmts := stmts })
    (fun _stmts ih supply => ih supply)
    (fun code supply => StmtPreserves.code supply code)
    (fun cond thenBody elseBody ihThen ihElse supply => by
      exact
        StmtPreserves.ifElse
          (supply := supply) (cond := cond)
          (thenBody := thenBody) (elseBody := elseBody)
          (ihThen (Block.compileFrom (LabelSupply.next supply) elseBody).next)
          (ihElse (LabelSupply.next supply)))
    (fun init cond postBlock body ihInit ihPost ihBody supply => by
      exact
        StmtPreserves.for_
          (supply := supply) (init := init) (postBlock := postBlock)
          (body := body) (cond := cond)
          (ihInit (LabelSupply.next supply))
          (ihBody (Block.compileFrom (LabelSupply.next supply) init).next)
          (ihPost
            (Block.compileFrom
              (Block.compileFrom (LabelSupply.next supply) init).next body).next))
    (fun supply => BlockPreserves.nil supply)
    (fun head _tail ihHead ihTail supply =>
      BlockPreserves.cons (ihHead supply)
        (ihTail (Stmt.compileFrom supply head).next))

theorem stmt :
    ∀ stmt supply, StmtPreserves supply stmt :=
  Stmt.rec
    (motive_1 := fun block => ∀ supply, BlockPreserves supply block)
    (motive_2 := fun stmt => ∀ supply, StmtPreserves supply stmt)
    (motive_3 := fun stmts =>
      ∀ supply, BlockPreserves supply { stmts := stmts })
    (fun _stmts ih supply => ih supply)
    (fun code supply => StmtPreserves.code supply code)
    (fun cond thenBody elseBody ihThen ihElse supply => by
      exact
        StmtPreserves.ifElse
          (supply := supply) (cond := cond)
          (thenBody := thenBody) (elseBody := elseBody)
          (ihThen (Block.compileFrom (LabelSupply.next supply) elseBody).next)
          (ihElse (LabelSupply.next supply)))
    (fun init cond postBlock body ihInit ihPost ihBody supply => by
      exact
        StmtPreserves.for_
          (supply := supply) (init := init) (postBlock := postBlock)
          (body := body) (cond := cond)
          (ihInit (LabelSupply.next supply))
          (ihBody (Block.compileFrom (LabelSupply.next supply) init).next)
          (ihPost
            (Block.compileFrom
              (Block.compileFrom (LabelSupply.next supply) init).next body).next))
    (fun supply => BlockPreserves.nil supply)
    (fun head _tail ihHead ihTail supply =>
      BlockPreserves.cons (ihHead supply)
        (ihTail (Stmt.compileFrom supply head).next))

end CompilerPreservation

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

noncomputable def assemblyReplayOfRun {program : Program} {fuel : Nat}
    {initial sourceFinal : EVMState}
    (hEntryPc : initial.pc = Assembly.Program.pcAfter ([] : Assembly.Program))
    (hFits : AssemblyProgram.PCFitsFrom ([] : Assembly.Program) program.compile)
    (hRun : Program.run fuel program initial = .ok sourceFinal) :
    AssemblyReplay program fuel initial sourceFinal := by
  classical
  have hEval := Program.eval_of_run hRun
  have hPres :=
    CompilerPreservation.block program.body 0
      (pre := []) (post := []) (fuel := fuel)
      (source := initial) (target := initial) (final := sourceFinal)
      (AssemblyProgram.labelsLt_nil 0)
      (by simpa [Program.compile, Block.compile] using hFits)
      (RelAt.entry hEntryPc)
      hEval
  let assemblyFuel := Classical.choose hPres
  let hPresFuel := Classical.choose_spec hPres
  let assemblyFinal := Classical.choose hPresFuel
  let hPresFinal := Classical.choose_spec hPresFuel
  exact
    { assemblyFuel := assemblyFuel
      assemblyFinal := assemblyFinal
      sourceRun := hRun
      assemblyRun := by
        change
          Assembly.Source.runN program.compile (Classical.choose hPres) initial =
            .ok (Classical.choose (Classical.choose_spec hPres))
        simpa [Program.compile, Block.compile] using hPresFinal.1
      projected := hPresFinal.2.sameData }

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

theorem compile_preserves {program : Program} {fuel : Nat}
    {initial sourceFinal : EVMState}
    (hEntryPc : initial.pc = Assembly.Program.pcAfter ([] : Assembly.Program))
    (hFits : AssemblyProgram.PCFitsFrom ([] : Assembly.Program) program.compile)
    (hRun : Program.run fuel program initial = .ok sourceFinal) :
    Program.run fuel program initial = .ok sourceFinal ∧
      ∃ assemblyFuel assemblyFinal,
        Assembly.Source.runN program.compile assemblyFuel initial = .ok assemblyFinal ∧
          eraseControl assemblyFinal = eraseControl sourceFinal := by
  exact
    compile_preserves_from_replay
      (assemblyReplayOfRun hEntryPc hFits hRun)

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
            Assembly.GasOracleAssumption program.compile initial ∧
              Assembly.OutOfGasPolicyAssumption program.compile initial ∧
                Assembly.CurrentContractProjectionAssumption program.compile initial ∧
                  ∃ assemblyFinal targetFinal,
                    Assembly.Preservation.BlockTrace program.compile target
                      replay.assemblyFuel initial targetFinal ∧
                      Assembly.eraseGas targetFinal =
                        Assembly.eraseGas assemblyFinal ∧
                      eraseControl assemblyFinal = eraseControl structuredFinal := by
  obtain
    ⟨hAccepted, hBytes, hEncoding, hNoGas,
      hGasOracle, hOutOfGas, hProjection,
      targetFinal, hTrace, hErase⟩ :=
    Assembly.compile_whole_program_sound hCompile hRuntime replay.assemblyRun
  exact
    ⟨hAccepted, hBytes, hEncoding, hNoGas,
      hGasOracle, hOutOfGas, hProjection,
      replay.assemblyFinal, targetFinal, hTrace, hErase, replay.projected⟩

theorem compile_whole_program_sound_of_run {program : Program}
    {target : Assembly.TargetProgram} {fuel : Nat}
    {initial structuredFinal : EVMState}
    (hCompile : Assembly.compile? program.compile = some target)
    (hRuntime : Assembly.RuntimeAssumptions program.compile target initial)
    (hEntryPc : initial.pc = Assembly.Program.pcAfter ([] : Assembly.Program))
    (hFits : AssemblyProgram.PCFitsFrom ([] : Assembly.Program) program.compile)
    (hRun : Program.run fuel program initial = .ok structuredFinal) :
    Assembly.Accepted program.compile ∧
      Assembly.Bytecode.compileBytes? program.compile =
        some (Assembly.Bytecode.encodeTarget target) ∧
        Assembly.Bytecode.EncodingCorrect target (Assembly.Bytecode.encodeTarget target) ∧
          target.GasOpcodeAbsent ∧
            Assembly.GasOracleAssumption program.compile initial ∧
              Assembly.OutOfGasPolicyAssumption program.compile initial ∧
                Assembly.CurrentContractProjectionAssumption program.compile initial ∧
                  ∃ assemblyFinal targetFinal,
                    Assembly.Preservation.BlockTrace program.compile target
                      (assemblyReplayOfRun hEntryPc hFits hRun).assemblyFuel
                      initial targetFinal ∧
                      Assembly.eraseGas targetFinal =
                        Assembly.eraseGas assemblyFinal ∧
                      eraseControl assemblyFinal =
                        eraseControl structuredFinal := by
  exact
    compile_whole_program_sound hCompile hRuntime
      (assemblyReplayOfRun hEntryPc hFits hRun)

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

theorem compile_whole_program_X_bridge_of_run {program : Program}
    {target : Assembly.TargetProgram} {fuel : Nat}
    {initial structuredFinal : EVMState}
    (hCompile : Assembly.compile? program.compile = some target)
    (hRuntime : Assembly.RuntimeAssumptions program.compile target initial)
    (hEntryPc : initial.pc = Assembly.Program.pcAfter ([] : Assembly.Program))
    (hFits : AssemblyProgram.PCFitsFrom ([] : Assembly.Program) program.compile)
    (hRun : Program.run fuel program initial = .ok structuredFinal)
    (hPreconditions :
      Assembly.GasAware.XPreconditionAssumptions target initial
        (assemblyReplayOfRun hEntryPc hFits hRun).assemblyFinal) :
    Assembly.GasAware.XBridgeCertificate program.compile target
      (assemblyReplayOfRun hEntryPc hFits hRun).assemblyFuel initial
      (assemblyReplayOfRun hEntryPc hFits hRun).assemblyFinal ∧
      eraseControl
        (assemblyReplayOfRun hEntryPc hFits hRun).assemblyFinal =
        eraseControl structuredFinal := by
  exact
    compile_whole_program_X_bridge hCompile hRuntime
      (assemblyReplayOfRun hEntryPc hFits hRun)
      hPreconditions

end Structured
end EvmCompiler
