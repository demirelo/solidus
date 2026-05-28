import EvmCompiler.Structured.Preservation
import EvmCompiler.Structured.GasParametric

namespace EvmCompiler
namespace Structured
namespace Preservation

namespace GasParametric

theorem sourceRunNResultWithGasOracle_append_running
    {program : Assembly.Program} {oracle : GasOracle}
    {firstFuel secondFuel cursor cursorMid cursorFinal : Nat}
    {state mid : EVMState} {result : Assembly.StepResult}
    (hFirst :
      Assembly.GasParametric.sourceRunNResultWithGasOracle program oracle
          firstFuel cursor state =
        .ok (.running mid, cursorMid))
    (hSecond :
      Assembly.GasParametric.sourceRunNResultWithGasOracle program oracle
          secondFuel cursorMid mid =
        .ok (result, cursorFinal)) :
    Assembly.GasParametric.sourceRunNResultWithGasOracle program oracle
        (firstFuel + secondFuel) cursor state =
      .ok (result, cursorFinal) := by
  induction firstFuel generalizing cursor state with
  | zero =>
      simp [Assembly.GasParametric.sourceRunNResultWithGasOracle] at hFirst
      rcases hFirst with ⟨hResult, hCursor⟩
      cases hResult
      cases hCursor
      simpa [Assembly.GasParametric.sourceRunNResultWithGasOracle] using hSecond
  | succ firstFuel ih =>
      unfold Assembly.GasParametric.sourceRunNResultWithGasOracle at hFirst
      cases hStep :
          Assembly.GasParametric.sourceStepResultWithGasOracle program oracle
            cursor state with
      | error err =>
          rw [hStep] at hFirst
          cases hFirst
      | ok stepPair =>
          rcases stepPair with ⟨stepResult, cursorAfterStep⟩
          rw [hStep] at hFirst
          cases stepResult with
          | running stateAfterStep =>
              change
                Assembly.GasParametric.sourceRunNResultWithGasOracle program
                    oracle firstFuel cursorAfterStep stateAfterStep =
                  Except.ok (.running mid, cursorMid) at hFirst
              have hFuel :
                  firstFuel + 1 + secondFuel =
                    firstFuel + secondFuel + 1 := by
                rw [Nat.add_assoc]
                rw [Nat.add_comm 1 secondFuel]
                rw [← Nat.add_assoc]
              rw [hFuel]
              unfold Assembly.GasParametric.sourceRunNResultWithGasOracle
              rw [hStep]
              exact ih hFirst
          | halted halt =>
              cases hFirst

def ARunResultWithGasOracle (program : Assembly.Program) (oracle : GasOracle)
    (cursor : Nat) (state : EVMState)
    (post : Assembly.StepResult → Nat → Prop) : Prop :=
  ∃ fuel result cursorFinal,
    Assembly.GasParametric.sourceRunNResultWithGasOracle program oracle fuel
        cursor state =
      .ok (result, cursorFinal) ∧
      post result cursorFinal

namespace ARunResultWithGasOracle

theorem pure {program : Assembly.Program} {oracle : GasOracle}
    {cursor : Nat} {state : EVMState}
    {post : Assembly.StepResult → Nat → Prop}
    (hPost : post (.running state) cursor) :
    ARunResultWithGasOracle program oracle cursor state post := by
  exact
    ⟨0, .running state, cursor,
      by simp [Assembly.GasParametric.sourceRunNResultWithGasOracle],
      hPost⟩

theorem bind_running {program : Assembly.Program} {oracle : GasOracle}
    {cursor : Nat} {state : EVMState}
    {middle : EVMState → Nat → Prop}
    {post : Assembly.StepResult → Nat → Prop}
    (hRun :
      ARunResultWithGasOracle program oracle cursor state
        (fun result cursorMid =>
          match result with
          | .running mid => middle mid cursorMid
          | .halted _ => False))
    (hNext :
      ∀ mid cursorMid, middle mid cursorMid →
        ARunResultWithGasOracle program oracle cursorMid mid post) :
    ARunResultWithGasOracle program oracle cursor state post := by
  rcases hRun with
    ⟨firstFuel, firstResult, cursorMid, hFirst, hMiddleResult⟩
  cases firstResult with
  | halted halt =>
      cases hMiddleResult
  | running mid =>
      rcases hNext mid cursorMid hMiddleResult with
        ⟨secondFuel, result, cursorFinal, hSecond, hPost⟩
      exact
        ⟨firstFuel + secondFuel, result, cursorFinal,
          sourceRunNResultWithGasOracle_append_running hFirst hSecond,
          hPost⟩

theorem mono {program : Assembly.Program} {oracle : GasOracle}
    {cursor : Nat} {state : EVMState}
    {post₁ post₂ : Assembly.StepResult → Nat → Prop}
    (hRun : ARunResultWithGasOracle program oracle cursor state post₁)
    (hPost : ∀ result cursorFinal, post₁ result cursorFinal →
      post₂ result cursorFinal) :
    ARunResultWithGasOracle program oracle cursor state post₂ := by
  rcases hRun with ⟨fuel, result, cursorFinal, hRun, hResult⟩
  exact ⟨fuel, result, cursorFinal, hRun, hPost result cursorFinal hResult⟩

theorem cast_program {oldProgram newProgram : Assembly.Program}
    {oracle : GasOracle} {cursor : Nat} {state : EVMState}
    {post : Assembly.StepResult → Nat → Prop}
    (hEq : oldProgram = newProgram)
    (hRun : ARunResultWithGasOracle oldProgram oracle cursor state post) :
    ARunResultWithGasOracle newProgram oracle cursor state post := by
  cases hEq
  exact hRun

theorem cast_program_mono {oldProgram newProgram : Assembly.Program}
    {oracle : GasOracle} {cursor : Nat} {state : EVMState}
    {post₁ post₂ : Assembly.StepResult → Nat → Prop}
    (hEq : oldProgram = newProgram)
    (hRun : ARunResultWithGasOracle oldProgram oracle cursor state post₁)
    (hPost : ∀ result cursorFinal, post₁ result cursorFinal →
      post₂ result cursorFinal) :
    ARunResultWithGasOracle newProgram oracle cursor state post₂ :=
  mono (cast_program hEq hRun) hPost

end ARunResultWithGasOracle

namespace BasicInstr

def ControlSafeWithGasOracle (instr : BasicInstr) : Prop :=
  ∀ {oracle : GasOracle} {cursor : Nat}
      {source target source' : EVMState} {cursor' : Nat},
    eraseControl target = eraseControl source →
      instr.stepWithGasOracle oracle cursor source = .ok (source', cursor') →
        ∃ target',
          instr.stepWithGasOracle oracle cursor target = .ok (target', cursor') ∧
            eraseControl target' = eraseControl source'

def StepPCWithGasOracle (instr : BasicInstr) : Prop :=
  ∀ {oracle : GasOracle} {cursor cursor' : Nat}
      {state final : EVMState},
    instr.stepWithGasOracle oracle cursor state = .ok (final, cursor') →
      final.pc =
        state.pc + EvmYul.UInt256.ofNat instr.toAssembly.byteSize

structure RunnerSafeWithGasOracle (instr : BasicInstr) : Prop where
  controlSafe : ControlSafeWithGasOracle instr
  stepPC : StepPCWithGasOracle instr

theorem controlSafeWithGasOracle_of_plain {instr : BasicInstr}
    (hSafe : Preservation.BasicInstr.RunnerSafe instr)
    (hPlain :
      ∀ (oracle : GasOracle) (cursor : Nat) (state : EVMState),
        instr.stepWithGasOracle oracle cursor state =
          (do
            let state' ← instr.step state
            pure (state', cursor))) :
    ControlSafeWithGasOracle instr := by
  intro oracle cursor source target source' cursor' hEq hStep
  rw [hPlain oracle cursor source] at hStep
  cases hSourceStep : instr.step source with
  | error err =>
      rw [hSourceStep] at hStep
      cases hStep
  | ok sourcePlain =>
      rw [hSourceStep] at hStep
      cases hStep
      obtain ⟨target', hTargetStep, hTargetEq⟩ :=
        hSafe.controlSafe hEq hSourceStep
      refine ⟨target', ?_, hTargetEq⟩
      rw [hPlain oracle cursor target, hTargetStep]
      rfl

theorem stepPCWithGasOracle_of_plain {instr : BasicInstr}
    (hSafe : Preservation.BasicInstr.RunnerSafe instr)
    (hPlain :
      ∀ (oracle : GasOracle) (cursor : Nat) (state : EVMState),
        instr.stepWithGasOracle oracle cursor state =
          (do
            let state' ← instr.step state
            pure (state', cursor))) :
    StepPCWithGasOracle instr := by
  intro oracle cursor cursor' state final hStep
  rw [hPlain oracle cursor state] at hStep
  cases hPlainStep : instr.step state with
  | error err =>
      rw [hPlainStep] at hStep
      cases hStep
  | ok plainFinal =>
      rw [hPlainStep] at hStep
      cases hStep
      exact hSafe.stepPC hPlainStep

theorem gas_controlSafeWithGasOracle :
    ControlSafeWithGasOracle (.op .gas) := by
  intro oracle cursor source target source' cursor' hEq hStep
  simp [BasicInstr.stepWithGasOracle, BasicOp.stepWithGasOracle,
    Assembly.GasParametric.Target.stepInstrWithGasOracle,
    Assembly.GasParametric.PrimOp.stepWithGasOracle] at hStep
  cases hStep
  refine
    ⟨target.replaceStackAndIncrPC
        (target.stack.push (oracle cursor)), ?_, ?_⟩
  · simp [BasicInstr.stepWithGasOracle, BasicOp.stepWithGasOracle,
      BasicOp.toPrimOp,
      Assembly.GasParametric.Target.stepInstrWithGasOracle,
      Assembly.GasParametric.PrimOp.stepWithGasOracle]
  · exact
      eraseControl_replaceStackAndIncrPC_of_eq hEq
        (by rw [stack_eq_of_eraseControl_eq hEq])

theorem gas_stepPCWithGasOracle :
    StepPCWithGasOracle (.op .gas) := by
  intro oracle cursor cursor' state final hStep
  simp [BasicInstr.stepWithGasOracle, BasicOp.stepWithGasOracle,
    Assembly.GasParametric.Target.stepInstrWithGasOracle,
    Assembly.GasParametric.PrimOp.stepWithGasOracle] at hStep
  cases hStep
  simp [BasicInstr.toAssembly, Assembly.Instr.byteSize,
    EvmYul.EVM.State.replaceStackAndIncrPC, EvmYul.EVM.State.incrPC]

theorem gas_runnerSafeWithGasOracle :
    RunnerSafeWithGasOracle (.op .gas) := by
  exact ⟨gas_controlSafeWithGasOracle, gas_stepPCWithGasOracle⟩

theorem runnerSafeWithGasOracle_of_runnerSafe {instr : BasicInstr}
    (hSafe : Preservation.BasicInstr.RunnerSafe instr) :
    RunnerSafeWithGasOracle instr := by
  constructor
  · cases instr with
    | push value =>
        exact
          controlSafeWithGasOracle_of_plain hSafe
            (by
              intro oracle cursor state
              rfl)
    | op op =>
        cases op <;>
          first
          | exact gas_controlSafeWithGasOracle
          | exact
              controlSafeWithGasOracle_of_plain hSafe
                (by
                  intro oracle cursor state
                  rfl)
  · cases instr with
    | push value =>
        exact
          stepPCWithGasOracle_of_plain hSafe
            (by
              intro oracle cursor state
              rfl)
    | op op =>
        cases op <;>
          first
          | exact gas_stepPCWithGasOracle
          | exact
              stepPCWithGasOracle_of_plain hSafe
                (by
                  intro oracle cursor state
                  rfl)

def PlainFrameSafe (instr : BasicInstr) : Prop :=
  ∀ (state final : EVMState) (hidden : EvmYul.Stack Word),
    instr.step state = .ok final →
      instr.step { state with stack := state.stack ++ hidden } =
        .ok { final with stack := final.stack ++ hidden }

def FrameSafeWithGasOracle (instr : BasicInstr) : Prop :=
  ∀ (oracle : GasOracle) (cursor cursor' : Nat)
      (state final : EVMState) (hidden : EvmYul.Stack Word),
    instr.stepWithGasOracle oracle cursor state = .ok (final, cursor') →
      instr.stepWithGasOracle oracle cursor
          { state with stack := state.stack ++ hidden } =
        .ok ({ final with stack := final.stack ++ hidden }, cursor')

theorem push_frameSafeWithGasOracle (value : Word) :
    FrameSafeWithGasOracle (.push value) := by
  intro oracle cursor cursor' state final hidden hStep
  simp [BasicInstr.stepWithGasOracle,
    Assembly.GasParametric.Target.stepInstrWithGasOracle,
    Assembly.Target.stepInstr, EvmYul.Stack.push] at hStep
  rcases hStep with ⟨hFinal, hCursor⟩
  cases hFinal
  cases hCursor
  simp [BasicInstr.stepWithGasOracle,
    Assembly.GasParametric.Target.stepInstrWithGasOracle,
    Assembly.Target.stepInstr, EvmYul.Stack.push,
    EvmYul.EVM.State.replaceStackAndIncrPC, EvmYul.EVM.State.incrPC]

theorem gas_frameSafeWithGasOracle :
    FrameSafeWithGasOracle (.op .gas) := by
  intro oracle cursor cursor' state final hidden hStep
  simp [BasicInstr.stepWithGasOracle,
    BasicOp.stepWithGasOracle,
    Assembly.GasParametric.Target.stepInstrWithGasOracle,
    Assembly.GasParametric.PrimOp.stepWithGasOracle,
    BasicOp.toPrimOp, EvmYul.Stack.push] at hStep
  rcases hStep with ⟨hFinal, hCursor⟩
  cases hFinal
  cases hCursor
  simp [BasicInstr.stepWithGasOracle, BasicOp.stepWithGasOracle,
    Assembly.GasParametric.Target.stepInstrWithGasOracle,
    Assembly.GasParametric.PrimOp.stepWithGasOracle,
    BasicOp.toPrimOp, EvmYul.Stack.push,
    EvmYul.EVM.State.replaceStackAndIncrPC, EvmYul.EVM.State.incrPC]

theorem frameSafeWithGasOracle_of_plainFrameSafe {instr : BasicInstr}
    (hFrame : PlainFrameSafe instr)
    (hPlain :
      ∀ (oracle : GasOracle) (cursor : Nat) (state : EVMState),
        instr.stepWithGasOracle oracle cursor state =
          (do
            let state' ← instr.step state
            pure (state', cursor))) :
    FrameSafeWithGasOracle instr := by
  intro oracle cursor cursor' state final hidden hStep
  rw [hPlain oracle cursor state] at hStep
  cases hPlainStep : instr.step state with
  | error err =>
      rw [hPlainStep] at hStep
      cases hStep
  | ok plainFinal =>
      rw [hPlainStep] at hStep
      cases hStep
      rw [hPlain oracle cursor { state with stack := state.stack ++ hidden }]
      rw [hFrame state _ hidden hPlainStep]
      rfl

theorem plainFrameSafe_of_singleton_frameSafe {instr : BasicInstr}
    (hFrame : Code.FrameSafe [instr]) :
    PlainFrameSafe instr := by
  intro state final hidden hStep
  have hRun : Code.run [instr] state = .ok final := by
    simp [Code.run, hStep, Bind.bind, Except.bind]
  have hHidden := hFrame state final hidden hRun
  cases hHiddenStep :
      instr.step { state with stack := state.stack ++ hidden } with
  | error err =>
      simp [Code.run, hHiddenStep, Bind.bind, Except.bind] at hHidden
  | ok hiddenFinal =>
      simp [Code.run, hHiddenStep, Bind.bind, Except.bind] at hHidden
      cases hHidden
      rfl

theorem pop_plainFrameSafe :
    PlainFrameSafe (.op .pop) :=
  plainFrameSafe_of_singleton_frameSafe Preservation.Code.pop_frameSafe

theorem pop_frameSafeWithGasOracle :
    FrameSafeWithGasOracle (.op .pop) :=
  frameSafeWithGasOracle_of_plainFrameSafe pop_plainFrameSafe
    (by intro oracle cursor state; rfl)

theorem invalid_plainFrameSafe :
    PlainFrameSafe (.op .invalid) := by
  intro state final hidden hStep
  unfold BasicInstr.step BasicOp.step at hStep
  simp [BasicOp.toPrimOp, Assembly.Target.stepInstr,
    Assembly.PrimOp.step, Assembly.PrimOp.continuingStep?,
    Assembly.PrimStep.run] at hStep

theorem invalid_frameSafeWithGasOracle :
    FrameSafeWithGasOracle (.op .invalid) :=
  frameSafeWithGasOracle_of_plainFrameSafe invalid_plainFrameSafe
    (by intro oracle cursor state; rfl)

theorem dup1_plainFrameSafe :
    PlainFrameSafe (.op .dup1) := by
  intro state final hidden hStep
  unfold BasicInstr.step BasicOp.step at hStep ⊢
  simp [BasicOp.toPrimOp, Assembly.Target.stepInstr,
    Assembly.PrimOp.step, Assembly.PrimOp.continuingStep?,
    Assembly.PrimStep.run] at hStep ⊢
  cases hStack : state.stack with
  | nil =>
      simp [EvmYul.dup, hStack] at hStep
  | cons top rest =>
      simp [EvmYul.dup, hStack, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC] at hStep ⊢
      cases hStep
      simp

theorem dup1_frameSafeWithGasOracle :
    FrameSafeWithGasOracle (.op .dup1) :=
  frameSafeWithGasOracle_of_plainFrameSafe dup1_plainFrameSafe
    (by intro oracle cursor state; rfl)

theorem eq_plainFrameSafe :
    PlainFrameSafe (.op .eq) := by
  intro state final hidden hStep
  unfold BasicInstr.step BasicOp.step at hStep ⊢
  simp [BasicOp.toPrimOp, Assembly.Target.stepInstr,
    Assembly.PrimOp.step, Assembly.PrimOp.continuingStep?,
    Assembly.PrimStep.run, EvmYul.EVM.execBinOp, Id.run] at hStep ⊢
  cases hStack : state.stack with
  | nil =>
      simp [EvmYul.Stack.pop2, hStack] at hStep
  | cons a rest1 =>
      cases hRest1 : rest1 with
      | nil =>
          simp [EvmYul.Stack.pop2, hStack, hRest1] at hStep
      | cons b rest =>
          simp [EvmYul.Stack.pop2, hStack, hRest1, EvmYul.Stack.push,
            EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC] at hStep ⊢
          cases hStep
          simp

theorem eq_frameSafeWithGasOracle :
    FrameSafeWithGasOracle (.op .eq) :=
  frameSafeWithGasOracle_of_plainFrameSafe eq_plainFrameSafe
    (by intro oracle cursor state; rfl)

theorem source_stepAtWithGasOracle_eq_stepWithGasOracle
    {instr : BasicInstr} {program : Assembly.Program} {pc : Nat}
    {oracle : GasOracle} {cursor : Nat} {state : EVMState} :
    Assembly.GasParametric.sourceStepAtWithGasOracle program pc
        instr.toAssembly oracle cursor state =
      (do
        let (state', cursor') ←
          instr.stepWithGasOracle oracle cursor state
        pure (.running state', cursor')) := by
  cases instr with
  | push value =>
      rfl
  | op op =>
      cases op <;> rfl

theorem source_stepResult_ctx_relAt_of_relAt_withGasOracle
    {instr : BasicInstr}
    {pre post : Assembly.Program}
    {source target source' : EVMState}
    {oracle : GasOracle} {cursor cursor' : Nat}
    (hSafe : RunnerSafeWithGasOracle instr)
    (hFit : PCFits pre)
    (hRel : RelAt (Assembly.Program.pcAfter pre) target source)
    (hStep : instr.stepWithGasOracle oracle cursor source =
      .ok (source', cursor')) :
    ∃ target',
      Assembly.GasParametric.sourceStepResultWithGasOracle
          (pre ++ instr.toAssembly :: post) oracle cursor target =
        .ok (.running target', cursor') ∧
        RelAt (Assembly.Program.pcAfter (pre ++ [instr.toAssembly]))
          target' source' := by
  obtain ⟨target', hTargetStep, hEq⟩ :=
    hSafe.controlSafe hRel.sameData hStep
  refine ⟨target', ?_, ?_, hEq⟩
  · unfold Assembly.GasParametric.sourceStepResultWithGasOracle
    have hAt :
        Assembly.Program.instrAtPc (pre ++ instr.toAssembly :: post)
            target.pc.toNat =
          some (Assembly.Program.byteLength pre, instr.toAssembly) := by
      unfold Assembly.Program.instrAtPc
      rw [hRel.pc_eq, hFit]
      simpa using
        Assembly.Program.instrAtPcFrom_append_boundary_cons
          pre post instr.toAssembly 0
    simp [hAt, source_stepAtWithGasOracle_eq_stepWithGasOracle,
      hTargetStep]
  · calc
      target'.pc
          = target.pc + EvmYul.UInt256.ofNat instr.toAssembly.byteSize :=
              hSafe.stepPC hTargetStep
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

namespace Code

inductive RunnerSafeWithGasOracle : Code → Prop where
  | nil : RunnerSafeWithGasOracle []
  | cons {instr : BasicInstr} {rest : Code}
      (hInstr : BasicInstr.RunnerSafeWithGasOracle instr)
      (hRest : RunnerSafeWithGasOracle rest) :
      RunnerSafeWithGasOracle (instr :: rest)

theorem runnerSafeWithGasOracle_of_runnerSafe {code : Code}
    (hSafe : Preservation.Code.RunnerSafe code) :
    RunnerSafeWithGasOracle code := by
  induction hSafe with
  | nil =>
      exact RunnerSafeWithGasOracle.nil
  | cons hInstr hRest ih =>
      exact
        RunnerSafeWithGasOracle.cons
          (BasicInstr.runnerSafeWithGasOracle_of_runnerSafe hInstr) ih

def FrameSafeWithGasOracle (code : Code) : Prop :=
  ∀ (oracle : GasOracle) (cursor cursor' : Nat)
      (state final : EVMState) (hidden : EvmYul.Stack Word),
    Code.runWithGasOracle code oracle cursor state = .ok (final, cursor') →
      Code.runWithGasOracle code oracle cursor
          { state with stack := state.stack ++ hidden } =
        .ok ({ final with stack := final.stack ++ hidden }, cursor')

inductive InstrFrameSafeWithGasOracle : Code → Prop where
  | nil : InstrFrameSafeWithGasOracle []
  | cons {instr : BasicInstr} {rest : Code}
      (hInstr : BasicInstr.FrameSafeWithGasOracle instr)
      (hRest : InstrFrameSafeWithGasOracle rest) :
      InstrFrameSafeWithGasOracle (instr :: rest)

theorem frameSafeWithGasOracle_of_instrFrameSafeWithGasOracle {code : Code}
    (hFrame : InstrFrameSafeWithGasOracle code) :
    FrameSafeWithGasOracle code := by
  induction hFrame with
  | nil =>
      intro oracle cursor cursor' state final hidden hRun
      simp [Code.runWithGasOracle] at hRun ⊢
      rcases hRun with ⟨hFinal, hCursor⟩
      cases hFinal
      cases hCursor
      simp
  | cons hInstrFrame hRestFrame ih =>
      rename_i instr rest
      intro oracle cursor cursor' state final hidden hRun
      unfold Code.runWithGasOracle at hRun ⊢
      cases hStep :
          instr.stepWithGasOracle oracle cursor state with
      | error err =>
          rw [hStep] at hRun
          cases hRun
      | ok stepPair =>
          rcases stepPair with ⟨mid, cursorMid⟩
          rw [hStep] at hRun
          have hHiddenStep :
              instr.stepWithGasOracle oracle cursor
                  { state with stack := state.stack ++ hidden } =
                .ok ({ mid with stack := mid.stack ++ hidden }, cursorMid) :=
            hInstrFrame oracle cursor cursorMid state mid hidden hStep
          rw [hHiddenStep]
          simpa [Bind.bind, Except.bind] using
            ih oracle cursorMid cursor' mid final hidden hRun

theorem pop_instrFrameSafeWithGasOracle :
    InstrFrameSafeWithGasOracle [BasicInstr.op .pop] := by
  exact
    InstrFrameSafeWithGasOracle.cons
      BasicInstr.pop_frameSafeWithGasOracle
      InstrFrameSafeWithGasOracle.nil

theorem pop_frameSafeWithGasOracle :
    FrameSafeWithGasOracle [BasicInstr.op .pop] :=
  frameSafeWithGasOracle_of_instrFrameSafeWithGasOracle
    pop_instrFrameSafeWithGasOracle

theorem switchTestCode_instrFrameSafeWithGasOracle (value : Word) :
    InstrFrameSafeWithGasOracle (Stmt.switchTestCode value) := by
  exact
    InstrFrameSafeWithGasOracle.cons
      BasicInstr.dup1_frameSafeWithGasOracle
      (InstrFrameSafeWithGasOracle.cons
        (BasicInstr.push_frameSafeWithGasOracle value)
        (InstrFrameSafeWithGasOracle.cons
          BasicInstr.eq_frameSafeWithGasOracle
          InstrFrameSafeWithGasOracle.nil))

theorem switchTestCode_frameSafeWithGasOracle (value : Word) :
    FrameSafeWithGasOracle (Stmt.switchTestCode value) :=
  frameSafeWithGasOracle_of_instrFrameSafeWithGasOracle
    (switchTestCode_instrFrameSafeWithGasOracle value)

theorem source_runResult_ctx_relAt_of_relAt_withGasOracle {code : Code}
    {pre post : Assembly.Program}
    {source target source' : EVMState}
    {oracle : GasOracle} {cursor cursor' : Nat}
    (hSafe : RunnerSafeWithGasOracle code)
    (hFits : Preservation.Code.PCFitsFrom pre code)
    (hRel : RelAt (Assembly.Program.pcAfter pre) target source)
    (hRun : Code.runWithGasOracle code oracle cursor source =
      .ok (source', cursor')) :
    ARunResultWithGasOracle (pre ++ code.toAssembly ++ post) oracle cursor target
      (fun result cursorFinal =>
        match result with
        | .running target' =>
            cursorFinal = cursor' ∧
              RelAt (Assembly.Program.pcAfter (pre ++ code.toAssembly))
                target' source'
        | .halted _ => False) := by
  induction code generalizing pre source target cursor with
  | nil =>
      simp [Code.runWithGasOracle] at hRun
      rcases hRun with ⟨hSourceEq, hCursorEq⟩
      cases hSourceEq
      cases hCursorEq
      refine ARunResultWithGasOracle.pure ?_
      constructor
      · rfl
      · simpa [Code.toAssembly, Assembly.Program.byteLength_append,
          Assembly.Program.pcAfter] using hRel
  | cons instr rest ih =>
      cases hSafe with
      | cons hInstr hRest =>
          unfold Code.runWithGasOracle at hRun
          cases hStep :
              instr.stepWithGasOracle oracle cursor source with
          | error err =>
              rw [hStep] at hRun
              cases hRun
          | ok stepPair =>
              rcases stepPair with ⟨sourceMid, cursorMid⟩
              rw [hStep] at hRun
              rcases hFits with ⟨hFitHere, hFitsRest⟩
              obtain ⟨targetMid, hAssemblyStep, hRelMid⟩ :=
                BasicInstr.source_stepResult_ctx_relAt_of_relAt_withGasOracle
                  (instr := instr) (pre := pre)
                  (post := Code.toAssembly rest ++ post)
                  hInstr hFitHere hRel hStep
              refine
                ARunResultWithGasOracle.bind_running
                  (program := pre ++ Code.toAssembly (instr :: rest) ++ post)
                  (middle := fun stateAfterInstr cursorAfterInstr =>
                    cursorAfterInstr = cursorMid ∧
                      RelAt
                        (Assembly.Program.pcAfter
                          (pre ++ [instr.toAssembly]))
                        stateAfterInstr sourceMid)
                  ?_ ?_
              · refine ⟨1, .running targetMid, cursorMid, ?_, ?_⟩
                · change
                    Assembly.GasParametric.sourceRunNResultWithGasOracle
                        (pre ++ Code.toAssembly (instr :: rest) ++ post)
                        oracle 1 cursor target =
                      Except.ok (.running targetMid, cursorMid)
                  rw [show
                      pre ++ Code.toAssembly (instr :: rest) ++ post =
                        pre ++ instr.toAssembly ::
                          (Code.toAssembly rest ++ post) by
                        simp [Code.toAssembly, List.append_assoc]]
                  unfold Assembly.GasParametric.sourceRunNResultWithGasOracle
                  rw [hAssemblyStep]
                  rfl
                · exact ⟨rfl, hRelMid⟩
              · intro stateAfterInstr cursorAfterInstr hStateAfterInstr
                rcases hStateAfterInstr with ⟨hCursorEq, hRelAfterInstr⟩
                subst cursorAfterInstr
                change
                  Code.runWithGasOracle rest oracle cursorMid sourceMid =
                    Except.ok (source', cursor') at hRun
                have hRestRun :=
                  ih (pre := pre ++ [instr.toAssembly])
                    hRest hFitsRest hRelAfterInstr hRun
                simpa [Code.toAssembly, List.append_assoc] using hRestRun

end Code

mutual
  inductive Block.FrameSafeWithGasOracle : Block → Prop where
    | nil : Block.FrameSafeWithGasOracle { stmts := [] }
    | cons {stmt : Stmt} {rest : List Stmt}
        (hStmt : Stmt.FrameSafeWithGasOracle stmt)
        (hRest : Block.FrameSafeWithGasOracle { stmts := rest }) :
        Block.FrameSafeWithGasOracle { stmts := stmt :: rest }

  inductive Stmt.FrameSafeWithGasOracle : Stmt → Prop where
    | code {code : Code} (hCode : Code.FrameSafeWithGasOracle code) :
        Stmt.FrameSafeWithGasOracle (.code code)
    | if_ {cond : Code} {body : Block}
        (hCond : Code.FrameSafeWithGasOracle cond)
        (hBody : Block.FrameSafeWithGasOracle body) :
        Stmt.FrameSafeWithGasOracle (.if_ cond body)
    | switch {scrutinee : Code} {cases : List (Word × Block)}
        {defaultBody : Option Block}
        (hScrutinee : Code.FrameSafeWithGasOracle scrutinee)
        (hCases :
          ∀ value body, (value, body) ∈ cases →
            Block.FrameSafeWithGasOracle body)
        (hDefault :
          ∀ body, defaultBody = some body →
            Block.FrameSafeWithGasOracle body) :
        Stmt.FrameSafeWithGasOracle (.switch scrutinee cases defaultBody)
    | for_ {init post body : Block} {cond : Code}
        (hInit : Block.FrameSafeWithGasOracle init)
        (hCond : Code.FrameSafeWithGasOracle cond)
        (hPost : Block.FrameSafeWithGasOracle post)
        (hBody : Block.FrameSafeWithGasOracle body) :
        Stmt.FrameSafeWithGasOracle (.for_ init cond post body)
    | brk : Stmt.FrameSafeWithGasOracle .brk
    | cont : Stmt.FrameSafeWithGasOracle .cont
    | leave : Stmt.FrameSafeWithGasOracle .leave
    | call {name : Name} : Stmt.FrameSafeWithGasOracle (.call name)
    | terminal {kind : Assembly.HaltKind} :
        Stmt.FrameSafeWithGasOracle (.terminal kind)
end

namespace Proc

def FrameSafeWithGasOracle (proc : Proc) : Prop :=
  Block.FrameSafeWithGasOracle proc.body

end Proc

namespace ProcList

def FrameSafeWithGasOracle : List Proc → Prop
  | [] => True
  | proc :: rest => Proc.FrameSafeWithGasOracle proc ∧
      FrameSafeWithGasOracle rest

theorem FrameSafeWithGasOracle_of_lookup? {procs : List Proc}
    {name : Name} {proc : Proc}
    (hSafe : FrameSafeWithGasOracle procs)
    (hLookup :
      EvmCompiler.Structured.ProcList.lookup? name procs = some proc) :
    Proc.FrameSafeWithGasOracle proc := by
  induction procs with
  | nil =>
      simp [EvmCompiler.Structured.ProcList.lookup?] at hLookup
  | cons head rest ih =>
      unfold EvmCompiler.Structured.ProcList.lookup? at hLookup
      by_cases hName : head.name = name
      · simp [hName] at hLookup
        cases hLookup
        exact hSafe.1
      · simp [hName] at hLookup
        exact ih hSafe.2 hLookup

end ProcList

namespace Program

def FrameSafeWithGasOracle (program : EvmCompiler.Structured.Program) :
    Prop :=
  ProcList.FrameSafeWithGasOracle program.procs ∧
    Block.FrameSafeWithGasOracle program.body

theorem procFrameSafeWithGasOracle_of_lookup?
    {program : EvmCompiler.Structured.Program} {name : Name} {proc : Proc}
    (hSafe : FrameSafeWithGasOracle program)
    (hLookup :
      EvmCompiler.Structured.ProcList.lookup? name program.procs = some proc) :
    Proc.FrameSafeWithGasOracle proc :=
  ProcList.FrameSafeWithGasOracle_of_lookup? hSafe.1 hLookup

structure AcceptedWithGasOracle
    (program : EvmCompiler.Structured.Program) : Prop where
  accepted : EvmCompiler.Structured.Preservation.Program.Accepted program
  oracleFrame : FrameSafeWithGasOracle program

namespace AcceptedWithGasOracle

theorem plainAccepted {program : EvmCompiler.Structured.Program}
    (hAccepted : AcceptedWithGasOracle program) :
    EvmCompiler.Structured.Preservation.Program.Accepted program :=
  hAccepted.accepted

end AcceptedWithGasOracle

noncomputable def frameSafeWithGasOracleChecked
    (program : EvmCompiler.Structured.Program) : Bool := by
  classical
  exact decide (FrameSafeWithGasOracle program)

theorem frameSafeWithGasOracle_of_check
    {program : EvmCompiler.Structured.Program}
    (h : frameSafeWithGasOracleChecked program = true) :
    FrameSafeWithGasOracle program := by
  unfold frameSafeWithGasOracleChecked at h
  classical
  exact of_decide_eq_true h

theorem frameSafeWithGasOracle_check_of
    {program : EvmCompiler.Structured.Program}
    (h : FrameSafeWithGasOracle program) :
    frameSafeWithGasOracleChecked program = true := by
  unfold frameSafeWithGasOracleChecked
  classical
  exact decide_eq_true h

noncomputable def acceptedWithGasOracle
    (program : EvmCompiler.Structured.Program) : Bool :=
  EvmCompiler.Structured.Preservation.Program.accepted program &&
    frameSafeWithGasOracleChecked program

theorem acceptedWithGasOracle_of_check
    {program : EvmCompiler.Structured.Program}
    (h : acceptedWithGasOracle program = true) :
    AcceptedWithGasOracle program := by
  unfold acceptedWithGasOracle at h
  cases hAcceptedChecked :
      EvmCompiler.Structured.Preservation.Program.accepted program <;>
    cases hOracleFrameChecked : frameSafeWithGasOracleChecked program <;>
      simp [hAcceptedChecked, hOracleFrameChecked] at h
  exact
    ⟨ EvmCompiler.Structured.Preservation.Program.accepted_of_check
        hAcceptedChecked
    , frameSafeWithGasOracle_of_check hOracleFrameChecked
    ⟩

theorem acceptedWithGasOracle_check_of
    {program : EvmCompiler.Structured.Program}
    (h : AcceptedWithGasOracle program) :
    acceptedWithGasOracle program = true := by
  unfold acceptedWithGasOracle
  rw [EvmCompiler.Structured.Preservation.Program.accepted_check_of
      h.accepted,
    frameSafeWithGasOracle_check_of h.oracleFrame]
  rfl

end Program

namespace AssemblyControl

theorem label_stepResult_ctx_relAt_of_relAt_withGasOracle
    {label : Assembly.Label}
    {pre post : Assembly.Program} {source target : EVMState}
    {oracle : GasOracle} {cursor : Nat}
    (hFit : PCFits pre)
    (hRel : RelAt (Assembly.Program.pcAfter pre) target source) :
    ∃ target',
      Assembly.GasParametric.sourceStepResultWithGasOracle
          (pre ++ [Assembly.Instr.label label] ++ post) oracle cursor
          target =
        .ok (.running target', cursor) ∧
        RelAt (Assembly.Program.pcAfter (pre ++ [Assembly.Instr.label label]))
          target' source := by
  refine ⟨target.incrPC, ?_, ?_, ?_⟩
  · unfold Assembly.GasParametric.sourceStepResultWithGasOracle
    have hAt :
        Assembly.Program.instrAtPc
            (pre ++ [Assembly.Instr.label label] ++ post)
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

theorem jump_stepResult_ctx_relAt_of_relAt_withGasOracle
    {label : Assembly.Label} {dest : Nat}
    {pre post : Assembly.Program} {source target : EVMState}
    {oracle : GasOracle} {cursor : Nat}
    (hFit : PCFits pre)
    (hRel : RelAt (Assembly.Program.pcAfter pre) target source)
    (hLabel :
      Assembly.Program.labelPc (pre ++ [Assembly.Instr.jump label] ++ post)
        label = some dest) :
    ∃ target',
      Assembly.GasParametric.sourceStepResultWithGasOracle
          (pre ++ [Assembly.Instr.jump label] ++ post) oracle cursor target =
        .ok (.running target', cursor) ∧
        RelAt (EvmYul.UInt256.ofNat dest) target' source := by
  refine ⟨Assembly.Source.jumpPc dest target, ?_, rfl, ?_⟩
  · unfold Assembly.GasParametric.sourceStepResultWithGasOracle
    have hAt :
        Assembly.Program.instrAtPc
            (pre ++ [Assembly.Instr.jump label] ++ post) target.pc.toNat =
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
    unfold Assembly.GasParametric.sourceStepAtWithGasOracle
    simp [hLabel', Assembly.Source.invalid, Assembly.Source.jumpPc,
      Assembly.Instr.haltKind?]
    rfl
  · simpa [SameData, Assembly.Source.jumpPc, eraseControl_with_pc] using
      hRel.sameData

theorem jumpi_stepResult_ctx_relAt_of_popCondition_withGasOracle
    {label : Assembly.Label} {dest : Nat}
    {pre post : Assembly.Program}
    {source target source' : EVMState} {condTrue : Bool}
    {oracle : GasOracle} {cursor : Nat}
    (hFit : PCFits pre)
    (hRel : RelAt (Assembly.Program.pcAfter pre) target source)
    (hLabel :
      Assembly.Program.labelPc (pre ++ [Assembly.Instr.jumpi label] ++ post)
        label = some dest)
    (hPop : Code.popCondition source = .ok (source', condTrue)) :
    ∃ target',
      Assembly.GasParametric.sourceStepResultWithGasOracle
          (pre ++ [Assembly.Instr.jumpi label] ++ post) oracle cursor
          target =
        .ok (.running target', cursor) ∧
        RelAt
          (if condTrue then
            EvmYul.UInt256.ofNat dest
          else
            Assembly.Program.pcAfter (pre ++ [Assembly.Instr.jumpi label]))
          target' source' := by
  unfold Code.popCondition at hPop
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
      have hLabel' :
          Assembly.Program.labelPc (pre ++ Assembly.Instr.jumpi label :: post)
            label = some dest := by
        simpa using hLabel
      unfold Assembly.GasParametric.sourceStepResultWithGasOracle
      rw [hAt]
      unfold Assembly.GasParametric.sourceStepAtWithGasOracle
      simp [hLabel', Assembly.Source.invalid, hTargetPop]
      by_cases hCond : cond != EvmYul.UInt256.ofNat 0
      · simp [hCond]
        refine
          ⟨{ target with pc := EvmYul.UInt256.ofNat dest, stack := rest },
            rfl, ?_, ?_⟩
        · rfl
        calc
          eraseControl
                { target with pc := EvmYul.UInt256.ofNat dest, stack := rest }
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
          ⟨{ target with
              pc := Assembly.Source.jumpiFallthroughPc target
              stack := rest },
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
          eraseControl
                { target with
                  pc := Assembly.Source.jumpiFallthroughPc target
                  stack := rest }
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

end AssemblyControl

namespace Code

theorem runCondition_jumpi_result_ctx_relAt_of_relAt_withGasOracle
    {cond : Code} {label : Assembly.Label} {dest : Nat}
    {pre post : Assembly.Program}
    {source target source' : EVMState} {condTrue : Bool}
    {oracle : GasOracle} {cursor cursor' : Nat}
    (hSafe : RunnerSafeWithGasOracle cond)
    (hFits : Preservation.Code.PCFitsFrom pre cond)
    (hRel : RelAt (Assembly.Program.pcAfter pre) target source)
    (hLabel :
      Assembly.Program.labelPc
          (pre ++ cond.toAssembly ++ [Assembly.Instr.jumpi label] ++ post)
          label = some dest)
    (hRun :
      Code.runConditionWithGasOracle cond oracle cursor source =
        .ok (source', condTrue, cursor')) :
    ARunResultWithGasOracle
      (pre ++ cond.toAssembly ++ [Assembly.Instr.jumpi label] ++ post)
      oracle cursor target
      (fun result cursorFinal =>
        match result with
        | .running target' =>
            cursorFinal = cursor' ∧
              RelAt
                (if condTrue then
                  EvmYul.UInt256.ofNat dest
                else
                  Assembly.Program.pcAfter
                    (pre ++ cond.toAssembly ++ [Assembly.Instr.jumpi label]))
                target' source'
        | .halted _ => False) := by
  unfold Code.runConditionWithGasOracle at hRun
  cases hCode :
      Code.runWithGasOracle cond oracle cursor source with
  | error _err =>
      rw [hCode] at hRun
      cases hRun
  | ok codeResult =>
      rcases codeResult with ⟨sourceAfterCode, cursorAfterCode⟩
      rw [hCode] at hRun
      cases hPop : Code.popCondition sourceAfterCode with
      | error _err =>
          simp [hPop, Bind.bind, Except.bind] at hRun
      | ok popResult =>
          rcases popResult with ⟨sourceAfterPop, condResult⟩
          simp [hPop, Bind.bind, Except.bind] at hRun
          rcases hRun with ⟨hSource, hCond, hCursor⟩
          subst source'
          subst condTrue
          subst cursor'
          refine
            ARunResultWithGasOracle.bind_running
              (program :=
                pre ++ cond.toAssembly ++ [Assembly.Instr.jumpi label] ++ post)
              (middle := fun targetAfterCode cursorAfterCode' =>
                cursorAfterCode' = cursorAfterCode ∧
                  RelAt (Assembly.Program.pcAfter (pre ++ cond.toAssembly))
                    targetAfterCode sourceAfterCode)
              ?_ ?_
          · have hCodeRun :=
              source_runResult_ctx_relAt_of_relAt_withGasOracle
                (code := cond) (pre := pre)
                (post := [Assembly.Instr.jumpi label] ++ post)
                hSafe hFits hRel hCode
            simpa [List.append_assoc] using hCodeRun
          · intro targetAfterCode cursorAfterCode' hAfterCode
            rcases hAfterCode with ⟨hCursorEq, hRelAfterCode⟩
            subst cursorAfterCode'
            have hLabel' :
                Assembly.Program.labelPc
                    ((pre ++ cond.toAssembly) ++
                      [Assembly.Instr.jumpi label] ++ post) label =
                  some dest := by
              simpa [List.append_assoc] using hLabel
            obtain ⟨targetAfterJump, hJumpStep, hRelAfterJump⟩ :=
              AssemblyControl.jumpi_stepResult_ctx_relAt_of_popCondition_withGasOracle
                (label := label) (dest := dest)
                (pre := pre ++ cond.toAssembly) (post := post)
                (Preservation.Code.PCFitsFrom.end hFits) hRelAfterCode
                hLabel' hPop
            refine ⟨1, .running targetAfterJump, cursorAfterCode, ?_, ?_⟩
            · change
                Assembly.GasParametric.sourceRunNResultWithGasOracle
                    (pre ++ cond.toAssembly ++
                      [Assembly.Instr.jumpi label] ++ post)
                    oracle 1 cursorAfterCode targetAfterCode =
                  Except.ok (.running targetAfterJump, cursorAfterCode)
              rw [show
                  pre ++ cond.toAssembly ++ [Assembly.Instr.jumpi label] ++
                      post =
                    (pre ++ cond.toAssembly) ++ [Assembly.Instr.jumpi label] ++
                      post by
                    simp [List.append_assoc]]
              unfold Assembly.GasParametric.sourceRunNResultWithGasOracle
              rw [hJumpStep]
              rfl
            · exact ⟨rfl, by simpa [List.append_assoc] using hRelAfterJump⟩

end Code

def SourceLocalNoGasInstr : Assembly.Instr → Prop
  | .prim .gas => False
  | .jump _ | .jumpi _ => False
  | _ => True

theorem primOp_stepWithGasOracle_noGas_eq_step
    {op : Assembly.PrimOp} {oracle : GasOracle} {cursor : Nat}
    {state : EVMState}
    (hNoGas : op ≠ .gas) :
    Assembly.GasParametric.PrimOp.stepWithGasOracle oracle cursor op state =
      (do
        let state' ← op.step state
        Except.ok (state', cursor)) := by
  unfold Assembly.GasParametric.PrimOp.stepWithGasOracle
  split
  · exact (hNoGas rfl).elim
  · cases hStep : op.step state <;> rfl

theorem sourceStepAtWithGasOracle_local_noGas_eq_targetInstr
    {instr : Assembly.Instr}
    {program : Assembly.Program} {pc : Nat} {oracle : GasOracle}
    {cursor : Nat} {state : EVMState}
    (hLocal : SourceLocalNoGasInstr instr) :
    Assembly.GasParametric.sourceStepAtWithGasOracle program pc instr
        oracle cursor state =
      (do
        let state' ←
          Assembly.Target.stepInstr
            (_root_.EvmCompiler.Structured.Preservation.StackShuffle.targetInstr
              instr)
            state
        match instr.haltKind? with
        | some kind =>
            Except.ok
              (Assembly.StepResult.halted
                { kind := kind
                  state := state'
                  output := kind.output state' },
                cursor)
        | none =>
            Except.ok (Assembly.StepResult.running state', cursor)) := by
  cases instr with
  | label _ =>
      rfl
  | prim op =>
      have hNoGas : op ≠ .gas := by
        intro h
        cases h
        exact hLocal
      simp only [Assembly.GasParametric.sourceStepAtWithGasOracle]
      rw [primOp_stepWithGasOracle_noGas_eq_step
        (oracle := oracle) (cursor := cursor) (state := state) hNoGas]
      simp [
        _root_.EvmCompiler.Structured.Preservation.StackShuffle.targetInstr,
        Assembly.Target.stepInstr, Bind.bind, Except.bind]
      cases hStep : op.step state with
      | error err =>
          simp
      | ok state' =>
          cases hKind : (Assembly.Instr.prim op).haltKind? <;> rfl
  | push _ =>
      rfl
  | jump _ =>
      cases hLocal
  | jumpi _ =>
      cases hLocal

theorem source_stepResult_local_withGasOracle {instr : Assembly.Instr}
    {pre post : Assembly.Program} {state final : EVMState}
    {oracle : GasOracle} {cursor : Nat}
    (hLocal : SourceLocalNoGasInstr instr)
    (hNoHalt : instr.haltKind? = none)
    (hFit : PCFits pre)
    (hPc : state.pc = Assembly.Program.pcAfter pre)
    (hStep :
      Assembly.Target.stepInstr
          (_root_.EvmCompiler.Structured.Preservation.StackShuffle.targetInstr instr) state =
        .ok final) :
    Assembly.GasParametric.sourceStepResultWithGasOracle
        (pre ++ [instr] ++ post) oracle cursor state =
      .ok (.running final, cursor) := by
  unfold Assembly.GasParametric.sourceStepResultWithGasOracle
  have hAt :
      Assembly.Program.instrAtPc (pre ++ [instr] ++ post) state.pc.toNat =
        some (Assembly.Program.byteLength pre, instr) := by
    unfold Assembly.Program.instrAtPc
    rw [hPc, hFit]
    simpa using
      Assembly.Program.instrAtPcFrom_append_boundary_cons pre post instr 0
  rw [hAt]
  change
    Assembly.GasParametric.sourceStepAtWithGasOracle
        (pre ++ [instr] ++ post) (Assembly.Program.byteLength pre) instr
        oracle cursor state =
      .ok (.running final, cursor)
  rw [sourceStepAtWithGasOracle_local_noGas_eq_targetInstr
    (program := pre ++ [instr] ++ post)
    (pc := Assembly.Program.byteLength pre) (oracle := oracle)
    (cursor := cursor) (state := state) hLocal]
  rw [hStep]
  simp [hNoHalt, Bind.bind, Except.bind]

theorem swapInstr_sourceLocalNoGas {n : Nat}
    (hOne : 1 ≤ n) (hBound : n ≤ 16) :
    SourceLocalNoGasInstr (StackShuffle.swapInstr n) := by
  have hCases :
      n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨
      n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨
      n = 13 ∨ n = 14 ∨ n = 15 ∨ n = 16 := by
    omega
  rcases hCases with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst n <;> simp [StackShuffle.swapInstr, SourceLocalNoGasInstr]

theorem dupInstr_sourceLocalNoGas {n : Nat}
    (hOne : 1 ≤ n) (hBound : n ≤ 16) :
    SourceLocalNoGasInstr (StackShuffle.dupInstr n) := by
  have hCases :
      n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨
      n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨
      n = 13 ∨ n = 14 ∨ n = 15 ∨ n = 16 := by
    omega
  rcases hCases with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst n <;> simp [StackShuffle.dupInstr, SourceLocalNoGasInstr]

namespace StackShuffleGas

theorem sinkTopUnder_source_exists_withGasOracle {state : EVMState}
    {args suffix : List Word} {token : Word}
    {pre post : Assembly.Program} {oracle : GasOracle} {cursor : Nat}
    (hFits :
      AssemblyProgram.PCFitsFrom pre
        (StackShuffle.sinkTopUnder args.length))
    (hPc :
      ({ state with stack := token :: args ++ suffix }).pc =
        Assembly.Program.pcAfter pre)
    (hBound : args.length ≤ 16) :
    ARunResultWithGasOracle
      (pre ++ StackShuffle.sinkTopUnder args.length ++ post) oracle cursor
      { state with stack := token :: args ++ suffix }
      (fun result cursorFinal =>
        match result with
        | .running final =>
            cursorFinal = cursor ∧
              final.stack = args ++ token :: suffix ∧
              eraseControl final =
                eraseControl { state with stack := args ++ token :: suffix } ∧
              final.pc =
                Assembly.Program.pcAfter
                  (pre ++ StackShuffle.sinkTopUnder args.length)
        | .halted _ => False) := by
  induction args using List.reverseRecOn generalizing state suffix token pre with
  | nil =>
      refine ARunResultWithGasOracle.pure ?_
      exact ⟨rfl, by simpa [StackShuffle.sinkTopUnder] using hPc⟩
  | append_singleton front last ih =>
      have hSwapBound : front.length + 1 ≤ 16 := by
        simpa [List.length_append] using hBound
      have hFrontBound : front.length ≤ 16 := by omega
      let swap := StackShuffle.swapInstr (front.length + 1)
      let start : EVMState :=
        { state with stack := token :: front ++ [last] ++ suffix }
      let mid : EVMState :=
        start.replaceStackAndIncrPC (last :: front ++ [token] ++ suffix)
      have hStep :
          Assembly.Target.stepInstr
              (_root_.EvmCompiler.Structured.Preservation.StackShuffle.targetInstr swap)
              start =
            .ok mid := by
        rw [show swap = StackShuffle.swapInstr (front.length + 1) from rfl]
        rw [_root_.EvmCompiler.Structured.Preservation.StackShuffle.swapInstr_step_eq_swap
          (by omega) hSwapBound]
        exact _root_.EvmCompiler.Structured.Preservation.StackShuffle.swap_snoc
          (state := state) (front := front)
          (suffix := suffix) (top := token) (last := last)
      have hSwapLocal : SourceLocalNoGasInstr swap := by
        have hCases :
            front.length + 1 = 1 ∨ front.length + 1 = 2 ∨
            front.length + 1 = 3 ∨ front.length + 1 = 4 ∨
            front.length + 1 = 5 ∨ front.length + 1 = 6 ∨
            front.length + 1 = 7 ∨ front.length + 1 = 8 ∨
            front.length + 1 = 9 ∨ front.length + 1 = 10 ∨
            front.length + 1 = 11 ∨ front.length + 1 = 12 ∨
            front.length + 1 = 13 ∨ front.length + 1 = 14 ∨
            front.length + 1 = 15 ∨ front.length + 1 = 16 := by
          omega
        dsimp [swap]
        rcases hCases with
          h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
          rw [h] <;>
          simp [StackShuffle.swapInstr, SourceLocalNoGasInstr]
      have hSwapNoHalt : swap.haltKind? = none := by
        exact
          _root_.EvmCompiler.Structured.Preservation.StackShuffle.swapInstr_haltKind?_none
            (n := front.length + 1) (by omega) hSwapBound
      have hSwapByte : swap.byteSize = 1 := by
        exact
          _root_.EvmCompiler.Structured.Preservation.StackShuffle.swapInstr_byteSize
            (n := front.length + 1) (by omega) hSwapBound
      have hFitsCons :
          PCFits pre ∧
            AssemblyProgram.PCFitsFrom (pre ++ [swap])
              (StackShuffle.sinkTopUnder front.length) := by
        simpa [StackShuffle.sinkTopUnder, List.length_append, swap,
          List.append_assoc] using hFits
      have hFirstFit : PCFits pre := by
        exact hFitsCons.1
      have hFirst :
          ARunResultWithGasOracle
            (pre ++ StackShuffle.sinkTopUnder (front ++ [last]).length ++ post)
            oracle cursor start
            (fun result cursorAfterSwap =>
              match result with
              | .running targetAfterSwap =>
                  cursorAfterSwap = cursor ∧
                    targetAfterSwap = mid ∧
                    targetAfterSwap.pc =
                      Assembly.Program.pcAfter (pre ++ [swap])
              | .halted _ => False) := by
        refine ⟨1, .running mid, cursor, ?_, ?_⟩
        · rw [show
            pre ++ StackShuffle.sinkTopUnder (front ++ [last]).length ++ post =
              pre ++ [swap] ++
                (StackShuffle.sinkTopUnder front.length ++ post) by
              simp [StackShuffle.sinkTopUnder, List.length_append, swap,
                List.append_assoc]]
          unfold Assembly.GasParametric.sourceRunNResultWithGasOracle
          rw [source_stepResult_local_withGasOracle
            (instr := swap) (pre := pre)
            (post := StackShuffle.sinkTopUnder front.length ++ post)
            (state := start) (final := mid) (oracle := oracle)
            (cursor := cursor)
            hSwapLocal hSwapNoHalt hFirstFit
            (by simpa [start, List.append_assoc] using hPc)
            hStep]
          rfl
        · refine ⟨rfl, rfl, ?_⟩
          have hPcState : state.pc = Assembly.Program.pcAfter pre := by
            simpa [start, List.append_assoc] using hPc
          calc
            mid.pc
                = state.pc + EvmYul.UInt256.ofNat 1 := by
                    simp [mid, start, EvmYul.EVM.State.replaceStackAndIncrPC,
                      EvmYul.EVM.State.incrPC]
            _ = Assembly.Program.pcAfter pre + EvmYul.UInt256.ofNat 1 := by
                    rw [hPcState]
            _ = EvmYul.UInt256.ofNat (Assembly.Program.byteLength pre + 1) := by
                    rw [Assembly.Program.pcAfter, Assembly.UInt256_ofNat_add]
            _ = Assembly.Program.pcAfter (pre ++ [swap]) := by
                    simp [Assembly.Program.pcAfter,
                      Assembly.Program.byteLength_append,
                      Assembly.Program.byteLength, hSwapByte]
      refine
        ARunResultWithGasOracle.bind_running
          (program :=
            pre ++ StackShuffle.sinkTopUnder (front ++ [last]).length ++ post)
          (middle := fun targetAfterSwap cursorAfterSwap =>
            cursorAfterSwap = cursor ∧
              targetAfterSwap = mid ∧
              targetAfterSwap.pc = Assembly.Program.pcAfter (pre ++ [swap]))
          hFirst ?_
      intro targetAfterSwap cursorAfterSwap hAfterSwap
      rcases hAfterSwap with ⟨hCursorAfterSwap, hTargetAfterSwap, hPcAfterSwap⟩
      subst cursorAfterSwap
      cases hTargetAfterSwap
      have hRestFits :
          AssemblyProgram.PCFitsFrom (pre ++ [swap])
            (StackShuffle.sinkTopUnder front.length) := by
        exact hFitsCons.2
      have hMidStack : mid.stack = last :: front ++ token :: suffix := by
        simp [mid, start, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, List.append_assoc]
      have hMidRecord :
          { mid with stack := last :: (front ++ token :: suffix) } = mid := by
        rw [show last :: (front ++ token :: suffix) =
            last :: front ++ token :: suffix by rfl]
        rw [← hMidStack]
      have hRest :=
        ih (state := mid) (suffix := token :: suffix) (token := last)
          (pre := pre ++ [swap])
          hRestFits hPcAfterSwap hFrontBound
      exact ARunResultWithGasOracle.mono
        (by
          simpa [StackShuffle.sinkTopUnder, List.length_append, swap,
            hMidRecord, List.append_assoc] using hRest)
        (by
          intro result cursorFinal hResult
          cases result with
          | halted halt =>
              cases hResult
          | running final =>
              rcases hResult with
                ⟨hCursorFinal, hStack, hErase, hPcFinal⟩
              refine ⟨hCursorFinal, ?_, ?_, ?_⟩
              · simpa [List.append_assoc] using hStack
              · calc
                  eraseControl final
                      =
                    eraseControl
                      { mid with stack := front ++ [last] ++ token :: suffix } :=
                        by simpa [List.append_assoc] using hErase
                  _ =
                    eraseControl
                      { state with stack := front ++ [last] ++ token :: suffix } := by
                        simp [mid, start, eraseControl, Assembly.eraseGas,
                          EvmYul.EVM.State.replaceStackAndIncrPC,
                          EvmYul.EVM.State.incrPC]
              · simpa [StackShuffle.sinkTopUnder, List.length_append, swap,
                  List.append_assoc] using hPcFinal)

theorem callPrologue_source_exists_withGasOracle {state : EVMState}
    {args suffix : List Word} {token : Word}
    {pre post : Assembly.Program} {oracle : GasOracle} {cursor : Nat}
    (hFits :
      AssemblyProgram.PCFitsFrom pre
        ([Assembly.Instr.push token] ++ StackShuffle.sinkTopUnder args.length))
    (hPc :
      ({ state with stack := args ++ suffix }).pc =
        Assembly.Program.pcAfter pre)
    (hBound : args.length ≤ 16) :
    ARunResultWithGasOracle
      (pre ++
        ([Assembly.Instr.push token] ++ StackShuffle.sinkTopUnder args.length) ++
        post)
      oracle cursor
      { state with stack := args ++ suffix }
      (fun result cursorFinal =>
        match result with
        | .running final =>
            cursorFinal = cursor ∧
              final.stack = args ++ token :: suffix ∧
              eraseControl final =
                eraseControl { state with stack := args ++ token :: suffix } ∧
              final.pc =
                Assembly.Program.pcAfter
                  (pre ++
                    ([Assembly.Instr.push token] ++
                      StackShuffle.sinkTopUnder args.length))
        | .halted _ => False) := by
  let start : EVMState := { state with stack := args ++ suffix }
  let afterPush : EVMState :=
    start.replaceStackAndIncrPC (token :: args ++ suffix) (pcΔ := 33)
  have hPushStep :
      Assembly.Target.stepInstr
          (_root_.EvmCompiler.Structured.Preservation.StackShuffle.targetInstr
            (Assembly.Instr.push token)) start =
        .ok afterPush := by
    simp [_root_.EvmCompiler.Structured.Preservation.StackShuffle.targetInstr, start,
      afterPush,
      Assembly.Target.stepInstr, EvmYul.Stack.push,
      EvmYul.EVM.State.replaceStackAndIncrPC, EvmYul.EVM.State.incrPC]
  have hFirst :
      ARunResultWithGasOracle
        (pre ++
          ([Assembly.Instr.push token] ++ StackShuffle.sinkTopUnder args.length) ++
          post)
        oracle cursor start
        (fun result cursorAfterPush =>
          match result with
          | .running targetAfterPush =>
              cursorAfterPush = cursor ∧
                targetAfterPush = afterPush ∧
                targetAfterPush.pc =
                  Assembly.Program.pcAfter (pre ++ [Assembly.Instr.push token])
          | .halted _ => False) := by
    refine ⟨1, .running afterPush, cursor, ?_, ?_⟩
    · rw [show
        pre ++
            ([Assembly.Instr.push token] ++ StackShuffle.sinkTopUnder args.length) ++
            post =
          pre ++ [Assembly.Instr.push token] ++
            (StackShuffle.sinkTopUnder args.length ++ post) by
          simp [List.append_assoc]]
      unfold Assembly.GasParametric.sourceRunNResultWithGasOracle
      rw [source_stepResult_local_withGasOracle
        (instr := Assembly.Instr.push token) (pre := pre)
        (post := StackShuffle.sinkTopUnder args.length ++ post)
        (state := start) (final := afterPush) (oracle := oracle)
        (cursor := cursor)
        (by simp [SourceLocalNoGasInstr]) rfl hFits.1
        (by simpa [start] using hPc) hPushStep]
      rfl
    · refine ⟨rfl, rfl, ?_⟩
      have hPcState : state.pc = Assembly.Program.pcAfter pre := by
        simpa [start] using hPc
      calc
        afterPush.pc
            = state.pc + EvmYul.UInt256.ofNat 33 := by
                simp [afterPush, start,
                  EvmYul.EVM.State.replaceStackAndIncrPC,
                  EvmYul.EVM.State.incrPC]
        _ = Assembly.Program.pcAfter pre + EvmYul.UInt256.ofNat 33 := by
                rw [hPcState]
        _ = EvmYul.UInt256.ofNat (Assembly.Program.byteLength pre + 33) := by
                rw [Assembly.Program.pcAfter, Assembly.UInt256_ofNat_add]
        _ = Assembly.Program.pcAfter (pre ++ [Assembly.Instr.push token]) := by
                simp [Assembly.Program.pcAfter,
                  Assembly.Program.byteLength_append,
                  Assembly.Program.byteLength, Assembly.Instr.byteSize,
                  Assembly.Instr.push32Size]
  refine
    ARunResultWithGasOracle.bind_running
      (program :=
        pre ++
          ([Assembly.Instr.push token] ++ StackShuffle.sinkTopUnder args.length) ++
          post)
      (middle := fun targetAfterPush cursorAfterPush =>
        cursorAfterPush = cursor ∧
          targetAfterPush = afterPush ∧
          targetAfterPush.pc =
            Assembly.Program.pcAfter (pre ++ [Assembly.Instr.push token]))
      hFirst ?_
  intro targetAfterPush cursorAfterPush hAfterPush
  rcases hAfterPush with
    ⟨hCursorAfterPush, hTargetAfterPush, hPcAfterPush⟩
  subst cursorAfterPush
  cases hTargetAfterPush
  have hRest :=
    sinkTopUnder_source_exists_withGasOracle
      (state := afterPush) (args := args) (suffix := suffix)
      (token := token) (pre := pre ++ [Assembly.Instr.push token])
      (post := post) (oracle := oracle) (cursor := cursor)
      (by simpa [List.append_assoc] using hFits.2)
      hPcAfterPush hBound
  exact ARunResultWithGasOracle.mono
    (by simpa [List.append_assoc] using hRest)
    (by
      intro result cursorFinal hResult
      cases result with
      | halted halt =>
          cases hResult
      | running final =>
          rcases hResult with ⟨hCursorFinal, hStack, hErase, hPcFinal⟩
          refine ⟨hCursorFinal, hStack, ?_, ?_⟩
          · calc
              eraseControl final
                  = eraseControl { afterPush with stack := args ++ token :: suffix } :=
                    hErase
              _ = eraseControl { state with stack := args ++ token :: suffix } := by
                    simp [afterPush, start, eraseControl, Assembly.eraseGas,
                      EvmYul.EVM.State.replaceStackAndIncrPC,
                      EvmYul.EVM.State.incrPC]
          · simpa [List.append_assoc] using hPcFinal)

theorem liftBuriedToTop_source_exists_withGasOracle {state : EVMState}
    {front suffix : List Word} {token : Word}
    {pre post : Assembly.Program} {oracle : GasOracle} {cursor : Nat}
    (hFits :
      AssemblyProgram.PCFitsFrom pre
        (StackShuffle.liftBuriedToTop front.length))
    (hPc :
      ({ state with stack := front ++ token :: suffix }).pc =
        Assembly.Program.pcAfter pre)
    (hBound : front.length ≤ 16) :
    ARunResultWithGasOracle
      (pre ++ StackShuffle.liftBuriedToTop front.length ++ post) oracle cursor
      { state with stack := front ++ token :: suffix }
      (fun result cursorFinal =>
        match result with
        | .running final =>
            cursorFinal = cursor ∧
              final.stack = token :: front ++ suffix ∧
              eraseControl final =
                eraseControl { state with stack := token :: front ++ suffix } ∧
              final.pc =
                Assembly.Program.pcAfter
                  (pre ++ StackShuffle.liftBuriedToTop front.length)
        | .halted _ => False) := by
  induction front using List.reverseRecOn generalizing state suffix token pre post with
  | nil =>
      refine ARunResultWithGasOracle.pure ?_
      exact ⟨rfl, by simpa [StackShuffle.liftBuriedToTop] using hPc⟩
  | append_singleton front last ih =>
      have hSwapBound : front.length + 1 ≤ 16 := by
        simpa [List.length_append] using hBound
      have hFrontBound : front.length ≤ 16 := by omega
      let swap := StackShuffle.swapInstr (front.length + 1)
      have hCodeEq :
          StackShuffle.liftBuriedToTop (front ++ [last]).length =
            StackShuffle.liftBuriedToTop front.length ++ [swap] := by
        simp [StackShuffle.liftBuriedToTop, List.length_append, swap]
      have hCodeLenEq :
          StackShuffle.liftBuriedToTop (front.length + 1) =
            StackShuffle.liftBuriedToTop front.length ++ [swap] := by
        simpa [List.length_append] using hCodeEq
      have hFitsAppend :
          AssemblyProgram.PCFitsFrom pre
            (StackShuffle.liftBuriedToTop front.length ++ [swap]) := by
        simpa [hCodeEq] using hFits
      have hLiftFits :
          AssemblyProgram.PCFitsFrom pre
            (StackShuffle.liftBuriedToTop front.length) :=
        AssemblyProgram.PCFitsFrom.left hFitsAppend
      have hSwapFits :
          AssemblyProgram.PCFitsFrom
            (pre ++ StackShuffle.liftBuriedToTop front.length) [swap] :=
        AssemblyProgram.PCFitsFrom.right hFitsAppend
      have hLift :=
        ih (state := state) (suffix := token :: suffix) (token := last)
          (pre := pre) (post := [swap] ++ post)
          hLiftFits
          (by simpa [List.append_assoc] using hPc)
          hFrontBound
      refine
        ARunResultWithGasOracle.bind_running
          (program :=
            pre ++ StackShuffle.liftBuriedToTop (front ++ [last]).length ++ post)
          (middle := fun targetAfterLift cursorAfterLift =>
            cursorAfterLift = cursor ∧
              targetAfterLift.stack = last :: front ++ token :: suffix ∧
              eraseControl targetAfterLift =
                eraseControl { state with stack := last :: front ++ token :: suffix } ∧
              targetAfterLift.pc =
                Assembly.Program.pcAfter
                  (pre ++ StackShuffle.liftBuriedToTop front.length))
          ?_ ?_
      · exact ARunResultWithGasOracle.mono
          (by simpa [hCodeLenEq, List.append_assoc] using hLift)
          (by
            intro result cursorAfterLift hResult
            cases result with
            | halted halt =>
                cases hResult
            | running mid =>
                rcases hResult with
                  ⟨hCursorAfterLift, hStack, hErase, hPcMid⟩
                exact ⟨hCursorAfterLift,
                  by simpa [List.append_assoc] using hStack,
                  by simpa [List.append_assoc] using hErase, hPcMid⟩)
      · intro mid cursorAfterLift hMid
        rcases hMid with ⟨hCursorAfterLift, hMidStack, hMidErase, hMidPc⟩
        subst cursorAfterLift
        have hMidRecord :
            { mid with stack := last :: front ++ [token] ++ suffix } = mid := by
          rw [show last :: front ++ [token] ++ suffix =
              last :: front ++ token :: suffix by simp [List.append_assoc]]
          rw [← hMidStack]
        let finalState : EVMState :=
          mid.replaceStackAndIncrPC (token :: front ++ [last] ++ suffix)
        have hStep :
            Assembly.Target.stepInstr
                (_root_.EvmCompiler.Structured.Preservation.StackShuffle.targetInstr
                  swap)
                mid =
              .ok finalState := by
          rw [← hMidRecord]
          rw [show swap = StackShuffle.swapInstr (front.length + 1) from rfl]
          rw [_root_.EvmCompiler.Structured.Preservation.StackShuffle.swapInstr_step_eq_swap
            (by omega) hSwapBound]
          exact _root_.EvmCompiler.Structured.Preservation.StackShuffle.swap_snoc
            (state := mid) (front := front) (suffix := suffix)
            (top := last) (last := token)
        have hSwapLocal : SourceLocalNoGasInstr swap := by
          exact swapInstr_sourceLocalNoGas
            (n := front.length + 1) (by omega) hSwapBound
        have hSwapNoHalt : swap.haltKind? = none := by
          exact
            _root_.EvmCompiler.Structured.Preservation.StackShuffle.swapInstr_haltKind?_none
              (n := front.length + 1) (by omega) hSwapBound
        have hSwapByte : swap.byteSize = 1 := by
          exact
            _root_.EvmCompiler.Structured.Preservation.StackShuffle.swapInstr_byteSize
              (n := front.length + 1) (by omega) hSwapBound
        refine ⟨1, .running finalState, cursor, ?_, ?_⟩
        · rw [show
            pre ++ StackShuffle.liftBuriedToTop (front ++ [last]).length ++ post =
              (pre ++ StackShuffle.liftBuriedToTop front.length) ++
                [swap] ++ post by
              rw [hCodeEq]
              simp [List.append_assoc]]
          unfold Assembly.GasParametric.sourceRunNResultWithGasOracle
          rw [source_stepResult_local_withGasOracle
            (instr := swap)
            (pre := pre ++ StackShuffle.liftBuriedToTop front.length)
            (post := post) (state := mid) (final := finalState)
            (oracle := oracle) (cursor := cursor)
            hSwapLocal hSwapNoHalt
            (AssemblyProgram.PCFitsFrom.start hSwapFits)
            hMidPc hStep]
          rfl
        · refine ⟨rfl, ?_, ?_, ?_⟩
          · simp [finalState, EvmYul.EVM.State.replaceStackAndIncrPC,
              EvmYul.EVM.State.incrPC, List.append_assoc]
          · calc
              eraseControl finalState
                  =
                eraseControl
                  { mid with stack := token :: front ++ [last] ++ suffix } := by
                    simp [finalState, eraseControl, Assembly.eraseGas,
                      EvmYul.EVM.State.replaceStackAndIncrPC,
                      EvmYul.EVM.State.incrPC]
              _ =
                eraseControl
                  { state with stack := token :: front ++ [last] ++ suffix } := by
                    simpa [eraseControl, Assembly.eraseGas, List.append_assoc]
                      using
                        eraseControl_with_stack_congr
                          (left := mid)
                          (right :=
                            { state with stack := last :: front ++ token :: suffix })
                          (stack := token :: front ++ [last] ++ suffix)
                          hMidErase
          · calc
              finalState.pc
                  = mid.pc + EvmYul.UInt256.ofNat 1 := by
                      simp [finalState, EvmYul.EVM.State.replaceStackAndIncrPC,
                        EvmYul.EVM.State.incrPC]
              _ =
                Assembly.Program.pcAfter
                    (pre ++ StackShuffle.liftBuriedToTop front.length) +
                  EvmYul.UInt256.ofNat 1 := by
                    rw [hMidPc]
              _ =
                EvmYul.UInt256.ofNat
                  (Assembly.Program.byteLength
                      (pre ++ StackShuffle.liftBuriedToTop front.length) + 1) := by
                    rw [Assembly.Program.pcAfter, Assembly.UInt256_ofNat_add]
              _ =
                Assembly.Program.pcAfter
                  (pre ++ StackShuffle.liftBuriedToTop front.length ++ [swap]) := by
                    simp [Assembly.Program.pcAfter,
                      Assembly.Program.byteLength_append,
                      Assembly.Program.byteLength, hSwapByte, Nat.add_assoc]
              _ =
                Assembly.Program.pcAfter
                  (pre ++ StackShuffle.liftBuriedToTop (front ++ [last]).length) := by
                    rw [hCodeEq]
                    simp [List.append_assoc]

theorem removeBuriedUnder_source_exists_withGasOracle {state : EVMState}
    {returnValues suffix : List Word} {token : Word}
    {pre post : Assembly.Program} {oracle : GasOracle} {cursor : Nat}
    (hFits :
      AssemblyProgram.PCFitsFrom pre
        (StackShuffle.removeBuriedUnder returnValues.length))
    (hPc :
      ({ state with stack := returnValues ++ token :: suffix }).pc =
        Assembly.Program.pcAfter pre)
    (hBound : returnValues.length ≤ 16) :
    ARunResultWithGasOracle
      (pre ++ StackShuffle.removeBuriedUnder returnValues.length ++ post)
      oracle cursor
      { state with stack := returnValues ++ token :: suffix }
      (fun result cursorFinal =>
        match result with
        | .running final =>
            cursorFinal = cursor ∧
              final.stack = returnValues ++ suffix ∧
              eraseControl final =
                eraseControl { state with stack := returnValues ++ suffix } ∧
              final.pc =
                Assembly.Program.pcAfter
                  (pre ++ StackShuffle.removeBuriedUnder returnValues.length)
        | .halted _ => False) := by
  have hFitsLift :
      AssemblyProgram.PCFitsFrom pre
        (StackShuffle.liftBuriedToTop returnValues.length) := by
    exact
      AssemblyProgram.PCFitsFrom.left
        (by simpa [StackShuffle.removeBuriedUnder, List.append_assoc] using hFits)
  have hFitsPop :
      AssemblyProgram.PCFitsFrom
        (pre ++ StackShuffle.liftBuriedToTop returnValues.length)
        [Assembly.Instr.prim .pop] := by
    exact
      AssemblyProgram.PCFitsFrom.right
        (by simpa [StackShuffle.removeBuriedUnder, List.append_assoc] using hFits)
  have hLift :=
    liftBuriedToTop_source_exists_withGasOracle
      (state := state) (front := returnValues) (suffix := suffix)
      (token := token) (pre := pre) (post := [Assembly.Instr.prim .pop] ++ post)
      (oracle := oracle) (cursor := cursor)
      hFitsLift hPc hBound
  refine
    ARunResultWithGasOracle.bind_running
      (program :=
        pre ++ StackShuffle.removeBuriedUnder returnValues.length ++ post)
      (middle := fun mid cursorMid =>
        cursorMid = cursor ∧
          mid.stack = token :: returnValues ++ suffix ∧
          eraseControl mid =
            eraseControl { state with stack := token :: returnValues ++ suffix } ∧
          mid.pc =
            Assembly.Program.pcAfter
              (pre ++ StackShuffle.liftBuriedToTop returnValues.length))
      ?_ ?_
  · exact ARunResultWithGasOracle.mono
      (by
        simpa [StackShuffle.removeBuriedUnder, List.append_assoc] using hLift)
      (by
        intro result cursorMid hResult
        cases result with
        | halted halt =>
            cases hResult
        | running mid =>
            rcases hResult with ⟨hCursorMid, hStack, hErase, hPcMid⟩
            exact ⟨hCursorMid, hStack, hErase, hPcMid⟩)
  · intro mid cursorMid hMid
    rcases hMid with ⟨hCursorMid, hMidStack, hMidErase, hMidPc⟩
    subst cursorMid
    have hMidRecord :
        { mid with stack := token :: returnValues ++ suffix } = mid := by
      rw [← hMidStack]
    let finalState : EVMState :=
      mid.replaceStackAndIncrPC (returnValues ++ suffix)
    have hPopStep :
        Assembly.Target.stepInstr
            (_root_.EvmCompiler.Structured.Preservation.StackShuffle.targetInstr
              (Assembly.Instr.prim .pop)) mid =
          .ok finalState := by
      rw [← hMidRecord]
      exact _root_.EvmCompiler.Structured.Preservation.StackShuffle.pop_cons_step
        (state := mid) (top := token) (suffix := returnValues ++ suffix)
    refine ⟨1, .running finalState, cursor, ?_, ?_⟩
    · rw [show
        pre ++ StackShuffle.removeBuriedUnder returnValues.length ++ post =
          (pre ++ StackShuffle.liftBuriedToTop returnValues.length) ++
            [Assembly.Instr.prim .pop] ++ post by
          simp [StackShuffle.removeBuriedUnder, List.append_assoc]]
      unfold Assembly.GasParametric.sourceRunNResultWithGasOracle
      rw [source_stepResult_local_withGasOracle
        (instr := Assembly.Instr.prim .pop)
        (pre := pre ++ StackShuffle.liftBuriedToTop returnValues.length)
        (post := post) (state := mid) (final := finalState)
        (oracle := oracle) (cursor := cursor)
        (by simp [SourceLocalNoGasInstr]) rfl
        (AssemblyProgram.PCFitsFrom.start hFitsPop)
        hMidPc hPopStep]
      rfl
    · refine ⟨rfl, ?_, ?_, ?_⟩
      · simp [finalState, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC]
      · calc
          eraseControl finalState
              =
            eraseControl { mid with stack := returnValues ++ suffix } := by
                simp [finalState, eraseControl, Assembly.eraseGas,
                  EvmYul.EVM.State.replaceStackAndIncrPC,
                  EvmYul.EVM.State.incrPC]
          _ =
            eraseControl { state with stack := returnValues ++ suffix } := by
                exact
                  eraseControl_with_stack_congr
                    (left := mid)
                    (right :=
                      { state with stack := token :: returnValues ++ suffix })
                    (stack := returnValues ++ suffix)
                    hMidErase
      · calc
          finalState.pc
              = mid.pc + EvmYul.UInt256.ofNat 1 := by
                  simp [finalState, EvmYul.EVM.State.replaceStackAndIncrPC,
                    EvmYul.EVM.State.incrPC]
          _ =
            Assembly.Program.pcAfter
                (pre ++ StackShuffle.liftBuriedToTop returnValues.length) +
              EvmYul.UInt256.ofNat 1 := by
                rw [hMidPc]
          _ =
            EvmYul.UInt256.ofNat
              (Assembly.Program.byteLength
                  (pre ++ StackShuffle.liftBuriedToTop returnValues.length) + 1) := by
                rw [Assembly.Program.pcAfter, Assembly.UInt256_ofNat_add]
          _ =
            Assembly.Program.pcAfter
              (pre ++ StackShuffle.removeBuriedUnder returnValues.length) := by
                simp [StackShuffle.removeBuriedUnder,
                  Assembly.Program.pcAfter, Assembly.Program.byteLength_append,
                  Assembly.Program.byteLength, Assembly.Instr.byteSize,
                  Nat.add_assoc]

theorem dispatchCondition_source_exists_withGasOracle {state : EVMState}
    {returnValues suffix : List Word} {token probe : Word}
    {pre post : Assembly.Program} {oracle : GasOracle} {cursor : Nat}
    (hFits :
      AssemblyProgram.PCFitsFrom pre
        [ StackShuffle.dupInstr (returnValues.length + 1)
        , Assembly.Instr.push probe
        , Assembly.Instr.prim .eq
        ])
    (hPc :
      ({ state with stack := returnValues ++ token :: suffix }).pc =
        Assembly.Program.pcAfter pre)
    (hBound : returnValues.length < 16) :
    ARunResultWithGasOracle
      (pre ++
        [ StackShuffle.dupInstr (returnValues.length + 1)
        , Assembly.Instr.push probe
        , Assembly.Instr.prim .eq
        ] ++ post)
      oracle cursor
      { state with stack := returnValues ++ token :: suffix }
      (fun result cursorFinal =>
        match result with
        | .running final =>
            cursorFinal = cursor ∧
              final.stack =
                EvmYul.UInt256.eq probe token ::
                  returnValues ++ token :: suffix ∧
              eraseControl final =
                eraseControl
                  { state with stack :=
                      EvmYul.UInt256.eq probe token ::
                        returnValues ++ token :: suffix } ∧
              final.pc =
                Assembly.Program.pcAfter
                  (pre ++
                    [ StackShuffle.dupInstr (returnValues.length + 1)
                    , Assembly.Instr.push probe
                    , Assembly.Instr.prim .eq
                    ])
        | .halted _ => False) := by
  let dupInstr := StackShuffle.dupInstr (returnValues.length + 1)
  let start : EVMState :=
    { state with stack := returnValues ++ token :: suffix }
  let afterDup : EVMState :=
    EvmYul.EVM.State.replaceStackAndIncrPC start
      (token :: returnValues ++ token :: suffix)
  let afterPush : EVMState :=
    afterDup.replaceStackAndIncrPC
      (probe :: token :: returnValues ++ token :: suffix) (pcΔ := 33)
  let finalState : EVMState :=
    afterPush.replaceStackAndIncrPC
      (EvmYul.UInt256.eq probe token ::
        returnValues ++ token :: suffix)
  have hDupStep :
      Assembly.Target.stepInstr
          (_root_.EvmCompiler.Structured.Preservation.StackShuffle.targetInstr
            dupInstr) start =
        .ok afterDup := by
    rw [show dupInstr = StackShuffle.dupInstr (returnValues.length + 1) from rfl]
    rw [_root_.EvmCompiler.Structured.Preservation.StackShuffle.dupInstr_step_eq_dup
      (by omega) (by omega)]
    simpa [afterDup, start, List.append_assoc] using
      (_root_.EvmCompiler.Structured.Preservation.StackShuffle.dup_append_token
        (state := state) (front := returnValues)
        (suffix := suffix) (token := token))
  have hPushStep :
      Assembly.Target.stepInstr
          (_root_.EvmCompiler.Structured.Preservation.StackShuffle.targetInstr
            (Assembly.Instr.push probe)) afterDup =
        .ok afterPush := by
    simp [_root_.EvmCompiler.Structured.Preservation.StackShuffle.targetInstr,
      afterPush, afterDup, Assembly.Target.stepInstr,
      EvmYul.Stack.push, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC]
  have hEqStep :
      Assembly.Target.stepInstr
          (_root_.EvmCompiler.Structured.Preservation.StackShuffle.targetInstr
            (Assembly.Instr.prim .eq)) afterPush =
        .ok finalState := by
    simp [_root_.EvmCompiler.Structured.Preservation.StackShuffle.targetInstr,
      finalState, afterPush, afterDup, Assembly.Target.stepInstr,
      Assembly.PrimOp.step, Assembly.PrimOp.continuingStep?,
      Assembly.PrimStep.run, EvmYul.EVM.execBinOp, EvmYul.Stack.push,
      EvmYul.Stack.pop2, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, Id.run]
  have hDupByte : dupInstr.byteSize = 1 := by
    exact
      _root_.EvmCompiler.Structured.Preservation.StackShuffle.dupInstr_byteSize
        (n := returnValues.length + 1) (by omega) (by omega)
  have hAfterDupPc :
      afterDup.pc = Assembly.Program.pcAfter (pre ++ [dupInstr]) := by
    have hPcState : state.pc = Assembly.Program.pcAfter pre := by
      simpa [start] using hPc
    calc
      afterDup.pc
          = state.pc + EvmYul.UInt256.ofNat 1 := by
              simp [afterDup, start, EvmYul.EVM.State.replaceStackAndIncrPC,
                EvmYul.EVM.State.incrPC]
      _ = Assembly.Program.pcAfter pre + EvmYul.UInt256.ofNat 1 := by
              rw [hPcState]
      _ = EvmYul.UInt256.ofNat (Assembly.Program.byteLength pre + 1) := by
              rw [Assembly.Program.pcAfter, Assembly.UInt256_ofNat_add]
      _ = Assembly.Program.pcAfter (pre ++ [dupInstr]) := by
              simp [Assembly.Program.pcAfter,
                Assembly.Program.byteLength_append,
                Assembly.Program.byteLength, hDupByte]
  have hAfterPushPc :
      afterPush.pc =
        Assembly.Program.pcAfter
          (pre ++ [dupInstr, Assembly.Instr.push probe]) := by
    calc
      afterPush.pc
          = afterDup.pc + EvmYul.UInt256.ofNat 33 := by
              simp [afterPush, EvmYul.EVM.State.replaceStackAndIncrPC,
                EvmYul.EVM.State.incrPC]
      _ =
        Assembly.Program.pcAfter (pre ++ [dupInstr]) +
          EvmYul.UInt256.ofNat 33 := by
              rw [hAfterDupPc]
      _ =
        EvmYul.UInt256.ofNat
          (Assembly.Program.byteLength (pre ++ [dupInstr]) + 33) := by
              rw [Assembly.Program.pcAfter, Assembly.UInt256_ofNat_add]
      _ =
        Assembly.Program.pcAfter
          (pre ++ [dupInstr, Assembly.Instr.push probe]) := by
              simp [Assembly.Program.pcAfter,
                Assembly.Program.byteLength_append,
                Assembly.Program.byteLength, Assembly.Instr.byteSize,
                Assembly.Instr.push32Size, Nat.add_assoc]
  have hEqFit : PCFits (pre ++ [dupInstr, Assembly.Instr.push probe]) := by
    simpa [dupInstr] using hFits.2.2.1
  refine ⟨3, .running finalState, cursor, ?_, ?_⟩
  · unfold Assembly.GasParametric.sourceRunNResultWithGasOracle
    rw [show
      pre ++
          [ StackShuffle.dupInstr (returnValues.length + 1)
          , Assembly.Instr.push probe
          , Assembly.Instr.prim .eq
          ] ++ post =
        pre ++ [dupInstr] ++
          ([Assembly.Instr.push probe, Assembly.Instr.prim .eq] ++ post) by
      simp [dupInstr, List.append_assoc]]
    rw [source_stepResult_local_withGasOracle
      (instr := dupInstr) (pre := pre)
      (post := [Assembly.Instr.push probe, Assembly.Instr.prim .eq] ++ post)
      (state := start) (final := afterDup)
      (oracle := oracle) (cursor := cursor)
      (dupInstr_sourceLocalNoGas
        (n := returnValues.length + 1) (by omega) (by omega))
      (_root_.EvmCompiler.Structured.Preservation.StackShuffle.dupInstr_haltKind?_none
        (n := returnValues.length + 1) (by omega) (by omega))
      hFits.1 (by simpa [start] using hPc) hDupStep]
    simp [Bind.bind, Except.bind]
    rw [show
      pre ++ dupInstr :: Assembly.Instr.push probe ::
          Assembly.Instr.prim .eq :: post =
        (pre ++ [dupInstr]) ++ [Assembly.Instr.push probe] ++
          ([Assembly.Instr.prim .eq] ++ post) by
      simp [List.append_assoc]]
    unfold Assembly.GasParametric.sourceRunNResultWithGasOracle
    rw [source_stepResult_local_withGasOracle
      (instr := Assembly.Instr.push probe) (pre := pre ++ [dupInstr])
      (post := [Assembly.Instr.prim .eq] ++ post)
      (state := afterDup) (final := afterPush)
      (oracle := oracle) (cursor := cursor)
      (by simp [SourceLocalNoGasInstr]) rfl hFits.2.1
      hAfterDupPc hPushStep]
    simp [Bind.bind, Except.bind]
    rw [show
      pre ++ dupInstr :: Assembly.Instr.push probe ::
          Assembly.Instr.prim .eq :: post =
        (pre ++ [dupInstr, Assembly.Instr.push probe]) ++
          [Assembly.Instr.prim .eq] ++ post by
      simp [List.append_assoc]]
    unfold Assembly.GasParametric.sourceRunNResultWithGasOracle
    rw [source_stepResult_local_withGasOracle
      (instr := Assembly.Instr.prim .eq)
      (pre := pre ++ [dupInstr, Assembly.Instr.push probe])
      (post := post) (state := afterPush) (final := finalState)
      (oracle := oracle) (cursor := cursor)
      (by simp [SourceLocalNoGasInstr]) rfl hEqFit hAfterPushPc hEqStep]
    simp [Assembly.GasParametric.sourceRunNResultWithGasOracle,
      Bind.bind, Except.bind]
  · refine ⟨rfl, ?_, ?_, ?_⟩
    · simp [finalState, afterPush, afterDup,
        EvmYul.EVM.State.replaceStackAndIncrPC, EvmYul.EVM.State.incrPC]
    · simp [finalState, afterPush, afterDup, start, eraseControl, Assembly.eraseGas,
        EvmYul.EVM.State.replaceStackAndIncrPC, EvmYul.EVM.State.incrPC]
    · calc
        finalState.pc
            = afterPush.pc + EvmYul.UInt256.ofNat 1 := by
                simp [finalState, EvmYul.EVM.State.replaceStackAndIncrPC,
                  EvmYul.EVM.State.incrPC]
        _ =
          Assembly.Program.pcAfter
              (pre ++ [dupInstr, Assembly.Instr.push probe]) +
            EvmYul.UInt256.ofNat 1 := by
                rw [hAfterPushPc]
        _ =
          EvmYul.UInt256.ofNat
            (Assembly.Program.byteLength
                (pre ++ [dupInstr, Assembly.Instr.push probe]) + 1) := by
                rw [Assembly.Program.pcAfter, Assembly.UInt256_ofNat_add]
        _ =
          Assembly.Program.pcAfter
            (pre ++
              [dupInstr, Assembly.Instr.push probe, Assembly.Instr.prim .eq]) := by
              simp [Assembly.Program.pcAfter,
                Assembly.Program.byteLength_append, Assembly.Program.byteLength,
                Assembly.Instr.byteSize, Nat.add_assoc]

theorem dispatchCondition_jumpi_source_exists_withGasOracle {state : EVMState}
    {returnValues suffix : List Word} {token probe : Word}
    {label : Assembly.Label} {dest : Nat}
    {pre post : Assembly.Program} {oracle : GasOracle} {cursor : Nat}
    (hFits :
      AssemblyProgram.PCFitsFrom pre
        [ StackShuffle.dupInstr (returnValues.length + 1)
        , Assembly.Instr.push probe
        , Assembly.Instr.prim .eq
        , Assembly.Instr.jumpi label
        ])
    (hPc :
      ({ state with stack := returnValues ++ token :: suffix }).pc =
        Assembly.Program.pcAfter pre)
    (hBound : returnValues.length < 16)
    (hLabel :
      Assembly.Program.labelPc
        (pre ++
          [ StackShuffle.dupInstr (returnValues.length + 1)
          , Assembly.Instr.push probe
          , Assembly.Instr.prim .eq
          , Assembly.Instr.jumpi label
          ] ++ post)
        label = some dest) :
    ARunResultWithGasOracle
      (pre ++
        [ StackShuffle.dupInstr (returnValues.length + 1)
        , Assembly.Instr.push probe
        , Assembly.Instr.prim .eq
        , Assembly.Instr.jumpi label
        ] ++ post)
      oracle cursor
      { state with stack := returnValues ++ token :: suffix }
      (fun result cursorFinal =>
        match result with
        | .running final =>
            cursorFinal = cursor ∧
              final.stack = returnValues ++ token :: suffix ∧
              eraseControl final =
                eraseControl
                  { state with stack := returnValues ++ token :: suffix } ∧
              final.pc =
                if probe = token then
                  EvmYul.UInt256.ofNat dest
                else
                  Assembly.Program.pcAfter
                    (pre ++
                      [ StackShuffle.dupInstr (returnValues.length + 1)
                      , Assembly.Instr.push probe
                      , Assembly.Instr.prim .eq
                      , Assembly.Instr.jumpi label
                      ])
        | .halted _ => False) := by
  let conditionCode : Assembly.Program :=
    [ StackShuffle.dupInstr (returnValues.length + 1)
    , Assembly.Instr.push probe
    , Assembly.Instr.prim .eq
    ]
  have hFitsCond :
      AssemblyProgram.PCFitsFrom pre conditionCode := by
    exact
      AssemblyProgram.PCFitsFrom.left
        (pre := pre) (first := conditionCode)
        (second := [Assembly.Instr.jumpi label])
        (by simpa [conditionCode] using hFits)
  have hFitsJump :
      AssemblyProgram.PCFitsFrom (pre ++ conditionCode)
        [Assembly.Instr.jumpi label] := by
    exact
      AssemblyProgram.PCFitsFrom.right
        (pre := pre) (first := conditionCode)
        (second := [Assembly.Instr.jumpi label])
        (by simpa [conditionCode] using hFits)
  have hCondition :=
    dispatchCondition_source_exists_withGasOracle
      (state := state) (returnValues := returnValues) (suffix := suffix)
      (token := token) (probe := probe) (pre := pre)
      (post := [Assembly.Instr.jumpi label] ++ post)
      (oracle := oracle) (cursor := cursor)
      (by simpa [conditionCode] using hFitsCond) hPc hBound
  refine
    ARunResultWithGasOracle.bind_running
      (program :=
        pre ++
          [ StackShuffle.dupInstr (returnValues.length + 1)
          , Assembly.Instr.push probe
          , Assembly.Instr.prim .eq
          , Assembly.Instr.jumpi label
          ] ++ post)
      (middle := fun mid cursorMid =>
        cursorMid = cursor ∧
          mid.stack =
            EvmYul.UInt256.eq probe token :: returnValues ++ token :: suffix ∧
          eraseControl mid =
            eraseControl
              { state with stack :=
                  EvmYul.UInt256.eq probe token ::
                    returnValues ++ token :: suffix } ∧
          mid.pc = Assembly.Program.pcAfter (pre ++ conditionCode))
      ?_ ?_
  · exact
      ARunResultWithGasOracle.mono
        (by
          simpa [conditionCode, List.append_assoc]
            using hCondition)
        (by
          intro result cursorMid hResult
          cases result with
          | halted halt =>
              cases hResult
          | running mid =>
              rcases hResult with
                ⟨hCursorMid, hStack, hErase, hPcMid⟩
              exact
                ⟨hCursorMid, hStack, hErase,
                  by simpa [conditionCode] using hPcMid⟩)
  · intro mid cursorMid hMid
    rcases hMid with ⟨hCursorMid, hMidStack, hMidErase, hMidPc⟩
    subst cursorMid
    let afterPop : EVMState :=
      { mid with stack := returnValues ++ token :: suffix }
    have hPop :
        Code.popCondition mid = .ok (afterPop, probe = token) := by
      unfold Code.popCondition
      rw [hMidStack]
      simp [EvmYul.Stack.pop, afterPop, uint256_eq_ne_zero]
    have hRel :
        RelAt (Assembly.Program.pcAfter (pre ++ conditionCode)) mid mid := by
      exact ⟨hMidPc, rfl⟩
    have hLabel' :
        Assembly.Program.labelPc
          ((pre ++ conditionCode) ++ [Assembly.Instr.jumpi label] ++ post)
          label = some dest := by
      simpa [conditionCode, List.append_assoc] using hLabel
    rcases
      AssemblyControl.jumpi_stepResult_ctx_relAt_of_popCondition_withGasOracle
        (label := label) (dest := dest) (pre := pre ++ conditionCode)
        (post := post) (source := mid) (target := mid)
        (source' := afterPop) (condTrue := probe = token)
        (oracle := oracle) (cursor := cursor)
        (AssemblyProgram.PCFitsFrom.start hFitsJump) hRel hLabel' hPop with
      ⟨final, hStep, hRelFinal⟩
    refine ⟨1, .running final, cursor, ?_, ?_⟩
    · unfold Assembly.GasParametric.sourceRunNResultWithGasOracle
      rw [show
        pre ++
            [ StackShuffle.dupInstr (returnValues.length + 1)
            , Assembly.Instr.push probe
            , Assembly.Instr.prim .eq
            , Assembly.Instr.jumpi label
            ] ++ post =
          (pre ++ conditionCode) ++ [Assembly.Instr.jumpi label] ++ post by
        simp [conditionCode, List.append_assoc]]
      rw [hStep]
      rfl
    · refine ⟨rfl, ?_, ?_, ?_⟩
      · exact
          stack_eq_of_eraseControl_eq
            (by simpa [afterPop] using hRelFinal.sameData)
      · calc
          eraseControl final = eraseControl afterPop := hRelFinal.sameData
          _ =
            eraseControl
              { state with stack := returnValues ++ token :: suffix } := by
              exact
                eraseControl_with_stack_congr
                  (left := mid)
                  (right :=
                    { state with stack :=
                        EvmYul.UInt256.eq probe token ::
                          returnValues ++ token :: suffix })
                  (stack := returnValues ++ token :: suffix)
                  hMidErase
      · simpa [conditionCode, List.append_assoc] using hRelFinal.pc_eq

end StackShuffleGas

namespace FrameStateRel

theorem runStateWithGasOracle_frameSafe_hidden_exists
    {source final : RunState} {target : EVMState}
    {tokens : List Word} {code : Code}
    {oracle : GasOracle} {cursor cursor' : Nat}
    (hRel : Preservation.Frame.StateRel source target tokens)
    (hFrame : Code.FrameSafeWithGasOracle code)
    (hRun :
      Code.runStateWithGasOracle code oracle cursor source =
        .ok (final, cursor')) :
    ∃ hiddenFinal,
      Code.runWithGasOracle code oracle cursor
          { source.evm with stack := target.stack } =
        .ok (hiddenFinal, cursor') ∧
        Preservation.Frame.StateRel final hiddenFinal tokens := by
  unfold Code.runStateWithGasOracle at hRun
  cases hCode : Code.runWithGasOracle code oracle cursor source.evm with
  | error _err =>
      rw [hCode] at hRun
      cases hRun
  | ok runResult =>
      rcases runResult with ⟨evmFinal, cursorFinal⟩
      rw [hCode] at hRun
      change
        Except.ok (source.withEVM evmFinal, cursorFinal) =
          Except.ok (final, cursor') at hRun
      cases hRun
      rcases hRel.hidden_suffix with ⟨suffix, hTargetStack, hMaterialize⟩
      let hiddenFinal : EVMState :=
        { evmFinal with stack := evmFinal.stack ++ suffix }
      have hHiddenRun :
          Code.runWithGasOracle code oracle cursor
              { source.evm with stack := source.evm.stack ++ suffix } =
            .ok (hiddenFinal, cursor') := by
        simpa [hiddenFinal] using
          hFrame oracle cursor cursor' source.evm evmFinal suffix hCode
      refine ⟨hiddenFinal, ?_, ?_⟩
      · rw [hTargetStack]
        exact hHiddenRun
      · refine ⟨?_, ?_⟩
        · simpa [RunState.withEVM, hiddenFinal] using
            hMaterialize evmFinal.stack
        · simp [RunState.withEVM, hiddenFinal]

theorem source_run_code_ctx_result_withGasOracle
    {source final : RunState}
    {target : EVMState} {tokens : List Word} {code : Code}
    {pre post : Assembly.Program}
    {oracle : GasOracle} {cursor cursor' : Nat}
    (hSafe : Code.RunnerSafeWithGasOracle code)
    (hFrame : Code.FrameSafeWithGasOracle code)
    (hFits : Preservation.Code.PCFitsFrom pre code)
    (hPc : target.pc = Assembly.Program.pcAfter pre)
    (hRel : Preservation.Frame.StateRel source target tokens)
    (hRun :
      Code.runStateWithGasOracle code oracle cursor source =
        .ok (final, cursor')) :
    ARunResultWithGasOracle (pre ++ code.toAssembly ++ post) oracle cursor
      target
      (fun result cursorFinal =>
        match result with
        | .running target' =>
            cursorFinal = cursor' ∧
              Preservation.Frame.StateRel final target' tokens ∧
                target'.pc =
                  Assembly.Program.pcAfter (pre ++ code.toAssembly)
        | .halted _ => False) := by
  rcases
    runStateWithGasOracle_frameSafe_hidden_exists
      (source := source) (final := final) (target := target)
      (tokens := tokens) (code := code) (oracle := oracle)
      (cursor := cursor) (cursor' := cursor') hRel hFrame hRun with
    ⟨hiddenFinal, hHiddenRun, hHiddenRel⟩
  have hRelAt :
      RelAt (Assembly.Program.pcAfter pre) target
        { source.evm with stack := target.stack } := by
    exact ⟨hPc, hRel.dataRel⟩
  have hRunAssembly :=
    Code.source_runResult_ctx_relAt_of_relAt_withGasOracle
      (code := code) (pre := pre) (post := post)
      hSafe hFits hRelAt hHiddenRun
  exact ARunResultWithGasOracle.mono hRunAssembly (by
    intro result cursorFinal hEnd
    cases result with
    | halted halt =>
        cases hEnd
    | running target' =>
        rcases hEnd with ⟨hCursor, hEnd⟩
        have hStack : target'.stack = hiddenFinal.stack :=
          stack_eq_of_eraseControl_eq hEnd.sameData
        refine ⟨hCursor, ?_, hEnd.pc_eq⟩
        refine ⟨?_, ?_⟩
        · rw [hStack]
          exact hHiddenRel.stackRel
        · calc
            eraseControl target'
                = eraseControl hiddenFinal := hEnd.sameData
            _ = eraseControl { final.evm with stack := hiddenFinal.stack } :=
                hHiddenRel.dataRel
            _ = eraseControl { final.evm with stack := target'.stack } := by
                rw [hStack])

theorem runConditionStateWithGasOracle_frameSafe_hidden_exists
    {source final : RunState} {target : EVMState}
    {tokens : List Word} {code : Code} {condTrue : Bool}
    {oracle : GasOracle} {cursor cursor' : Nat}
    (hRel : Preservation.Frame.StateRel source target tokens)
    (hFrame : Code.FrameSafeWithGasOracle code)
    (hRun :
      Code.runConditionStateWithGasOracle code oracle cursor source =
        .ok (final, condTrue, cursor')) :
    ∃ hiddenFinal,
      Code.runConditionWithGasOracle code oracle cursor
          { source.evm with stack := target.stack } =
        .ok (hiddenFinal, condTrue, cursor') ∧
        Preservation.Frame.StateRel final hiddenFinal tokens := by
  unfold Code.runConditionStateWithGasOracle Code.runConditionWithGasOracle at hRun
  cases hCode : Code.runWithGasOracle code oracle cursor source.evm with
  | error _err =>
      rw [hCode] at hRun
      cases hRun
  | ok runResult =>
      rcases runResult with ⟨evmAfterCode, cursorAfterCode⟩
      rw [hCode] at hRun
      cases hPop : Code.popCondition evmAfterCode with
      | error _err =>
          simp [hPop, Bind.bind, Except.bind] at hRun
      | ok popResult =>
          rcases popResult with ⟨evmAfterPop, condResult⟩
          simp [hPop, Bind.bind, Except.bind] at hRun
          rcases hRun with ⟨hFinal, hCond, hCursor⟩
          cases hFinal
          cases hCond
          cases hCursor
          rcases hRel.hidden_suffix with ⟨suffix, hTargetStack, hMaterialize⟩
          let hiddenAfterCode : EVMState :=
            { evmAfterCode with stack := evmAfterCode.stack ++ suffix }
          have hHiddenCode :
              Code.runWithGasOracle code oracle cursor
                  { source.evm with stack := source.evm.stack ++ suffix } =
                .ok (hiddenAfterCode, cursor') := by
            simpa [hiddenAfterCode] using
              hFrame oracle cursor cursor' source.evm evmAfterCode
                suffix hCode
          have hHiddenPop :
                  Code.popCondition hiddenAfterCode =
                .ok
                  ({ evmAfterPop with stack := evmAfterPop.stack ++ suffix },
                    condTrue) := by
            simpa [hiddenAfterCode] using
              Preservation.Frame.StateRel.popCondition_hidden_suffix
                (hidden := suffix) hPop
          refine
            ⟨{ evmAfterPop with stack := evmAfterPop.stack ++ suffix },
              ?_, ?_⟩
          · rw [hTargetStack]
            unfold Code.runConditionWithGasOracle
            rw [hHiddenCode]
            simp [hHiddenPop, Bind.bind, Except.bind]
          · refine ⟨?_, ?_⟩
            · simpa [RunState.withEVM] using hMaterialize evmAfterPop.stack
            · simp [RunState.withEVM]

theorem runCondition_jumpi_result_ctx_withGasOracle
    {source final : RunState} {target : EVMState}
    {tokens : List Word} {cond : Code}
    {label : Assembly.Label} {dest : Nat}
    {pre post : Assembly.Program} {condTrue : Bool}
    {oracle : GasOracle} {cursor cursor' : Nat}
    (hSafe : Code.RunnerSafeWithGasOracle cond)
    (hFrame : Code.FrameSafeWithGasOracle cond)
    (hFits : Preservation.Code.PCFitsFrom pre cond)
    (hPc : target.pc = Assembly.Program.pcAfter pre)
    (hRel : Preservation.Frame.StateRel source target tokens)
    (hLabel :
      Assembly.Program.labelPc
          (pre ++ cond.toAssembly ++ [Assembly.Instr.jumpi label] ++ post)
          label = some dest)
    (hRun :
      Code.runConditionStateWithGasOracle cond oracle cursor source =
        .ok (final, condTrue, cursor')) :
    ARunResultWithGasOracle
      (pre ++ cond.toAssembly ++ [Assembly.Instr.jumpi label] ++ post)
      oracle cursor target
      (fun result cursorFinal =>
        match result with
        | .running target' =>
            cursorFinal = cursor' ∧
              Preservation.Frame.StateRel final target' tokens ∧
                target'.pc =
                  if condTrue then
                    EvmYul.UInt256.ofNat dest
                  else
                    Assembly.Program.pcAfter
                      (pre ++ cond.toAssembly ++ [Assembly.Instr.jumpi label])
        | .halted _ => False) := by
  rcases
    runConditionStateWithGasOracle_frameSafe_hidden_exists
      (source := source) (final := final) (target := target)
      (tokens := tokens) (code := cond) (condTrue := condTrue)
      (oracle := oracle) (cursor := cursor) (cursor' := cursor')
      hRel hFrame hRun with
    ⟨hiddenFinal, hHiddenRun, hHiddenRel⟩
  have hRelAt :
      RelAt (Assembly.Program.pcAfter pre) target
        { source.evm with stack := target.stack } := by
    exact ⟨hPc, hRel.dataRel⟩
  have hRunAssembly :=
    Code.runCondition_jumpi_result_ctx_relAt_of_relAt_withGasOracle
      (cond := cond) (label := label) (dest := dest)
      (pre := pre) (post := post)
      hSafe hFits hRelAt hLabel hHiddenRun
  exact ARunResultWithGasOracle.mono hRunAssembly (by
    intro result cursorFinal hEnd
    cases result with
    | halted halt =>
        cases hEnd
    | running target' =>
        rcases hEnd with ⟨hCursor, hEnd⟩
        have hStack : target'.stack = hiddenFinal.stack :=
          stack_eq_of_eraseControl_eq hEnd.sameData
        refine ⟨hCursor, ?_, hEnd.pc_eq⟩
        refine ⟨?_, ?_⟩
        · rw [hStack]
          exact hHiddenRel.stackRel
        · calc
            eraseControl target'
                = eraseControl hiddenFinal := hEnd.sameData
            _ = eraseControl { final.evm with stack := hiddenFinal.stack } :=
                hHiddenRel.dataRel
            _ = eraseControl { final.evm with stack := target'.stack } := by
                rw [hStack])

theorem label_stepResult_at_withGasOracle {label : Assembly.Label}
    {pre post : Assembly.Program} {source : RunState} {target : EVMState}
    {tokens : List Word} {oracle : GasOracle} {cursor : Nat}
    (hFit : PCFits pre)
    (hPc : target.pc = Assembly.Program.pcAfter pre)
    (hRel : Preservation.Frame.StateRel source target tokens) :
    ∃ target',
      Assembly.GasParametric.sourceStepResultWithGasOracle
          (pre ++ [Assembly.Instr.label label] ++ post) oracle cursor target =
        .ok (.running target', cursor) ∧
        Preservation.Frame.StateRel source target' tokens ∧
        target'.pc =
          Assembly.Program.pcAfter (pre ++ [Assembly.Instr.label label]) := by
  let target' := target.incrPC
  have hRelAt :
      RelAt (Assembly.Program.pcAfter pre) target
        { source.evm with stack := target.stack } := by
    exact ⟨hPc, hRel.dataRel⟩
  rcases
    AssemblyControl.label_stepResult_ctx_relAt_of_relAt_withGasOracle
      (label := label) (pre := pre) (post := post)
      (oracle := oracle) (cursor := cursor) hFit hRelAt with
    ⟨target'', hStep, hRelAfter⟩
  refine ⟨target'', hStep, ?_, hRelAfter.pc_eq⟩
  have hStack : target''.stack = target.stack :=
    stack_eq_of_eraseControl_eq
      (by
        calc
          eraseControl target''
              = eraseControl { source.evm with stack := target.stack } :=
                  hRelAfter.sameData
          _ = eraseControl target := hRel.dataRel.symm)
  refine ⟨?_, ?_⟩
  · simpa [hStack] using hRel.stackRel
  · rw [hStack]
    exact hRelAfter.sameData

theorem jump_stepResult_at_withGasOracle
    {label : Assembly.Label} {dest : Nat}
    {pre post : Assembly.Program} {source : RunState} {target : EVMState}
    {tokens : List Word} {oracle : GasOracle} {cursor : Nat}
    (hFit : PCFits pre)
    (hPc : target.pc = Assembly.Program.pcAfter pre)
    (hRel : Preservation.Frame.StateRel source target tokens)
    (hLabel :
      Assembly.Program.labelPc (pre ++ [Assembly.Instr.jump label] ++ post)
        label = some dest) :
    ∃ target',
      Assembly.GasParametric.sourceStepResultWithGasOracle
          (pre ++ [Assembly.Instr.jump label] ++ post) oracle cursor target =
        .ok (.running target', cursor) ∧
        Preservation.Frame.StateRel source target' tokens ∧
        target'.pc = EvmYul.UInt256.ofNat dest := by
  have hRelAt :
      RelAt (Assembly.Program.pcAfter pre) target
        { source.evm with stack := target.stack } := by
    exact ⟨hPc, hRel.dataRel⟩
  rcases
    AssemblyControl.jump_stepResult_ctx_relAt_of_relAt_withGasOracle
      (label := label) (dest := dest) (pre := pre) (post := post)
      (oracle := oracle) (cursor := cursor) hFit hRelAt hLabel with
    ⟨target', hStep, hRelAfter⟩
  refine ⟨target', hStep, ?_, hRelAfter.pc_eq⟩
  have hStack : target'.stack = target.stack :=
    stack_eq_of_eraseControl_eq
      (by
        calc
          eraseControl target'
              = eraseControl { source.evm with stack := target.stack } :=
                  hRelAfter.sameData
          _ = eraseControl target := hRel.dataRel.symm)
  refine ⟨?_, ?_⟩
  · simpa [hStack] using hRel.stackRel
  · rw [hStack]
    exact hRelAfter.sameData

theorem source_callEntry_after_prologue_withGasOracle
    {source : RunState} {target : EVMState}
    {tokens : List Word} {argc retc : Nat}
    {args callerStack : EvmYul.Stack Word} {token : Word}
    {pre post : Assembly.Program} {oracle : GasOracle} {cursor : Nat}
    (hFits :
      AssemblyProgram.PCFitsFrom pre
        ([Assembly.Instr.push token] ++
          StackShuffle.sinkTopUnder args.length))
    (hPc : target.pc = Assembly.Program.pcAfter pre)
    (hRel : Preservation.Frame.StateRel source target tokens)
    (hSplit :
      StackFrame.splitArgs? argc source.evm.stack =
        some (args, callerStack))
    (hArgBound : args.length ≤ 16) :
    ARunResultWithGasOracle
      (pre ++
        ([Assembly.Instr.push token] ++
          StackShuffle.sinkTopUnder args.length) ++
        post)
      oracle cursor target
      (fun result cursorFinal =>
        match result with
        | .running final =>
            cursorFinal = cursor ∧
              Preservation.Frame.StateRel
                ((source.withEVM { source.evm with stack := args }).pushReturn
                  callerStack retc)
                final (token :: tokens) ∧
              final.pc =
                Assembly.Program.pcAfter
                  (pre ++
                    ([Assembly.Instr.push token] ++
                      StackShuffle.sinkTopUnder args.length))
        | .halted _ => False) := by
  rcases
    Preservation.Frame.StateRel.caller_materialization_of_split
      hRel hSplit with
    ⟨callerTarget, hCaller, hTargetStack⟩
  have hTargetRecord : { target with stack := args ++ callerTarget } = target := by
    rw [← hTargetStack]
  have hRun :=
    StackShuffleGas.callPrologue_source_exists_withGasOracle
      (state := target) (args := args) (suffix := callerTarget)
      (token := token) (pre := pre) (post := post)
      (oracle := oracle) (cursor := cursor)
      hFits (by simpa using hPc) hArgBound
  exact ARunResultWithGasOracle.mono
    (by simpa [hTargetRecord] using hRun)
    (by
      intro result cursorFinal hResult
      cases result with
      | halted halt =>
          cases hResult
      | running final =>
          rcases hResult with
            ⟨hCursorFinal, hFinalStack, hFinalErase, hFinalPc⟩
          refine ⟨hCursorFinal, ?_, hFinalPc⟩
          refine ⟨?_, ?_⟩
          · rw [hFinalStack]
            simpa [RunState.withEVM, RunState.pushReturn, List.append_assoc]
              using
                (Preservation.Frame.materializeStack_callEntry
                  (args := args) (callerStack := callerStack)
                  (callerTarget := callerTarget)
                  (returns := source.returns) (tokens := tokens)
                  (retc := retc) (token := token) hCaller)
          · calc
              eraseControl final
                  =
                eraseControl { target with stack := args ++ token :: callerTarget } :=
                    hFinalErase
              _ =
                eraseControl
                  { source.evm with stack := args ++ token :: callerTarget } :=
                    hRel.dataRel_replace_stack (args ++ token :: callerTarget)
              _ =
                eraseControl
                  { ((source.withEVM { source.evm with stack := args }).pushReturn
                        callerStack retc).evm with
                    stack := final.stack } := by
                    simp [RunState.withEVM, RunState.pushReturn, hFinalStack])

theorem source_callEntry_after_prologue_and_jump_withGasOracle
    {source : RunState} {target : EVMState}
    {tokens : List Word} {argc retc : Nat}
    {args callerStack : EvmYul.Stack Word} {token : Word}
    {entryLabel : Assembly.Label} {entryDest : Nat}
    {pre post : Assembly.Program} {oracle : GasOracle} {cursor : Nat}
    (hFits :
      AssemblyProgram.PCFitsFrom pre
        (([Assembly.Instr.push token] ++
          StackShuffle.sinkTopUnder args.length) ++
          [Assembly.Instr.jump entryLabel]))
    (hPc : target.pc = Assembly.Program.pcAfter pre)
    (hRel : Preservation.Frame.StateRel source target tokens)
    (hSplit :
      StackFrame.splitArgs? argc source.evm.stack =
        some (args, callerStack))
    (hArgBound : args.length ≤ 16)
    (hEntryLabel :
      Assembly.Program.labelPc
        (pre ++
          (([Assembly.Instr.push token] ++
            StackShuffle.sinkTopUnder args.length) ++
            [Assembly.Instr.jump entryLabel]) ++
          post)
        entryLabel = some entryDest) :
    ARunResultWithGasOracle
      (pre ++
        (([Assembly.Instr.push token] ++
          StackShuffle.sinkTopUnder args.length) ++
          [Assembly.Instr.jump entryLabel]) ++
        post)
      oracle cursor target
      (fun result cursorFinal =>
        match result with
        | .running final =>
            cursorFinal = cursor ∧
              Preservation.Frame.StateRel
                ((source.withEVM { source.evm with stack := args }).pushReturn
                  callerStack retc)
                final (token :: tokens) ∧
              final.pc = EvmYul.UInt256.ofNat entryDest
        | .halted _ => False) := by
  let prologue : Assembly.Program :=
    [Assembly.Instr.push token] ++ StackShuffle.sinkTopUnder args.length
  let callState : RunState :=
    (source.withEVM { source.evm with stack := args }).pushReturn
      callerStack retc
  have hFitsPrologue :
      AssemblyProgram.PCFitsFrom pre prologue := by
    exact
      AssemblyProgram.PCFitsFrom.left
        (pre := pre) (first := prologue)
        (second := [Assembly.Instr.jump entryLabel])
        (by simpa [prologue, List.append_assoc] using hFits)
  have hFitsJump :
      AssemblyProgram.PCFitsFrom (pre ++ prologue)
        [Assembly.Instr.jump entryLabel] := by
    exact
      AssemblyProgram.PCFitsFrom.right
        (pre := pre) (first := prologue)
        (second := [Assembly.Instr.jump entryLabel])
        (by simpa [prologue, List.append_assoc] using hFits)
  have hPrologueRun :=
    source_callEntry_after_prologue_withGasOracle
      (source := source) (target := target) (tokens := tokens)
      (argc := argc) (retc := retc) (args := args)
      (callerStack := callerStack) (token := token)
      (pre := pre) (post := [Assembly.Instr.jump entryLabel] ++ post)
      (oracle := oracle) (cursor := cursor)
      (by simpa [prologue] using hFitsPrologue)
      hPc hRel hSplit hArgBound
  refine
    ARunResultWithGasOracle.bind_running
      (program :=
        pre ++
          (([Assembly.Instr.push token] ++
            StackShuffle.sinkTopUnder args.length) ++
            [Assembly.Instr.jump entryLabel]) ++
          post)
      (middle := fun afterPrologue cursorAfterPrologue =>
        cursorAfterPrologue = cursor ∧
          Preservation.Frame.StateRel callState afterPrologue (token :: tokens) ∧
          afterPrologue.pc = Assembly.Program.pcAfter (pre ++ prologue))
      ?_ ?_
  · exact
      ARunResultWithGasOracle.mono
        (by
          simpa [prologue, callState, List.append_assoc] using hPrologueRun)
        (by
          intro result cursorAfterPrologue hResult
          cases result with
          | halted halt =>
              cases hResult
          | running afterPrologue =>
              simpa [prologue, callState] using hResult)
  · intro afterPrologue cursorAfterPrologue hAfterPrologue
    rcases hAfterPrologue with
      ⟨hCursorAfterPrologue, hRelAfterPrologue, hPcAfterPrologue⟩
    subst cursorAfterPrologue
    have hJumpLabel :
        Assembly.Program.labelPc
          ((pre ++ prologue) ++ [Assembly.Instr.jump entryLabel] ++ post)
          entryLabel = some entryDest := by
      simpa [prologue, List.append_assoc] using hEntryLabel
    rcases
      jump_stepResult_at_withGasOracle
        (label := entryLabel) (dest := entryDest)
        (pre := pre ++ prologue) (post := post)
        (source := callState) (target := afterPrologue)
        (tokens := token :: tokens) (oracle := oracle) (cursor := cursor)
        (AssemblyProgram.PCFitsFrom.start hFitsJump)
        hPcAfterPrologue hRelAfterPrologue hJumpLabel with
      ⟨afterJump, hJump, hRelAfterJump, hPcAfterJump⟩
    refine ⟨1, .running afterJump, cursor, ?_, ?_⟩
    · change
        Assembly.GasParametric.sourceRunNResultWithGasOracle
            (pre ++
              (([Assembly.Instr.push token] ++
                StackShuffle.sinkTopUnder args.length) ++
                [Assembly.Instr.jump entryLabel]) ++
              post)
            oracle 1 cursor afterPrologue =
          .ok (.running afterJump, cursor)
      unfold Assembly.GasParametric.sourceRunNResultWithGasOracle
      rw [show
          pre ++
              (([Assembly.Instr.push token] ++
                StackShuffle.sinkTopUnder args.length) ++
                [Assembly.Instr.jump entryLabel]) ++
              post =
            (pre ++ prologue) ++ [Assembly.Instr.jump entryLabel] ++ post by
          simp [prologue, List.append_assoc]]
      rw [hJump]
      rfl
    · exact ⟨rfl, hRelAfterJump, hPcAfterJump⟩

theorem source_returnAttach_after_remove_withGasOracle
    {callee : RunState} {target : EVMState}
    {tokens : List Word} {token : Word} {frame : ReturnDest}
    {returns : List ReturnDest} {pre post : Assembly.Program}
    {oracle : GasOracle} {cursor : Nat}
    (hFits :
      AssemblyProgram.PCFitsFrom pre
        (StackShuffle.removeBuriedUnder callee.evm.stack.length))
    (hPc : target.pc = Assembly.Program.pcAfter pre)
    (hRel : Preservation.Frame.StateRel callee target (token :: tokens))
    (hReturns : callee.returns = frame :: returns)
    (hBound : callee.evm.stack.length ≤ 16) :
    ARunResultWithGasOracle
      (pre ++ StackShuffle.removeBuriedUnder callee.evm.stack.length ++ post)
      oracle cursor target
      (fun result cursorFinal =>
        match result with
        | .running final =>
            cursorFinal = cursor ∧
              Preservation.Frame.StateRel
                { callee with
                  evm :=
                    { callee.evm with
                      stack := callee.evm.stack ++ frame.callerStack }
                  returns := returns }
                final tokens ∧
              final.pc =
                Assembly.Program.pcAfter
                  (pre ++
                    StackShuffle.removeBuriedUnder callee.evm.stack.length)
        | .halted _ => False) := by
  rcases
    Preservation.Frame.StateRel.caller_materialization_of_top_return
      hRel hReturns with
    ⟨callerTarget, hCaller, hTargetStack⟩
  have hTargetRecord :
      { target with stack := callee.evm.stack ++ token :: callerTarget } =
        target := by
    rw [← hTargetStack]
  have hRun :=
    StackShuffleGas.removeBuriedUnder_source_exists_withGasOracle
      (state := target) (returnValues := callee.evm.stack)
      (suffix := callerTarget) (token := token) (pre := pre) (post := post)
      (oracle := oracle) (cursor := cursor)
      hFits (by simpa using hPc) hBound
  exact ARunResultWithGasOracle.mono
    (by simpa [hTargetRecord] using hRun)
    (by
      intro result cursorFinal hResult
      cases result with
      | halted halt =>
          cases hResult
      | running final =>
          rcases hResult with
            ⟨hCursorFinal, hFinalStack, hFinalErase, hFinalPc⟩
          refine ⟨hCursorFinal, ?_, hFinalPc⟩
          refine ⟨?_, ?_⟩
          · rw [hFinalStack]
            exact Preservation.Frame.materializeStack_returnAttach hCaller
          · have hEraseTarget :
                eraseControl final =
                  eraseControl
                    { target with stack := callee.evm.stack ++ callerTarget } :=
              hFinalErase
            have hEraseSource :
                eraseControl
                    { target with stack := callee.evm.stack ++ callerTarget } =
                  eraseControl
                    { callee.evm with stack := callee.evm.stack ++ callerTarget } :=
              hRel.dataRel_replace_stack
                (callee.evm.stack ++ callerTarget)
            have hEraseFinalSource :
                eraseControl
                    { callee.evm with stack := callee.evm.stack ++ callerTarget } =
                  eraseControl
                    { { callee with
                          evm :=
                            { callee.evm with
                              stack := callee.evm.stack ++ frame.callerStack }
                          returns := returns }.evm with
                      stack := final.stack } := by
              simp [hFinalStack]
            exact hEraseTarget.trans (hEraseSource.trans hEraseFinalSource))

theorem label_runResult_at_withGasOracle {label : Assembly.Label}
    {pre post : Assembly.Program} {source : RunState} {target : EVMState}
    {tokens : List Word} {oracle : GasOracle} {cursor : Nat}
    (hFit : PCFits pre)
    (hPc : target.pc = Assembly.Program.pcAfter pre)
    (hRel : Preservation.Frame.StateRel source target tokens) :
    ARunResultWithGasOracle (pre ++ [Assembly.Instr.label label] ++ post)
      oracle cursor target
      (fun result cursorFinal =>
        match result with
        | .running target' =>
            cursorFinal = cursor ∧
              Preservation.Frame.StateRel source target' tokens ∧
                target'.pc =
                  Assembly.Program.pcAfter
                    (pre ++ [Assembly.Instr.label label])
        | .halted _ => False) := by
  rcases
    label_stepResult_at_withGasOracle
      (label := label) (pre := pre) (post := post)
      (oracle := oracle) (cursor := cursor) hFit hPc hRel with
    ⟨target', hStep, hRel', hPc'⟩
  refine ⟨1, .running target', cursor, ?_, ?_⟩
  · unfold Assembly.GasParametric.sourceRunNResultWithGasOracle
    rw [hStep]
    rfl
  · exact ⟨rfl, hRel', hPc'⟩

theorem dispatch_case_runResult_at_withGasOracle
    {caseLabel returnLabel : Assembly.Label}
    {dest : Nat} {pre post : Assembly.Program}
    {callee : RunState} {target : EVMState}
    {tokens : List Word} {token : Word} {frame : ReturnDest}
    {returns : List ReturnDest}
    {oracle : GasOracle} {cursor : Nat}
    (hFits :
      AssemblyProgram.PCFitsFrom pre
        ([Assembly.Instr.label caseLabel] ++
          StackShuffle.removeBuriedUnder callee.evm.stack.length ++
          [Assembly.Instr.jump returnLabel]))
    (hPc : target.pc = Assembly.Program.pcAfter pre)
    (hRel : Preservation.Frame.StateRel callee target (token :: tokens))
    (hReturns : callee.returns = frame :: returns)
    (hBound : callee.evm.stack.length ≤ 16)
    (hReturnLabel :
      Assembly.Program.labelPc
        (pre ++ [Assembly.Instr.label caseLabel] ++
          StackShuffle.removeBuriedUnder callee.evm.stack.length ++
          [Assembly.Instr.jump returnLabel] ++ post)
        returnLabel = some dest) :
    ARunResultWithGasOracle
      (pre ++ [Assembly.Instr.label caseLabel] ++
        StackShuffle.removeBuriedUnder callee.evm.stack.length ++
        [Assembly.Instr.jump returnLabel] ++ post)
      oracle cursor target
      (fun result cursorFinal =>
        match result with
        | .running final =>
            cursorFinal = cursor ∧
              Preservation.Frame.StateRel
                { callee with
                  evm :=
                    { callee.evm with
                      stack := callee.evm.stack ++ frame.callerStack }
                  returns := returns }
                final tokens ∧
              final.pc = EvmYul.UInt256.ofNat dest
        | .halted _ => False) := by
  let removeCode := StackShuffle.removeBuriedUnder callee.evm.stack.length
  let returned : RunState :=
    { callee with
      evm :=
        { callee.evm with stack := callee.evm.stack ++ frame.callerStack }
      returns := returns }
  have hFitsAfterLabel :
      AssemblyProgram.PCFitsFrom (pre ++ [Assembly.Instr.label caseLabel])
        (removeCode ++ [Assembly.Instr.jump returnLabel]) := by
    exact
      AssemblyProgram.PCFitsFrom.right
        (pre := pre) (first := [Assembly.Instr.label caseLabel])
        (second := removeCode ++ [Assembly.Instr.jump returnLabel])
        (by simpa [removeCode, List.append_assoc] using hFits)
  have hFitsRemove :
      AssemblyProgram.PCFitsFrom (pre ++ [Assembly.Instr.label caseLabel])
        removeCode := by
    exact
      AssemblyProgram.PCFitsFrom.left
        (pre := pre ++ [Assembly.Instr.label caseLabel])
        (first := removeCode) (second := [Assembly.Instr.jump returnLabel])
        hFitsAfterLabel
  have hFitsAfterRemove :
      AssemblyProgram.PCFitsFrom
        (pre ++ [Assembly.Instr.label caseLabel] ++ removeCode)
        [Assembly.Instr.jump returnLabel] := by
    exact
      AssemblyProgram.PCFitsFrom.right
        (pre := pre ++ [Assembly.Instr.label caseLabel])
        (first := removeCode) (second := [Assembly.Instr.jump returnLabel])
        hFitsAfterLabel
  have hLabelRun :=
    label_runResult_at_withGasOracle
      (label := caseLabel) (pre := pre)
      (post := removeCode ++ [Assembly.Instr.jump returnLabel] ++ post)
      (source := callee) (target := target) (tokens := token :: tokens)
      (oracle := oracle) (cursor := cursor)
      (AssemblyProgram.PCFitsFrom.start hFits) hPc hRel
  refine
    ARunResultWithGasOracle.bind_running
      (program :=
        pre ++ [Assembly.Instr.label caseLabel] ++
          StackShuffle.removeBuriedUnder callee.evm.stack.length ++
          [Assembly.Instr.jump returnLabel] ++ post)
      (middle := fun afterLabel cursorAfterLabel =>
        cursorAfterLabel = cursor ∧
          Preservation.Frame.StateRel callee afterLabel (token :: tokens) ∧
          afterLabel.pc =
            Assembly.Program.pcAfter
              (pre ++ [Assembly.Instr.label caseLabel]))
      ?_ ?_
  · exact
      ARunResultWithGasOracle.mono
        (by simpa [removeCode, List.append_assoc] using hLabelRun)
        (by
          intro result cursorAfterLabel hResult
          cases result with
          | halted halt =>
              cases hResult
          | running afterLabel =>
              exact hResult)
  · intro afterLabel cursorAfterLabel hAfterLabel
    rcases hAfterLabel with
      ⟨hCursorAfterLabel, hRelAfterLabel, hPcAfterLabel⟩
    subst cursorAfterLabel
    have hRemoveRun :=
      source_returnAttach_after_remove_withGasOracle
        (callee := callee) (target := afterLabel) (tokens := tokens)
        (token := token) (frame := frame) (returns := returns)
        (pre := pre ++ [Assembly.Instr.label caseLabel])
        (post := [Assembly.Instr.jump returnLabel] ++ post)
        (oracle := oracle) (cursor := cursor)
        (by simpa [removeCode] using hFitsRemove)
        hPcAfterLabel hRelAfterLabel hReturns hBound
    refine
      ARunResultWithGasOracle.bind_running
        (program :=
          pre ++ [Assembly.Instr.label caseLabel] ++
            StackShuffle.removeBuriedUnder callee.evm.stack.length ++
            [Assembly.Instr.jump returnLabel] ++ post)
        (middle := fun afterRemove cursorAfterRemove =>
          cursorAfterRemove = cursor ∧
            Preservation.Frame.StateRel returned afterRemove tokens ∧
            afterRemove.pc =
              Assembly.Program.pcAfter
                ((pre ++ [Assembly.Instr.label caseLabel]) ++ removeCode))
        ?_ ?_
    · exact
        ARunResultWithGasOracle.mono
          (by
            simpa [returned, removeCode, List.append_assoc] using hRemoveRun)
          (by
            intro result cursorAfterRemove hResult
            cases result with
            | halted halt =>
                cases hResult
            | running afterRemove =>
                rcases hResult with
                  ⟨hCursorAfterRemove, hRelReturned, hPcAfterRemove⟩
                exact ⟨hCursorAfterRemove, hRelReturned,
                  by simpa [removeCode] using hPcAfterRemove⟩)
    · intro afterRemove cursorAfterRemove hAfterRemove
      rcases hAfterRemove with
        ⟨hCursorAfterRemove, hRelAfterRemove, hPcAfterRemove⟩
      subst cursorAfterRemove
      have hLabelJump :
          Assembly.Program.labelPc
            ((pre ++ [Assembly.Instr.label caseLabel] ++ removeCode) ++
              [Assembly.Instr.jump returnLabel] ++ post)
            returnLabel = some dest := by
        simpa [removeCode, List.append_assoc] using hReturnLabel
      rcases
        jump_stepResult_at_withGasOracle
          (label := returnLabel) (dest := dest)
          (pre := pre ++ [Assembly.Instr.label caseLabel] ++ removeCode)
          (post := post) (source := returned) (target := afterRemove)
          (tokens := tokens) (oracle := oracle) (cursor := cursor)
          (AssemblyProgram.PCFitsFrom.start hFitsAfterRemove)
          hPcAfterRemove hRelAfterRemove hLabelJump with
        ⟨final, hJump, hRelFinal, hPcFinal⟩
      refine ⟨1, .running final, cursor, ?_, ?_⟩
      · unfold Assembly.GasParametric.sourceRunNResultWithGasOracle
        rw [show
          pre ++ [Assembly.Instr.label caseLabel] ++
              StackShuffle.removeBuriedUnder callee.evm.stack.length ++
              [Assembly.Instr.jump returnLabel] ++ post =
            (pre ++ [Assembly.Instr.label caseLabel] ++ removeCode) ++
              [Assembly.Instr.jump returnLabel] ++ post by
          simp [removeCode, List.append_assoc]]
        rw [hJump]
        rfl
      · exact ⟨rfl, hRelFinal, hPcFinal⟩

theorem dispatch_mismatched_test_runResult_at_withGasOracle
    {caseLabel : Assembly.Label} {caseDest : Nat}
    {pre post : Assembly.Program}
    {callee : RunState} {target : EVMState}
    {tokens : List Word} {token probe : Word} {frame : ReturnDest}
    {returns : List ReturnDest}
    {oracle : GasOracle} {cursor : Nat}
    (hNe : probe ≠ token)
    (hFits :
      AssemblyProgram.PCFitsFrom pre
        [ StackShuffle.dupInstr (callee.evm.stack.length + 1)
        , Assembly.Instr.push probe
        , Assembly.Instr.prim .eq
        , Assembly.Instr.jumpi caseLabel
        ])
    (hPc : target.pc = Assembly.Program.pcAfter pre)
    (hRel : Preservation.Frame.StateRel callee target (token :: tokens))
    (hReturns : callee.returns = frame :: returns)
    (hBound : callee.evm.stack.length < 16)
    (hCaseLabel :
      Assembly.Program.labelPc
        (pre ++
          [ StackShuffle.dupInstr (callee.evm.stack.length + 1)
          , Assembly.Instr.push probe
          , Assembly.Instr.prim .eq
          , Assembly.Instr.jumpi caseLabel
          ] ++ post)
        caseLabel = some caseDest) :
    ARunResultWithGasOracle
      (pre ++
        [ StackShuffle.dupInstr (callee.evm.stack.length + 1)
        , Assembly.Instr.push probe
        , Assembly.Instr.prim .eq
        , Assembly.Instr.jumpi caseLabel
        ] ++ post)
      oracle cursor target
      (fun result cursorFinal =>
        match result with
        | .running final =>
            cursorFinal = cursor ∧
              Preservation.Frame.StateRel callee final (token :: tokens) ∧
              final.pc =
                Assembly.Program.pcAfter
                  (pre ++
                    [ StackShuffle.dupInstr (callee.evm.stack.length + 1)
                    , Assembly.Instr.push probe
                    , Assembly.Instr.prim .eq
                    , Assembly.Instr.jumpi caseLabel
                    ])
        | .halted _ => False) := by
  rcases
    Preservation.Frame.StateRel.caller_materialization_of_top_return
      hRel hReturns with
    ⟨callerTarget, hCaller, hTargetStack⟩
  have hTargetRecord :
      { target with stack := callee.evm.stack ++ token :: callerTarget } =
        target := by
    rw [← hTargetStack]
  have hRun :=
    StackShuffleGas.dispatchCondition_jumpi_source_exists_withGasOracle
      (state := target) (returnValues := callee.evm.stack)
      (suffix := callerTarget) (token := token) (probe := probe)
      (label := caseLabel) (dest := caseDest) (pre := pre) (post := post)
      (oracle := oracle) (cursor := cursor)
      hFits (by simpa [hTargetRecord] using hPc) hBound hCaseLabel
  exact
    ARunResultWithGasOracle.mono
      (by simpa [hTargetRecord] using hRun)
      (by
        intro result cursorFinal hResult
        cases result with
        | halted halt =>
            cases hResult
        | running final =>
            rcases hResult with
              ⟨hCursorFinal, hStack, hErase, hPcFinal⟩
            have hRelFinal :
                Preservation.Frame.StateRel callee final (token :: tokens) := by
              refine ⟨?_, ?_⟩
              · rw [hReturns]
                simp [Preservation.Frame.materializeStack, hCaller, hStack]
              · calc
                  eraseControl final = eraseControl target := by
                    simpa [hTargetRecord] using hErase
                  _ =
                    eraseControl
                      { target with
                        stack := callee.evm.stack ++ token :: callerTarget } := by
                      rw [hTargetRecord]
                  _ =
                    eraseControl
                      { callee.evm with
                        stack := callee.evm.stack ++ token :: callerTarget } :=
                      hRel.dataRel_replace_stack
                        (callee.evm.stack ++ token :: callerTarget)
                  _ =
                    eraseControl { callee.evm with stack := final.stack } := by
                      rw [hStack]
            refine ⟨hCursorFinal, hRelFinal, ?_⟩
            simpa [hNe] using hPcFinal)

theorem dispatch_selected_site_runResult_at_withGasOracle
    {caseLabel returnLabel : Assembly.Label} {returnDest : Nat}
    {pre between post : Assembly.Program}
    {callee : RunState} {target : EVMState}
    {tokens : List Word} {token : Word} {frame : ReturnDest}
    {returns : List ReturnDest}
    {oracle : GasOracle} {cursor : Nat}
    (hFits :
      AssemblyProgram.PCFitsFrom pre
        ([ StackShuffle.dupInstr (callee.evm.stack.length + 1)
         , Assembly.Instr.push token
         , Assembly.Instr.prim .eq
         , Assembly.Instr.jumpi caseLabel
         ] ++ between ++
          [Assembly.Instr.label caseLabel] ++
          StackShuffle.removeBuriedUnder callee.evm.stack.length ++
          [Assembly.Instr.jump returnLabel]))
    (hPc : target.pc = Assembly.Program.pcAfter pre)
    (hRel : Preservation.Frame.StateRel callee target (token :: tokens))
    (hReturns : callee.returns = frame :: returns)
    (hBound : callee.evm.stack.length < 16)
    (hExact :
      ExactLabels
        (pre ++
          [ StackShuffle.dupInstr (callee.evm.stack.length + 1)
          , Assembly.Instr.push token
          , Assembly.Instr.prim .eq
          , Assembly.Instr.jumpi caseLabel
          ] ++ between ++
          [Assembly.Instr.label caseLabel] ++
          StackShuffle.removeBuriedUnder callee.evm.stack.length ++
          [Assembly.Instr.jump returnLabel] ++ post))
    (hReturnLabel :
      Assembly.Program.labelPc
        (pre ++
          [ StackShuffle.dupInstr (callee.evm.stack.length + 1)
          , Assembly.Instr.push token
          , Assembly.Instr.prim .eq
          , Assembly.Instr.jumpi caseLabel
          ] ++ between ++
          [Assembly.Instr.label caseLabel] ++
          StackShuffle.removeBuriedUnder callee.evm.stack.length ++
          [Assembly.Instr.jump returnLabel] ++ post)
        returnLabel = some returnDest) :
    ARunResultWithGasOracle
      (pre ++
        [ StackShuffle.dupInstr (callee.evm.stack.length + 1)
        , Assembly.Instr.push token
        , Assembly.Instr.prim .eq
        , Assembly.Instr.jumpi caseLabel
        ] ++ between ++
        [Assembly.Instr.label caseLabel] ++
        StackShuffle.removeBuriedUnder callee.evm.stack.length ++
        [Assembly.Instr.jump returnLabel] ++ post)
      oracle cursor target
      (fun result cursorFinal =>
        match result with
        | .running final =>
            cursorFinal = cursor ∧
              Preservation.Frame.StateRel
                { callee with
                  evm :=
                    { callee.evm with
                      stack := callee.evm.stack ++ frame.callerStack }
                  returns := returns }
                final tokens ∧
              final.pc = EvmYul.UInt256.ofNat returnDest
        | .halted _ => False) := by
  let testCode : Assembly.Program :=
    [ StackShuffle.dupInstr (callee.evm.stack.length + 1)
    , Assembly.Instr.push token
    , Assembly.Instr.prim .eq
    , Assembly.Instr.jumpi caseLabel
    ]
  let removeCode := StackShuffle.removeBuriedUnder callee.evm.stack.length
  let casePre := pre ++ testCode ++ between
  let fullProgram :=
    pre ++ testCode ++ between ++ [Assembly.Instr.label caseLabel] ++
      removeCode ++ [Assembly.Instr.jump returnLabel] ++ post
  let returned : RunState :=
    { callee with
      evm :=
        { callee.evm with stack := callee.evm.stack ++ frame.callerStack }
      returns := returns }
  rcases
    Preservation.Frame.StateRel.caller_materialization_of_top_return
      hRel hReturns with
    ⟨callerTarget, hCaller, hTargetStack⟩
  have hTargetRecord :
      { target with stack := callee.evm.stack ++ token :: callerTarget } =
        target := by
    rw [← hTargetStack]
  have hExactFull : ExactLabels fullProgram := by
    simpa [fullProgram, testCode, removeCode, List.append_assoc] using hExact
  have hFitsTest :
      AssemblyProgram.PCFitsFrom pre testCode := by
    exact
      AssemblyProgram.PCFitsFrom.left
        (pre := pre) (first := testCode)
        (second := between ++ [Assembly.Instr.label caseLabel] ++
          removeCode ++ [Assembly.Instr.jump returnLabel])
        (by simpa [testCode, removeCode, List.append_assoc] using hFits)
  have hFitsCase :
      AssemblyProgram.PCFitsFrom casePre
        ([Assembly.Instr.label caseLabel] ++ removeCode ++
          [Assembly.Instr.jump returnLabel]) := by
    simpa [casePre, List.append_assoc] using
      (AssemblyProgram.PCFitsFrom.right
        (pre := pre) (first := testCode ++ between)
        (second :=
          [Assembly.Instr.label caseLabel] ++ removeCode ++
            [Assembly.Instr.jump returnLabel])
        (by simpa [testCode, removeCode, List.append_assoc] using hFits))
  have hCaseLabel :
      Assembly.Program.labelPc fullProgram caseLabel =
        some (Assembly.Program.byteLength casePre) := by
    have hHere :=
      hExactFull.labelPc_at casePre caseLabel
        (removeCode ++ [Assembly.Instr.jump returnLabel] ++ post)
        (by simp [fullProgram, casePre, testCode, removeCode, List.append_assoc])
    simpa [fullProgram] using hHere
  have hTestRun :=
    StackShuffleGas.dispatchCondition_jumpi_source_exists_withGasOracle
      (state := target) (returnValues := callee.evm.stack)
      (suffix := callerTarget) (token := token) (probe := token)
      (label := caseLabel) (dest := Assembly.Program.byteLength casePre)
      (pre := pre)
      (post := between ++ [Assembly.Instr.label caseLabel] ++ removeCode ++
        [Assembly.Instr.jump returnLabel] ++ post)
      (oracle := oracle) (cursor := cursor)
      (by simpa [testCode] using hFitsTest)
      (by simpa [hTargetRecord] using hPc)
      hBound
      (by simpa [fullProgram, testCode, removeCode, List.append_assoc] using
        hCaseLabel)
  refine
    ARunResultWithGasOracle.bind_running
      (program :=
        pre ++
          [ StackShuffle.dupInstr (callee.evm.stack.length + 1)
          , Assembly.Instr.push token
          , Assembly.Instr.prim .eq
          , Assembly.Instr.jumpi caseLabel
          ] ++ between ++
          [Assembly.Instr.label caseLabel] ++
          StackShuffle.removeBuriedUnder callee.evm.stack.length ++
          [Assembly.Instr.jump returnLabel] ++ post)
      (middle := fun afterTest cursorAfterTest =>
        cursorAfterTest = cursor ∧
          Preservation.Frame.StateRel callee afterTest (token :: tokens) ∧
          afterTest.pc = Assembly.Program.pcAfter casePre)
      ?_ ?_
  · exact
      ARunResultWithGasOracle.mono
        (by
          simpa [testCode, removeCode, fullProgram, hTargetRecord,
            List.append_assoc] using hTestRun)
        (by
          intro result cursorAfterTest hResult
          cases result with
          | halted halt =>
              cases hResult
          | running afterTest =>
              rcases hResult with
                ⟨hCursorAfterTest, hStack, hErase, hPcAfterTest⟩
              have hRelAfterTest :
                  Preservation.Frame.StateRel callee afterTest (token :: tokens) := by
                refine ⟨?_, ?_⟩
                · rw [hReturns]
                  simp [Preservation.Frame.materializeStack, hCaller, hStack]
                · calc
                    eraseControl afterTest = eraseControl target := hErase
                    _ =
                      eraseControl
                        { target with
                          stack := callee.evm.stack ++ token :: callerTarget } := by
                        rw [hTargetRecord]
                    _ =
                      eraseControl
                        { callee.evm with
                          stack := callee.evm.stack ++ token :: callerTarget } :=
                        hRel.dataRel_replace_stack
                          (callee.evm.stack ++ token :: callerTarget)
                    _ =
                      eraseControl { callee.evm with stack := afterTest.stack } := by
                        rw [hStack]
              refine ⟨hCursorAfterTest, hRelAfterTest, ?_⟩
              simpa [casePre, testCode] using hPcAfterTest)
  · intro afterTest cursorAfterTest hAfterTest
    rcases hAfterTest with
      ⟨hCursorAfterTest, hRelAfterTest, hPcAfterTest⟩
    subst cursorAfterTest
    have hCaseRun :=
      dispatch_case_runResult_at_withGasOracle
        (caseLabel := caseLabel) (returnLabel := returnLabel)
        (dest := returnDest) (pre := casePre) (post := post)
        (callee := callee) (target := afterTest) (tokens := tokens)
        (token := token) (frame := frame) (returns := returns)
        (oracle := oracle) (cursor := cursor)
        (by simpa [removeCode] using hFitsCase)
        hPcAfterTest hRelAfterTest hReturns (by omega)
        (by
          simpa [fullProgram, casePre, testCode, removeCode, List.append_assoc]
            using hReturnLabel)
    simpa [casePre, testCode, removeCode, List.append_assoc] using hCaseRun

theorem jump_then_label_runResult_at_withGasOracle {label : Assembly.Label}
    {pre between post : Assembly.Program} {source : RunState}
    {target : EVMState} {tokens : List Word}
    {oracle : GasOracle} {cursor : Nat}
    (hFitJump : PCFits pre)
    (hFitLabel : PCFits (pre ++ [Assembly.Instr.jump label] ++ between))
    (hPc : target.pc = Assembly.Program.pcAfter pre)
    (hRel : Preservation.Frame.StateRel source target tokens)
    (hLabel :
      Assembly.Program.labelPc
          (pre ++ [Assembly.Instr.jump label] ++ between ++
            [Assembly.Instr.label label] ++ post) label =
        some
          (Assembly.Program.byteLength
            (pre ++ [Assembly.Instr.jump label] ++ between))) :
    ARunResultWithGasOracle
      (pre ++ [Assembly.Instr.jump label] ++ between ++
        [Assembly.Instr.label label] ++ post)
      oracle cursor target
      (fun result cursorFinal =>
        match result with
        | .running target' =>
            cursorFinal = cursor ∧
              Preservation.Frame.StateRel source target' tokens ∧
                target'.pc =
                  Assembly.Program.pcAfter
                    (pre ++ [Assembly.Instr.jump label] ++ between ++
                      [Assembly.Instr.label label])
        | .halted _ => False) := by
  let labelPre := pre ++ [Assembly.Instr.jump label] ++ between
  have hJumpLabel :
      Assembly.Program.labelPc
          (pre ++ [Assembly.Instr.jump label] ++
            (between ++ [Assembly.Instr.label label] ++ post)) label =
        some (Assembly.Program.byteLength labelPre) := by
    simpa [labelPre, List.append_assoc] using hLabel
  rcases
    jump_stepResult_at_withGasOracle (label := label)
      (dest := Assembly.Program.byteLength labelPre)
      (pre := pre) (post := between ++ [Assembly.Instr.label label] ++ post)
      (oracle := oracle) (cursor := cursor)
      hFitJump hPc hRel hJumpLabel with
    ⟨targetAfterJump, hJump, hRelAfterJump, hPcAfterJump⟩
  refine
    ARunResultWithGasOracle.bind_running
      (program :=
        pre ++ [Assembly.Instr.jump label] ++ between ++
          [Assembly.Instr.label label] ++ post)
      (middle := fun targetAfterJump cursorAfterJump =>
        cursorAfterJump = cursor ∧
          Preservation.Frame.StateRel source targetAfterJump tokens ∧
            targetAfterJump.pc = Assembly.Program.pcAfter labelPre)
      ?_ ?_
  · refine ⟨1, .running targetAfterJump, cursor, ?_, ?_⟩
    · change
        Assembly.GasParametric.sourceRunNResultWithGasOracle
            (pre ++ [Assembly.Instr.jump label] ++ between ++
              [Assembly.Instr.label label] ++ post)
            oracle 1 cursor target =
          .ok (.running targetAfterJump, cursor)
      rw [show
          pre ++ [Assembly.Instr.jump label] ++ between ++
              [Assembly.Instr.label label] ++ post =
            pre ++ [Assembly.Instr.jump label] ++
              (between ++ [Assembly.Instr.label label] ++ post) by
          simp [List.append_assoc]]
      unfold Assembly.GasParametric.sourceRunNResultWithGasOracle
      rw [hJump]
      rfl
    · exact ⟨rfl, hRelAfterJump, hPcAfterJump⟩
  · intro targetAfterJump cursorAfterJump hMiddle
    rcases hMiddle with ⟨hCursor, hRelMiddle, hPcMiddle⟩
    subst cursorAfterJump
    have hLabelRun :=
      label_runResult_at_withGasOracle
        (label := label) (pre := labelPre) (post := post)
        (oracle := oracle) (cursor := cursor)
        hFitLabel hPcMiddle hRelMiddle
    exact
      ARunResultWithGasOracle.mono
        (by simpa [labelPre, List.append_assoc] using hLabelRun)
        (by
          intro result cursorFinal hResult
          cases result with
          | halted halt =>
              cases hResult
          | running target' =>
              simpa [labelPre, List.append_assoc] using hResult)

theorem pop_stepResult_at_withGasOracle {pre post : Assembly.Program}
    {source : RunState} {target : EVMState} {tokens : List Word}
    {stack : EvmYul.Stack Word} {value : Word}
    {oracle : GasOracle} {cursor : Nat}
    (hFit : PCFits pre)
    (hPc : target.pc = Assembly.Program.pcAfter pre)
    (hRel : Preservation.Frame.StateRel source target tokens)
    (hPop : source.evm.stack.pop = some (stack, value)) :
    ∃ targetFinal,
      Assembly.GasParametric.sourceStepResultWithGasOracle
          (pre ++ [Assembly.Instr.prim .pop] ++ post) oracle cursor target =
        .ok (.running targetFinal, cursor) ∧
        Preservation.Frame.StateRel
          (source.withEVM { source.evm with stack := stack })
          targetFinal tokens ∧
        targetFinal.pc =
          Assembly.Program.pcAfter (pre ++ [Assembly.Instr.prim .pop]) := by
  rcases hRel.pop_visible hPop with
    ⟨suffix, hTargetStack, hTargetPop, hRelAfterPopStack⟩
  let targetFinal : EVMState :=
    target.replaceStackAndIncrPC (stack ++ suffix)
  refine ⟨targetFinal, ?_, ?_, ?_⟩
  · unfold Assembly.GasParametric.sourceStepResultWithGasOracle
    have hAt :
        Assembly.Program.instrAtPc
            (pre ++ [Assembly.Instr.prim .pop] ++ post)
            target.pc.toNat =
          some (Assembly.Program.byteLength pre, Assembly.Instr.prim .pop) := by
      unfold Assembly.Program.instrAtPc
      rw [hPc, hFit]
      simpa using
        Assembly.Program.instrAtPcFrom_append_boundary_cons
          pre post (Assembly.Instr.prim .pop) 0
    rw [hAt]
    unfold Assembly.GasParametric.sourceStepAtWithGasOracle
    change
      (do
        let (state', cursor') ←
          Assembly.GasParametric.PrimOp.stepWithGasOracle oracle cursor
            .pop target
        match (Assembly.Instr.prim .pop).haltKind? with
        | some kind =>
            Except.ok
              (Assembly.StepResult.halted
                { kind := kind
                  state := state'
                  output := kind.output state' },
                cursor')
        | none =>
            Except.ok (Assembly.StepResult.running state', cursor')) =
        Except.ok (Assembly.StepResult.running targetFinal, cursor)
    have hTargetStep :
        Assembly.GasParametric.PrimOp.stepWithGasOracle oracle cursor .pop
            target =
          .ok (targetFinal, cursor) := by
      unfold Assembly.GasParametric.PrimOp.stepWithGasOracle
      unfold Assembly.PrimOp.step
      simp [Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
        hTargetPop, targetFinal]
    rw [hTargetStep]
    rfl
  · refine ⟨?_, ?_⟩
    · simpa [targetFinal, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC] using hRelAfterPopStack.stackRel
    · calc
        eraseControl targetFinal
            = eraseControl { target with stack := stack ++ suffix } := by
                simp [targetFinal, eraseControl, Assembly.eraseGas,
                  EvmYul.EVM.State.replaceStackAndIncrPC,
                  EvmYul.EVM.State.incrPC]
        _ =
            eraseControl
              { (source.withEVM { source.evm with stack := stack }).evm with
                stack := (stack ++ suffix) } := hRelAfterPopStack.dataRel
  · simp [targetFinal, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, hPc, Assembly.Program.pcAfter,
      Assembly.Program.byteLength_append, Assembly.Program.byteLength,
      Assembly.Instr.byteSize, Assembly.UInt256_ofNat_add]

end FrameStateRel

namespace DispatchPreservation

def testCode (base : LabelSupply) (retc idx : Nat) (site : CallSite) :
    Assembly.Program :=
  [ StackShuffle.dupInstr (retc + 1)
  , Assembly.Instr.push site.token
  , Assembly.Instr.prim .eq
  , Assembly.Instr.jumpi (LabelSupply.label base idx)
  ]

def caseCode (base : LabelSupply) (retc idx : Nat) (site : CallSite) :
    Assembly.Program :=
  [Assembly.Instr.label (LabelSupply.label base idx)] ++
    StackShuffle.removeBuriedUnder retc ++
    [Assembly.Instr.jump site.returnLabel]

def tableCode (base : LabelSupply) (retc idx : Nat)
    (casePrefix : Assembly.Program) (sites : List CallSite) :
    Assembly.Program :=
  Dispatch.testsForRetc base retc idx sites ++
    [Assembly.Instr.prim .invalid] ++
    casePrefix ++
    Dispatch.casesForRetc base retc idx sites

@[simp] theorem legacy_testCode_eq (base : LabelSupply)
    (retc idx : Nat) (site : CallSite) :
    _root_.EvmCompiler.Structured.Preservation.DispatchPreservation.testCode
        base retc idx site =
      testCode base retc idx site := by
  rfl

@[simp] theorem legacy_caseCode_eq (base : LabelSupply)
    (retc idx : Nat) (site : CallSite) :
    _root_.EvmCompiler.Structured.Preservation.DispatchPreservation.caseCode
        base retc idx site =
      caseCode base retc idx site := by
  rfl

@[simp] theorem testsForRetc_cons (base : LabelSupply)
    (retc idx : Nat) (site : CallSite) (rest : List CallSite) :
    Dispatch.testsForRetc base retc idx (site :: rest) =
      testCode base retc idx site ++
        Dispatch.testsForRetc base retc (idx + 1) rest := by
  simp [Dispatch.testsForRetc, testCode]

@[simp] theorem casesForRetc_cons (base : LabelSupply)
    (retc idx : Nat) (site : CallSite) (rest : List CallSite) :
    Dispatch.casesForRetc base retc idx (site :: rest) =
      caseCode base retc idx site ++
        Dispatch.casesForRetc base retc (idx + 1) rest := by
  simp [Dispatch.casesForRetc, caseCode, List.append_assoc]

set_option maxHeartbeats 800000 in
theorem selected_table_runResult_at_withGasOracle
    {base : LabelSupply} {retc idx : Nat}
    {casePrefix post pre : Assembly.Program}
    {sites : List CallSite} {site : CallSite}
    {returnDest : Nat}
    {callee : RunState} {target : EVMState}
    {tokens : List Word} {token : Word} {frame : ReturnDest}
    {returns : List ReturnDest}
    {oracle : GasOracle} {cursor : Nat}
    (hMem : site ∈ sites)
    (hNoDup : (sites.map CallSite.token).Nodup)
    (hToken : site.token = token)
    (hRetc : callee.evm.stack.length = retc)
    (hFits :
      AssemblyProgram.PCFitsFrom pre
        (tableCode base retc idx casePrefix sites))
    (hPc : target.pc = Assembly.Program.pcAfter pre)
    (hRel : Preservation.Frame.StateRel callee target (token :: tokens))
    (hReturns : callee.returns = frame :: returns)
    (hBound : retc < 16)
    (hExact :
      ExactLabels (pre ++ tableCode base retc idx casePrefix sites ++ post))
    (hReturnLabel :
      Assembly.Program.labelPc
        (pre ++ tableCode base retc idx casePrefix sites ++ post)
        site.returnLabel = some returnDest) :
    ARunResultWithGasOracle
      (pre ++ tableCode base retc idx casePrefix sites ++ post)
      oracle cursor target
      (fun result cursorFinal =>
        match result with
        | .running final =>
            cursorFinal = cursor ∧
              Preservation.Frame.StateRel
                { callee with
                  evm :=
                    { callee.evm with
                      stack := callee.evm.stack ++ frame.callerStack }
                  returns := returns }
                final tokens ∧
              final.pc = EvmYul.UInt256.ofNat returnDest
        | .halted _ => False) := by
  induction sites generalizing pre idx casePrefix target with
  | nil =>
      cases hMem
  | cons head rest ih =>
      have hHeadNotIn : head.token ∉ rest.map CallSite.token := by
        exact (List.nodup_cons.mp (by simpa using hNoDup)).1
      have hNoDupRest : (rest.map CallSite.token).Nodup := by
        exact (List.nodup_cons.mp (by simpa using hNoDup)).2
      let headTest := testCode base retc idx head
      let headCase := caseCode base retc idx head
      let testsRest := Dispatch.testsForRetc base retc (idx + 1) rest
      let casesRest := Dispatch.casesForRetc base retc (idx + 1) rest
      have hMemCons : site = head ∨ site ∈ rest := by
        simpa using hMem
      rcases hMemCons with hEq | hMemRest
      · subst head
        have hFitsSelected :
              AssemblyProgram.PCFitsFrom pre
                ([ StackShuffle.dupInstr (callee.evm.stack.length + 1)
                 , Assembly.Instr.push token
                 , Assembly.Instr.prim .eq
                 , Assembly.Instr.jumpi (LabelSupply.label base idx)
                 ] ++
                  (testsRest ++ [Assembly.Instr.prim .invalid] ++ casePrefix) ++
                  [Assembly.Instr.label (LabelSupply.label base idx)] ++
                  StackShuffle.removeBuriedUnder callee.evm.stack.length ++
                  [Assembly.Instr.jump site.returnLabel]) := by
            exact
              AssemblyProgram.PCFitsFrom.left
                (pre := pre)
                (first :=
                  [ StackShuffle.dupInstr (callee.evm.stack.length + 1)
                  , Assembly.Instr.push token
                  , Assembly.Instr.prim .eq
                  , Assembly.Instr.jumpi (LabelSupply.label base idx)
                  ] ++
                  (testsRest ++ [Assembly.Instr.prim .invalid] ++ casePrefix) ++
                  [Assembly.Instr.label (LabelSupply.label base idx)] ++
                  StackShuffle.removeBuriedUnder callee.evm.stack.length ++
                  [Assembly.Instr.jump site.returnLabel])
                (second := casesRest)
                (by
                  simpa [tableCode, headTest, headCase, testsRest, casesRest,
                    testCode, caseCode, hRetc, hToken, List.append_assoc] using hFits)
        have hExactSelected :
              ExactLabels
                (pre ++
                  [ StackShuffle.dupInstr (callee.evm.stack.length + 1)
                  , Assembly.Instr.push token
                  , Assembly.Instr.prim .eq
                  , Assembly.Instr.jumpi (LabelSupply.label base idx)
                  ] ++
                  (testsRest ++ [Assembly.Instr.prim .invalid] ++ casePrefix) ++
                  [Assembly.Instr.label (LabelSupply.label base idx)] ++
                  StackShuffle.removeBuriedUnder callee.evm.stack.length ++
                  [Assembly.Instr.jump site.returnLabel] ++ casesRest ++ post) := by
            simpa [tableCode, headTest, headCase, testsRest, casesRest,
              testCode, caseCode, hRetc, hToken, List.append_assoc] using hExact
        have hReturnSelected :
              Assembly.Program.labelPc
                (pre ++
                  [ StackShuffle.dupInstr (callee.evm.stack.length + 1)
                  , Assembly.Instr.push token
                  , Assembly.Instr.prim .eq
                  , Assembly.Instr.jumpi (LabelSupply.label base idx)
                  ] ++
                  (testsRest ++ [Assembly.Instr.prim .invalid] ++ casePrefix) ++
                  [Assembly.Instr.label (LabelSupply.label base idx)] ++
                  StackShuffle.removeBuriedUnder callee.evm.stack.length ++
                  [Assembly.Instr.jump site.returnLabel] ++ casesRest ++ post)
                site.returnLabel = some returnDest := by
            simpa [tableCode, headTest, headCase, testsRest, casesRest,
              testCode, caseCode, hRetc, hToken, List.append_assoc] using hReturnLabel
        have hRun :=
            FrameStateRel.dispatch_selected_site_runResult_at_withGasOracle
              (caseLabel := LabelSupply.label base idx)
              (returnLabel := site.returnLabel) (returnDest := returnDest)
              (pre := pre)
              (between := testsRest ++ [Assembly.Instr.prim .invalid] ++ casePrefix)
              (post := casesRest ++ post)
              (callee := callee) (target := target) (tokens := tokens)
              (token := token) (frame := frame) (returns := returns)
              (oracle := oracle) (cursor := cursor)
              hFitsSelected hPc hRel hReturns (by omega)
              (by simpa [List.append_assoc] using hExactSelected)
              (by simpa [List.append_assoc] using hReturnSelected)
        simpa [tableCode, headTest, headCase, testsRest, casesRest,
            testCode, caseCode, hRetc, hToken, List.append_assoc] using hRun
      ·
          have hNe : head.token ≠ token := by
            intro hEq
            have hSiteTokenMem : site.token ∈ rest.map CallSite.token :=
              List.mem_map_of_mem (f := CallSite.token) hMemRest
            apply hHeadNotIn
            simpa [hEq, hToken] using hSiteTokenMem
          let headCasePre :=
            pre ++ headTest ++ testsRest ++ [Assembly.Instr.prim .invalid] ++
              casePrefix
          have hHeadCaseLabel :
              Assembly.Program.labelPc
                (pre ++ tableCode base retc idx casePrefix (head :: rest) ++ post)
                (LabelSupply.label base idx) =
                  some (Assembly.Program.byteLength headCasePre) := by
            have hHere :=
              hExact.labelPc_at headCasePre (LabelSupply.label base idx)
                (StackShuffle.removeBuriedUnder retc ++
                  [Assembly.Instr.jump head.returnLabel] ++ casesRest ++ post)
                (by
                  simp [tableCode, headCasePre, headTest, testsRest,
                    casesRest, testCode, caseCode, List.append_assoc])
            simpa [headCasePre] using hHere
          have hFitsHead :
              AssemblyProgram.PCFitsFrom pre
                [ StackShuffle.dupInstr (callee.evm.stack.length + 1)
                , Assembly.Instr.push head.token
                , Assembly.Instr.prim .eq
                , Assembly.Instr.jumpi (LabelSupply.label base idx)
                ] := by
            have hHead :
                AssemblyProgram.PCFitsFrom pre headTest :=
              AssemblyProgram.PCFitsFrom.left
                (pre := pre) (first := headTest)
                (second :=
                  testsRest ++ [Assembly.Instr.prim .invalid] ++ casePrefix ++
                    headCase ++ casesRest)
                (by
                  simpa [tableCode, headTest, headCase, testsRest, casesRest,
                    testCode, caseCode, List.append_assoc] using hFits)
            simpa [headTest, testCode, hRetc] using hHead
          have hRunHead :=
            FrameStateRel.dispatch_mismatched_test_runResult_at_withGasOracle
              (caseLabel := LabelSupply.label base idx)
              (caseDest := Assembly.Program.byteLength headCasePre)
              (pre := pre)
              (post :=
                testsRest ++ [Assembly.Instr.prim .invalid] ++ casePrefix ++
                  headCase ++ casesRest ++ post)
              (callee := callee) (target := target) (tokens := tokens)
              (token := token) (probe := head.token)
              (frame := frame) (returns := returns)
              (oracle := oracle) (cursor := cursor)
              hNe hFitsHead hPc hRel hReturns (by omega)
              (by
                simpa [tableCode, headTest, headCase, testsRest, casesRest,
                  testCode, caseCode, hRetc, headCasePre, List.append_assoc]
                  using hHeadCaseLabel)
          refine
            ARunResultWithGasOracle.bind_running
              (program :=
                pre ++ tableCode base retc idx casePrefix (head :: rest) ++ post)
              (middle := fun afterHead cursorAfterHead =>
                cursorAfterHead = cursor ∧
                  Preservation.Frame.StateRel callee afterHead (token :: tokens) ∧
                  afterHead.pc = Assembly.Program.pcAfter (pre ++ headTest))
              ?_ ?_
          · exact
              ARunResultWithGasOracle.mono
                (by
                  simpa [tableCode, headTest, headCase, testsRest, casesRest,
                    testCode, caseCode, hRetc, List.append_assoc] using hRunHead)
                (by
                  intro result cursorAfterHead hResult
                  cases result with
                  | halted halt =>
                      cases hResult
                  | running afterHead =>
                      rcases hResult with
                        ⟨hCursorAfterHead, hRelAfterHead, hPcAfterHead⟩
                      exact
                        ⟨hCursorAfterHead, hRelAfterHead, by
                          simpa [headTest, testCode, hRetc] using hPcAfterHead⟩)
          · intro afterHead cursorAfterHead hAfterHead
            rcases hAfterHead with
              ⟨hCursorAfterHead, hRelAfterHead, hPcAfterHead⟩
            subst cursorAfterHead
            have hFitsRest :
                AssemblyProgram.PCFitsFrom (pre ++ headTest)
                  (tableCode base retc (idx + 1) (casePrefix ++ headCase) rest) := by
              simpa [tableCode, headTest, headCase, testsRest, casesRest,
                testCode, caseCode, List.append_assoc] using
                (AssemblyProgram.PCFitsFrom.right
                  (pre := pre) (first := headTest)
                  (second :=
                    testsRest ++ [Assembly.Instr.prim .invalid] ++
                      casePrefix ++ headCase ++ casesRest)
                  (by
                    simpa [tableCode, headTest, headCase, testsRest, casesRest,
                      testCode, caseCode, List.append_assoc] using hFits))
            have hExactRest :
                ExactLabels
                  ((pre ++ headTest) ++
                    tableCode base retc (idx + 1) (casePrefix ++ headCase) rest ++
                    post) := by
              simpa [tableCode, headTest, headCase, testsRest, casesRest,
                testCode, caseCode, List.append_assoc] using hExact
            have hReturnRest :
                Assembly.Program.labelPc
                  ((pre ++ headTest) ++
                    tableCode base retc (idx + 1) (casePrefix ++ headCase) rest ++
                    post)
                  site.returnLabel = some returnDest := by
              simpa [tableCode, headTest, headCase, testsRest, casesRest,
                testCode, caseCode, List.append_assoc] using hReturnLabel
            simpa [tableCode, headTest, headCase, testsRest, casesRest,
              testCode, caseCode, List.append_assoc] using
              (ih (pre := pre ++ headTest) (idx := idx + 1)
                (casePrefix := casePrefix ++ headCase)
                hMemRest hNoDupRest hFitsRest
                hPcAfterHead hRelAfterHead hExactRest hReturnRest)

theorem forProc_selected_runResult_at_withGasOracle
    {proc : Proc} {sites : List CallSite} {supply : LabelSupply}
    {site : CallSite} {returnDest : Nat}
    {pre post : Assembly.Program}
    {callee : RunState} {target : EVMState}
    {tokens : List Word} {token : Word} {frame : ReturnDest}
    {returns : List ReturnDest}
    {oracle : GasOracle} {cursor : Nat}
    (hMem : site ∈ (sites.filter (CallSite.forProc proc.name)))
    (hNoDup :
      (((sites.filter (CallSite.forProc proc.name)).map CallSite.token)).Nodup)
    (hToken : site.token = token)
    (hRetc : callee.evm.stack.length = proc.retc)
    (hFits :
      AssemblyProgram.PCFitsFrom pre
        (Dispatch.forProc proc sites supply).code)
    (hPc : target.pc = Assembly.Program.pcAfter pre)
    (hRel : Preservation.Frame.StateRel callee target (token :: tokens))
    (hReturns : callee.returns = frame :: returns)
    (hBound : proc.retc < 16)
    (hExact :
      ExactLabels (pre ++ (Dispatch.forProc proc sites supply).code ++ post))
    (hReturnLabel :
      Assembly.Program.labelPc
        (pre ++ (Dispatch.forProc proc sites supply).code ++ post)
        site.returnLabel = some returnDest) :
    ARunResultWithGasOracle
      (pre ++ (Dispatch.forProc proc sites supply).code ++ post)
      oracle cursor target
      (fun result cursorFinal =>
        match result with
        | .running final =>
            cursorFinal = cursor ∧
              Preservation.Frame.StateRel
                { callee with
                  evm :=
                    { callee.evm with
                      stack := callee.evm.stack ++ frame.callerStack }
                  returns := returns }
                final tokens ∧
              final.pc = EvmYul.UInt256.ofNat returnDest
        | .halted _ => False) := by
  let procSites := sites.filter (CallSite.forProc proc.name)
  have hFitsTable :
      AssemblyProgram.PCFitsFrom pre
        (tableCode supply proc.retc 0 [] procSites) := by
    simpa [Dispatch.forProc, tableCode, procSites, List.append_assoc] using hFits
  have hExactTable :
      ExactLabels (pre ++ tableCode supply proc.retc 0 [] procSites ++ post) := by
    simpa [Dispatch.forProc, tableCode, procSites, List.append_assoc] using hExact
  have hReturnTable :
      Assembly.Program.labelPc
        (pre ++ tableCode supply proc.retc 0 [] procSites ++ post)
        site.returnLabel = some returnDest := by
    simpa [Dispatch.forProc, tableCode, procSites, List.append_assoc] using
      hReturnLabel
  have hRun :=
    selected_table_runResult_at_withGasOracle
      (base := supply) (retc := proc.retc) (idx := 0)
      (casePrefix := []) (post := post) (pre := pre)
      (sites := procSites) (site := site) (returnDest := returnDest)
      (callee := callee) (target := target) (tokens := tokens)
      (token := token) (frame := frame) (returns := returns)
      (oracle := oracle) (cursor := cursor)
      (by simpa [procSites] using hMem) (by simpa [procSites] using hNoDup)
      hToken hRetc hFitsTable hPc hRel hReturns hBound hExactTable hReturnTable
  simpa [Dispatch.forProc, tableCode, procSites, List.append_assoc] using hRun

end DispatchPreservation

namespace ProcedureCall

def bodyCtx (program : Program) (proc : Proc) : CompileContext :=
  { procs := program.procs, leaveLabel? := some (ProcLabel.exit proc.name) }

noncomputable def bodyCode (program : Program) (proc : Proc)
    (supply : LabelSupply) : Assembly.Program :=
  (Block.compileFromCtx proc.body (bodyCtx program proc) supply).code

def dispatchCode (proc : Proc) (sites : List CallSite)
    (supply : LabelSupply) : Assembly.Program :=
  (Dispatch.forProc proc sites supply).code

noncomputable def procSegment (program : Program) (proc : Proc)
    (bodySupply dispatchSupply : LabelSupply) (sites : List CallSite) :
    Assembly.Program :=
  [Assembly.Instr.label (ProcLabel.entry proc.name)] ++
    bodyCode program proc bodySupply ++
    [Assembly.Instr.label (ProcLabel.exit proc.name)] ++
    dispatchCode proc sites dispatchSupply

def ProcBodyPreservesAtSegmentWithGasOracle (program : Program) (proc : Proc)
    (bodySupply dispatchSupply : LabelSupply) (sites : List CallSite)
    (fuel : Nat) (pre post : Assembly.Program) : Prop :=
  ∀ {source : RunState} {outcome : Outcome}
    {target : EVMState} {tokens : List Word}
    {oracle : GasOracle} {cursor cursorFinal : Nat},
    target.pc =
        Assembly.Program.pcAfter
          (pre ++ [Assembly.Instr.label (ProcLabel.entry proc.name)]) →
      Preservation.Frame.StateRel source target tokens →
      Block.EvalWithGasOracle program oracle fuel proc.body cursor source
        outcome cursorFinal →
      ARunResultWithGasOracle
        (pre ++ procSegment program proc bodySupply dispatchSupply sites ++ post)
        oracle cursor target
        (fun result targetCursorFinal =>
          targetCursorFinal = cursorFinal ∧
            CompiledOutcomeRel
              (pre ++
                procSegment program proc bodySupply dispatchSupply sites ++ post)
              (bodyCtx program proc)
              (Assembly.Program.pcAfter
                ((pre ++ [Assembly.Instr.label (ProcLabel.entry proc.name)]) ++
                  bodyCode program proc bodySupply))
              outcome result tokens)

def callJumpCode (proc : Proc) (args : EvmYul.Stack Word)
    (token : Word) : Assembly.Program :=
  ([Assembly.Instr.push token] ++ StackShuffle.sinkTopUnder args.length) ++
    [Assembly.Instr.jump (ProcLabel.entry proc.name)]

def callSiteCode (proc : Proc) (args : EvmYul.Stack Word)
    (token : Word) (returnLabel : Assembly.Label) : Assembly.Program :=
  callJumpCode proc args token ++ [Assembly.Instr.label returnLabel]

def callJumpCodeStatic (proc : Proc) (token : Word) : Assembly.Program :=
  ([Assembly.Instr.push token] ++ StackShuffle.sinkTopUnder proc.argc) ++
    [Assembly.Instr.jump (ProcLabel.entry proc.name)]

def callSiteCodeStatic (proc : Proc) (token : Word)
    (returnLabel : Assembly.Label) : Assembly.Program :=
  callJumpCodeStatic proc token ++ [Assembly.Instr.label returnLabel]

theorem callJumpCode_eq_static {proc : Proc} {args : EvmYul.Stack Word}
    {token : Word}
    (hArgsLen : args.length = proc.argc) :
    callJumpCode proc args token = callJumpCodeStatic proc token := by
  simp [callJumpCode, callJumpCodeStatic, hArgsLen]

theorem callSiteCode_eq_static {proc : Proc} {args : EvmYul.Stack Word}
    {token : Word} {returnLabel : Assembly.Label}
    (hArgsLen : args.length = proc.argc) :
    callSiteCode proc args token returnLabel =
      callSiteCodeStatic proc token returnLabel := by
  simp [callSiteCode, callSiteCodeStatic, callJumpCode_eq_static hArgsLen]

theorem compile_call_code_eq_callSiteCode {ctx : CompileContext}
    {supply : LabelSupply} {name : Name} {proc : Proc}
    {args : EvmYul.Stack Word}
    (hLookup : ProcList.lookup? name ctx.procs = some proc)
    (hArgsLen : args.length = proc.argc) :
    (Stmt.compileFromCtxCore (.call name) ctx supply).code =
      callSiteCode proc args (Stmt.callToken supply)
        (LabelSupply.label supply 0) := by
  have hName := ProcList.name_of_lookup? hLookup
  simp [Stmt.compileFromCtxCore, hLookup, callSiteCode, callJumpCode,
    hArgsLen, hName, List.append_assoc]

theorem compile_call_code_eq_callSiteCodeStatic {ctx : CompileContext}
    {supply : LabelSupply} {name : Name} {proc : Proc}
    (hLookup : ProcList.lookup? name ctx.procs = some proc) :
    (Stmt.compileFromCtxCore (.call name) ctx supply).code =
      callSiteCodeStatic proc (Stmt.callToken supply)
        (LabelSupply.label supply 0) := by
  have hName := ProcList.name_of_lookup? hLookup
  simp [Stmt.compileFromCtxCore, hLookup, callSiteCodeStatic,
    callJumpCodeStatic, hName, List.append_assoc]

theorem callSite_mem_filter_for_lookup {procs : List Proc}
    {name : Name} {proc : Proc} {sites : List CallSite} {site : CallSite}
    (hLookup : ProcList.lookup? name procs = some proc)
    (hMem : site ∈ sites)
    (hSiteName : site.procName = name) :
    site ∈ sites.filter (CallSite.forProc proc.name) := by
  have hProcName := ProcList.name_of_lookup? hLookup
  simp [CallSite.forProc, hMem, hSiteName, hProcName]

theorem arg_bound_of_split {proc : Proc}
    {state : RunState} {args callerStack : EvmYul.Stack Word}
    (hSplit :
      StackFrame.splitArgs? proc.argc state.evm.stack =
        some (args, callerStack))
    (hArgc : proc.argc ≤ 16) :
    args.length ≤ 16 := by
  have hArgsLen :=
    _root_.EvmCompiler.Structured.Preservation.Frame.StackFrameFacts.splitArgs?_args_length
      hSplit
  omega

theorem exit_label_then_dispatch_withGasOracle {proc : Proc}
    {dispatchSupply : LabelSupply} {sites : List CallSite}
    {site : CallSite} {returnDest : Nat}
    {bodyState returned : RunState}
    {stack : EvmYul.Stack Word} {frame : ReturnDest}
    {target : EVMState} {tokens : List Word} {token : Word}
    {preExit post : Assembly.Program}
    {oracle : GasOracle} {cursor : Nat}
    (hAttach :
      StackFrame.attachReturns? frame bodyState.evm.stack = some stack)
    (hReturns : bodyState.returns = frame :: returned.returns)
    (hRetc : bodyState.evm.stack.length = proc.retc)
    (hMem : site ∈ sites.filter (CallSite.forProc proc.name))
    (hNoDup :
      ((sites.filter (CallSite.forProc proc.name)).map CallSite.token).Nodup)
    (hToken : site.token = token)
    (hBound : proc.retc < 16)
    (hFitsExit :
      AssemblyProgram.PCFitsFrom preExit
        [Assembly.Instr.label (ProcLabel.exit proc.name)])
    (hFitsDispatch :
      AssemblyProgram.PCFitsFrom
        (preExit ++ [Assembly.Instr.label (ProcLabel.exit proc.name)])
        (dispatchCode proc sites dispatchSupply))
    (hPc : target.pc = Assembly.Program.pcAfter preExit)
    (hRel : Preservation.Frame.StateRel bodyState target (token :: tokens))
    (hExact :
      ExactLabels
        (preExit ++ [Assembly.Instr.label (ProcLabel.exit proc.name)] ++
          dispatchCode proc sites dispatchSupply ++ post))
    (hReturnLabel :
      Assembly.Program.labelPc
        (preExit ++ [Assembly.Instr.label (ProcLabel.exit proc.name)] ++
          dispatchCode proc sites dispatchSupply ++ post)
        site.returnLabel = some returnDest) :
    ARunResultWithGasOracle
      (preExit ++ [Assembly.Instr.label (ProcLabel.exit proc.name)] ++
        dispatchCode proc sites dispatchSupply ++ post)
      oracle cursor target
      (fun result cursorFinal =>
        match result with
        | .running final =>
            cursorFinal = cursor ∧
              Preservation.Frame.StateRel
                (returned.withEVM { bodyState.evm with stack := stack })
                final tokens ∧
              final.pc = EvmYul.UInt256.ofNat returnDest
        | .halted _ => False) := by
  let dcode := dispatchCode proc sites dispatchSupply
  have hSourceEq :
      returned.withEVM { bodyState.evm with stack := stack } =
        { bodyState with
          evm :=
            { bodyState.evm with
              stack := bodyState.evm.stack ++ frame.callerStack }
          returns := returned.returns } :=
    _root_.EvmCompiler.Structured.Preservation.Frame.CallFacts.returned_with_attached_eq
      hAttach
  have hExitRun :=
    FrameStateRel.label_runResult_at_withGasOracle
      (label := ProcLabel.exit proc.name)
      (pre := preExit) (post := dcode ++ post)
      (source := bodyState) (target := target)
      (tokens := token :: tokens) (oracle := oracle) (cursor := cursor)
      (AssemblyProgram.PCFitsFrom.start hFitsExit) hPc hRel
  refine
    ARunResultWithGasOracle.bind_running
      (program :=
        preExit ++ [Assembly.Instr.label (ProcLabel.exit proc.name)] ++
          dispatchCode proc sites dispatchSupply ++ post)
      (middle := fun afterExit cursorAfterExit =>
        cursorAfterExit = cursor ∧
          Preservation.Frame.StateRel bodyState afterExit (token :: tokens) ∧
          afterExit.pc =
            Assembly.Program.pcAfter
              (preExit ++ [Assembly.Instr.label (ProcLabel.exit proc.name)]))
      ?_ ?_
  · simpa [dcode, dispatchCode, List.append_assoc] using hExitRun
  · intro afterExit cursorAfterExit hAfterExit
    rcases hAfterExit with
      ⟨hCursorAfterExit, hRelAfterExit, hPcAfterExit⟩
    subst cursorAfterExit
    have hDispatch :=
      DispatchPreservation.forProc_selected_runResult_at_withGasOracle
        (proc := proc) (sites := sites) (supply := dispatchSupply)
        (site := site) (returnDest := returnDest)
        (pre := preExit ++ [Assembly.Instr.label (ProcLabel.exit proc.name)])
        (post := post) (callee := bodyState) (target := afterExit)
        (tokens := tokens) (token := token) (frame := frame)
        (returns := returned.returns)
        (oracle := oracle) (cursor := cursor)
        hMem hNoDup hToken hRetc
        (by simpa [dispatchCode, dcode] using hFitsDispatch)
        hPcAfterExit hRelAfterExit hReturns hBound
        (by simpa [dispatchCode, dcode, List.append_assoc] using hExact)
        (by simpa [dispatchCode, dcode, List.append_assoc] using hReturnLabel)
    exact
      ARunResultWithGasOracle.mono
        (by
          simpa [dispatchCode, dcode, List.append_assoc] using hDispatch)
        (by
          intro result cursorFinal hResult
          cases result with
          | halted halt =>
              cases hResult
          | running final =>
              rcases hResult with
                ⟨hCursorFinal, hRelFinal, hPcFinal⟩
              exact
                ⟨hCursorFinal, by simpa [hSourceEq] using hRelFinal, hPcFinal⟩)

end ProcedureCall

namespace Terminal

def RelSafeWithGasOracle (kind : Assembly.HaltKind) : Prop :=
  ∀ {oracle : GasOracle} {cursor cursor' : Nat}
      {source : RunState} {sourceFinal target : EVMState}
      {tokens : List Word},
    Frame.StateRel source target tokens →
      Terminal.stepWithGasOracle kind oracle cursor source.evm =
        .ok (sourceFinal, cursor') →
        ∃ targetFinal,
          Terminal.stepWithGasOracle kind oracle cursor target =
            .ok (targetFinal, cursor') ∧
            Frame.StateRel (source.withEVM sourceFinal) targetFinal tokens

theorem stepWithGasOracle_eq_plain (kind : Assembly.HaltKind)
    (oracle : GasOracle) (cursor : Nat) (state : EVMState) :
    Terminal.stepWithGasOracle kind oracle cursor state =
      (do
        let state' ← Terminal.step kind state
        pure (state', cursor)) := by
  cases kind <;> rfl

theorem relSafeWithGasOracle_of_relSafe {kind : Assembly.HaltKind}
    (hSafe : Preservation.Terminal.RelSafe kind) :
    RelSafeWithGasOracle kind := by
  intro oracle cursor cursor' source sourceFinal target tokens hRel hStep
  rw [stepWithGasOracle_eq_plain] at hStep
  cases hPlainStep : Terminal.step kind source.evm with
  | error err =>
      rw [hPlainStep] at hStep
      cases hStep
  | ok plainFinal =>
      rw [hPlainStep] at hStep
      cases hStep
      rcases hSafe hRel hPlainStep with
        ⟨targetFinal, hTargetStep, hTargetRel⟩
      refine ⟨targetFinal, ?_, hTargetRel⟩
      rw [stepWithGasOracle_eq_plain, hTargetStep]
      rfl

end Terminal

namespace FrameStateRel

theorem terminal_stepResult_at_withGasOracle {kind : Assembly.HaltKind}
    {pre post : Assembly.Program} {source : RunState}
    {sourceFinal target : EVMState} {tokens : List Word}
    {oracle : GasOracle} {cursor cursor' : Nat}
    (hSafe : Terminal.RelSafeWithGasOracle kind)
    (hFit : PCFits pre)
    (hPc : target.pc = Assembly.Program.pcAfter pre)
    (hRel : Preservation.Frame.StateRel source target tokens)
    (hStep : Terminal.stepWithGasOracle kind oracle cursor source.evm =
      .ok (sourceFinal, cursor')) :
    ∃ targetFinal,
      Assembly.GasParametric.sourceStepResultWithGasOracle
          (pre ++ [Assembly.Instr.prim kind.toPrimOp] ++ post)
          oracle cursor target =
        .ok (.halted
          { kind := kind
            state := targetFinal
            output := kind.output targetFinal },
          cursor') ∧
        Preservation.Frame.StateRel
          (source.withEVM sourceFinal) targetFinal tokens := by
  rcases hSafe hRel hStep with ⟨targetFinal, hTargetStep, hTargetRel⟩
  refine ⟨targetFinal, ?_, hTargetRel⟩
  unfold Assembly.GasParametric.sourceStepResultWithGasOracle
  have hAt :
      Assembly.Program.instrAtPc
          (pre ++ [Assembly.Instr.prim kind.toPrimOp] ++ post)
          target.pc.toNat =
        some (Assembly.Program.byteLength pre,
          Assembly.Instr.prim kind.toPrimOp) := by
    unfold Assembly.Program.instrAtPc
    rw [hPc, hFit]
    simpa using
      Assembly.Program.instrAtPcFrom_append_boundary_cons
        pre post (Assembly.Instr.prim kind.toPrimOp) 0
  rw [hAt]
  unfold Assembly.GasParametric.sourceStepAtWithGasOracle
  change
    (do
      let (state', cursorAfterStep) ←
        Terminal.stepWithGasOracle kind oracle cursor target
      match (kind.toPrimOp).haltKind? with
      | some haltKind =>
          Except.ok
            (Assembly.StepResult.halted
              { kind := haltKind
                state := state'
                output := haltKind.output state' },
              cursorAfterStep)
      | none =>
          Except.ok (Assembly.StepResult.running state', cursorAfterStep)) =
      Except.ok
        (Assembly.StepResult.halted
          { kind := kind
            state := targetFinal
            output := kind.output targetFinal },
          cursor')
  rw [hTargetStep]
  simp [Assembly.HaltKind.toPrimOp_haltKind?, Bind.bind, Except.bind]

end FrameStateRel

def StmtPreservesWithGasOracle (program : Program) (ctx : CompileContext)
    (supply : LabelSupply) (stmt : Stmt) : Prop :=
  ∀ {pre post : Assembly.Program} {fuel : Nat}
    {source : RunState} {outcome : Outcome} {target : EVMState}
    {tokens : List Word} {oracle : GasOracle} {cursor cursorFinal : Nat},
    AssemblyProgram.PCFitsFrom pre
        (Stmt.compileFromCtxCore stmt ctx supply).code →
      ContextLabelsResolve
        (pre ++ (Stmt.compileFromCtxCore stmt ctx supply).code ++ post) ctx →
      ExactLabels
        (pre ++ (Stmt.compileFromCtxCore stmt ctx supply).code ++ post) →
      target.pc = Assembly.Program.pcAfter pre →
      Frame.StateRel source target tokens →
      Stmt.EvalWithGasOracle program oracle fuel stmt cursor source outcome
        cursorFinal →
      ARunResultWithGasOracle
        (pre ++ (Stmt.compileFromCtxCore stmt ctx supply).code ++ post)
        oracle cursor target
        (fun result targetCursorFinal =>
          targetCursorFinal = cursorFinal ∧
            CompiledOutcomeRel
              (pre ++ (Stmt.compileFromCtxCore stmt ctx supply).code ++ post)
              ctx
              (Assembly.Program.pcAfter
                (pre ++ (Stmt.compileFromCtxCore stmt ctx supply).code))
              outcome result tokens)

def BlockPreservesWithGasOracle (program : Program) (ctx : CompileContext)
    (supply : LabelSupply) (block : Block) : Prop :=
  ∀ {pre post : Assembly.Program} {fuel : Nat}
    {source : RunState} {outcome : Outcome} {target : EVMState}
    {tokens : List Word} {oracle : GasOracle} {cursor cursorFinal : Nat},
    AssemblyProgram.PCFitsFrom pre
        (Block.compileFromCtx block ctx supply).code →
      ContextLabelsResolve
        (pre ++ (Block.compileFromCtx block ctx supply).code ++ post) ctx →
      ExactLabels
        (pre ++ (Block.compileFromCtx block ctx supply).code ++ post) →
      target.pc = Assembly.Program.pcAfter pre →
      Frame.StateRel source target tokens →
      Block.EvalWithGasOracle program oracle fuel block cursor source outcome
        cursorFinal →
      ARunResultWithGasOracle
        (pre ++ (Block.compileFromCtx block ctx supply).code ++ post)
        oracle cursor target
        (fun result targetCursorFinal =>
          targetCursorFinal = cursorFinal ∧
            CompiledOutcomeRel
              (pre ++ (Block.compileFromCtx block ctx supply).code ++ post)
              ctx
              (Assembly.Program.pcAfter
                (pre ++ (Block.compileFromCtx block ctx supply).code))
              outcome result tokens)

def BlockPreservesWithGasOracleAtFuel (program : Program)
    (ctx : CompileContext) (supply : LabelSupply) (block : Block)
    (fuel : Nat) : Prop :=
  ∀ {pre post : Assembly.Program}
    {source : RunState} {outcome : Outcome} {target : EVMState}
    {tokens : List Word} {oracle : GasOracle} {cursor cursorFinal : Nat},
    AssemblyProgram.PCFitsFrom pre
        (Block.compileFromCtx block ctx supply).code →
      ContextLabelsResolve
        (pre ++ (Block.compileFromCtx block ctx supply).code ++ post) ctx →
      ExactLabels
        (pre ++ (Block.compileFromCtx block ctx supply).code ++ post) →
      target.pc = Assembly.Program.pcAfter pre →
      Frame.StateRel source target tokens →
      Block.EvalWithGasOracle program oracle fuel block cursor source outcome
        cursorFinal →
      ARunResultWithGasOracle
        (pre ++ (Block.compileFromCtx block ctx supply).code ++ post)
        oracle cursor target
        (fun result targetCursorFinal =>
          targetCursorFinal = cursorFinal ∧
            CompiledOutcomeRel
              (pre ++ (Block.compileFromCtx block ctx supply).code ++ post)
              ctx
              (Assembly.Program.pcAfter
                (pre ++ (Block.compileFromCtx block ctx supply).code))
              outcome result tokens)

theorem blockPreservesWithGasOracleAtFuel_of_preserves {program : Program}
    {ctx : CompileContext} {supply : LabelSupply} {block : Block}
    {fuel : Nat}
    (hPreserves :
      BlockPreservesWithGasOracle program ctx supply block) :
    BlockPreservesWithGasOracleAtFuel program ctx supply block fuel := by
  intro pre post source outcome target tokens oracle cursor cursorFinal hFits
    hResolve hExact hPc hRel hEval
  exact hPreserves hFits hResolve hExact hPc hRel hEval

namespace ProcedureCall

theorem procBodyPreservesAtSegment_of_local_withGasOracle {program : Program}
    {proc : Proc}
    {bodySupply dispatchSupply : LabelSupply} {sites : List CallSite}
    {fuel : Nat} {pre post : Assembly.Program}
    (hBodyPres :
      BlockPreservesWithGasOracleAtFuel program (bodyCtx program proc)
        bodySupply proc.body fuel)
    (hFits :
      AssemblyProgram.PCFitsFrom pre
        (procSegment program proc bodySupply dispatchSupply sites))
    (hExact :
      ExactLabels
        (pre ++ procSegment program proc bodySupply dispatchSupply sites ++
          post)) :
    ProcBodyPreservesAtSegmentWithGasOracle program proc bodySupply
      dispatchSupply sites fuel pre post := by
  intro source outcome target tokens oracle cursor cursorFinal
    hPc hRel hEval
  let ctx := bodyCtx program proc
  let bcode := bodyCode program proc bodySupply
  let dcode := dispatchCode proc sites dispatchSupply
  let exitLabel := ProcLabel.exit proc.name
  have hFitsAfterEntry :
      AssemblyProgram.PCFitsFrom
        (pre ++ [Assembly.Instr.label (ProcLabel.entry proc.name)])
        (bcode ++ ([Assembly.Instr.label exitLabel] ++ dcode)) := by
    exact
      AssemblyProgram.PCFitsFrom.right
        (pre := pre)
        (first := [Assembly.Instr.label (ProcLabel.entry proc.name)])
        (second := bcode ++ ([Assembly.Instr.label exitLabel] ++ dcode))
        (by
          simpa [procSegment, bcode, dcode, bodyCode, dispatchCode, exitLabel,
            List.append_assoc] using hFits)
  have hFitsBody :
      AssemblyProgram.PCFitsFrom
        (pre ++ [Assembly.Instr.label (ProcLabel.entry proc.name)])
        bcode := by
    exact
      AssemblyProgram.PCFitsFrom.left
        (pre := pre ++ [Assembly.Instr.label (ProcLabel.entry proc.name)])
        (first := bcode)
        (second := [Assembly.Instr.label exitLabel] ++ dcode)
        hFitsAfterEntry
  have hExitPc :
      Assembly.Program.labelPc
        (pre ++ procSegment program proc bodySupply dispatchSupply sites ++ post)
        exitLabel =
          some
            (Assembly.Program.byteLength
              ((pre ++ [Assembly.Instr.label (ProcLabel.entry proc.name)]) ++
                bcode)) := by
    have hHere :=
      hExact.labelPc_at
        ((pre ++ [Assembly.Instr.label (ProcLabel.entry proc.name)]) ++ bcode)
        exitLabel
        (dcode ++ post)
        (by
          simp [procSegment, bcode, dcode, bodyCode, dispatchCode, exitLabel,
            List.append_assoc])
    simpa [bcode, dcode, exitLabel] using hHere
  have hResolveBody :
      ContextLabelsResolve
        ((pre ++ [Assembly.Instr.label (ProcLabel.entry proc.name)]) ++
          bcode ++ ([Assembly.Instr.label exitLabel] ++ dcode ++ post))
        ctx := by
    refine ⟨?_, ?_, ?_⟩
    · intro label h
      simp [ctx, bodyCtx] at h
    · intro label h
      simp [ctx, bodyCtx] at h
    · intro label h
      simp [ctx, bodyCtx] at h
      cases h
      refine ⟨Assembly.Program.byteLength
        ((pre ++ [Assembly.Instr.label (ProcLabel.entry proc.name)]) ++
          bcode), ?_⟩
      simpa [procSegment, bcode, dcode, bodyCode, dispatchCode, exitLabel,
        List.append_assoc] using hExitPc
  have hExactBody :
      ExactLabels
        ((pre ++ [Assembly.Instr.label (ProcLabel.entry proc.name)]) ++
          bcode ++ ([Assembly.Instr.label exitLabel] ++ dcode ++ post)) := by
    simpa [procSegment, bcode, dcode, bodyCode, dispatchCode, exitLabel,
      List.append_assoc] using hExact
  have hRun :=
    hBodyPres
      (pre := pre ++ [Assembly.Instr.label (ProcLabel.entry proc.name)])
      (post := [Assembly.Instr.label exitLabel] ++ dcode ++ post)
      (source := source) (outcome := outcome) (target := target)
      (tokens := tokens) (oracle := oracle) (cursor := cursor)
      (cursorFinal := cursorFinal)
      (by simpa [bodyCode, ctx, bcode] using hFitsBody)
      hResolveBody hExactBody hPc hRel hEval
  simpa [ProcBodyPreservesAtSegmentWithGasOracle, procSegment, bodyCode,
    dispatchCode, ctx, bcode, dcode, exitLabel, List.append_assoc] using hRun

end ProcedureCall

namespace ProofOutcome

def ReturnsPreserved (initial : RunState) (outcome : Outcome) : Prop :=
  match outcome.mode with
  | .halt _ => True
  | _ => outcome.state.returns = initial.returns

def ModeAllowed (canBreak canContinue canLeave : Bool)
    (outcome : Outcome) : Prop :=
  match outcome.mode with
  | .regular | .halt _ => True
  | .brk => canBreak = true
  | .cont => canContinue = true
  | .leave => canLeave = true

theorem whole_of_modeAllowed_false {outcome : Outcome}
    (hAllowed : ModeAllowed false false false outcome) :
    WholeProgramSourceOutcome outcome := by
  cases outcome with
  | mk state mode =>
      cases mode <;> simp [ModeAllowed, WholeProgramSourceOutcome] at hAllowed ⊢

end ProofOutcome

theorem code_runStateWithGasOracle_returns_eq {code : Code}
    {oracle : GasOracle} {cursor cursor' : Nat}
    {state final : RunState}
    (hRun :
      EvmCompiler.Structured.Code.runStateWithGasOracle code oracle cursor
          state =
        .ok (final, cursor')) :
    final.returns = state.returns := by
  unfold EvmCompiler.Structured.Code.runStateWithGasOracle at hRun
  cases hCode :
      EvmCompiler.Structured.Code.runWithGasOracle code oracle cursor
        state.evm with
  | error err =>
      simp [hCode, Bind.bind, Except.bind] at hRun
  | ok result =>
      rcases result with ⟨evm, cursor''⟩
      simp [hCode] at hRun
      cases hRun
      rfl

theorem code_runConditionStateWithGasOracle_returns_eq {code : Code}
    {oracle : GasOracle} {cursor cursor' : Nat}
    {state final : RunState} {cond : Bool}
    (hRun :
      EvmCompiler.Structured.Code.runConditionStateWithGasOracle code oracle
          cursor state =
        .ok (final, cond, cursor')) :
    final.returns = state.returns := by
  unfold EvmCompiler.Structured.Code.runConditionStateWithGasOracle at hRun
  cases hCond :
      EvmCompiler.Structured.Code.runConditionWithGasOracle code oracle cursor
        state.evm with
  | error err =>
      simp [hCond, Bind.bind, Except.bind] at hRun
  | ok result =>
      rcases result with ⟨evm, cond', cursor''⟩
      simp [hCond] at hRun
      cases hRun
      rfl

mutual
  theorem Block.EvalWithGasOracle.returns_preserved {program : Program}
      {oracle : GasOracle} {fuel cursor cursorFinal : Nat}
      {block : Block} {state : RunState} {outcome : Outcome}
      (hEval :
        Block.EvalWithGasOracle program oracle fuel block cursor state outcome
          cursorFinal) :
      ProofOutcome.ReturnsPreserved state outcome := by
    cases hEval with
    | nil =>
        simp [ProofOutcome.ReturnsPreserved, Outcome.regular]
    | cons_regular hStmt hRest =>
        have hStmtReturns := Stmt.EvalWithGasOracle.returns_preserved hStmt
        have hRestReturns := Block.EvalWithGasOracle.returns_preserved hRest
        cases outcome with
        | mk outState outMode =>
            cases outMode <;>
              simp [ProofOutcome.ReturnsPreserved, Outcome.regular]
                at hStmtReturns hRestReturns ⊢
            · exact hRestReturns.trans hStmtReturns
            · exact hRestReturns.trans hStmtReturns
            · exact hRestReturns.trans hStmtReturns
            · exact hRestReturns.trans hStmtReturns
    | cons_brk hStmt =>
        simpa [ProofOutcome.ReturnsPreserved, Outcome.brk] using
          Stmt.EvalWithGasOracle.returns_preserved hStmt
    | cons_cont hStmt =>
        simpa [ProofOutcome.ReturnsPreserved, Outcome.cont] using
          Stmt.EvalWithGasOracle.returns_preserved hStmt
    | cons_leave hStmt =>
        simpa [ProofOutcome.ReturnsPreserved, Outcome.leave] using
          Stmt.EvalWithGasOracle.returns_preserved hStmt
    | cons_halt hStmt =>
        simp [ProofOutcome.ReturnsPreserved, Outcome.halt]

  theorem Stmt.EvalWithGasOracle.returns_preserved {program : Program}
      {oracle : GasOracle} {fuel cursor cursorFinal : Nat}
      {stmt : Stmt} {state : RunState} {outcome : Outcome}
      (hEval :
        Stmt.EvalWithGasOracle program oracle fuel stmt cursor state outcome
          cursorFinal) :
      ProofOutcome.ReturnsPreserved state outcome := by
    cases hEval with
    | code hCode =>
        simpa [ProofOutcome.ReturnsPreserved, Outcome.regular] using
          code_runStateWithGasOracle_returns_eq hCode
    | if_false hCond =>
        simpa [ProofOutcome.ReturnsPreserved, Outcome.regular] using
          code_runConditionStateWithGasOracle_returns_eq hCond
    | if_true hCond hBody =>
        have hCondReturns :=
          code_runConditionStateWithGasOracle_returns_eq hCond
        have hBodyReturns := Block.EvalWithGasOracle.returns_preserved hBody
        cases outcome with
        | mk outState outMode =>
            cases outMode <;>
              simp [ProofOutcome.ReturnsPreserved] at hBodyReturns ⊢
            · exact hBodyReturns.trans hCondReturns
            · exact hBodyReturns.trans hCondReturns
            · exact hBodyReturns.trans hCondReturns
            · exact hBodyReturns.trans hCondReturns
    | switch_none hScrutinee hPop hSelect =>
        simpa [ProofOutcome.ReturnsPreserved, Outcome.regular, RunState.withEVM]
          using code_runStateWithGasOracle_returns_eq hScrutinee
    | switch_some hScrutinee hPop hStateAfterPop hSelect hBody =>
        have hScrutineeReturns :=
          code_runStateWithGasOracle_returns_eq hScrutinee
        have hBodyReturns := Block.EvalWithGasOracle.returns_preserved hBody
        subst hStateAfterPop
        cases outcome with
        | mk outState outMode =>
            cases outMode <;>
              simp [ProofOutcome.ReturnsPreserved, RunState.withEVM]
                at hBodyReturns ⊢
            · exact hBodyReturns.trans hScrutineeReturns
            · exact hBodyReturns.trans hScrutineeReturns
            · exact hBodyReturns.trans hScrutineeReturns
            · exact hBodyReturns.trans hScrutineeReturns
    | for_init_regular hInit hLoop =>
        have hInitReturns := Block.EvalWithGasOracle.returns_preserved hInit
        have hLoopReturns := For.EvalWithGasOracle.returns_preserved hLoop
        cases outcome with
        | mk outState outMode =>
            cases outMode <;>
              simp [ProofOutcome.ReturnsPreserved, Outcome.regular]
                at hInitReturns hLoopReturns ⊢
            · exact hLoopReturns.trans hInitReturns
            · exact hLoopReturns.trans hInitReturns
            · exact hLoopReturns.trans hInitReturns
            · exact hLoopReturns.trans hInitReturns
    | for_init_leave hInit =>
        simpa [ProofOutcome.ReturnsPreserved, Outcome.leave] using
          Block.EvalWithGasOracle.returns_preserved hInit
    | for_init_halt hInit =>
        simp [ProofOutcome.ReturnsPreserved, Outcome.halt]
    | brk =>
        simp [ProofOutcome.ReturnsPreserved, Outcome.brk]
    | cont =>
        simp [ProofOutcome.ReturnsPreserved, Outcome.cont]
    | leave hReturns =>
        simp [ProofOutcome.ReturnsPreserved, Outcome.leave]
    | call_regular hLookup hSplit hBody hPop hAttach =>
        rename_i proc args callerStack stack bodyState returned frame
        have hBodyReturns := Block.EvalWithGasOracle.returns_preserved hBody
        have hPopReturns := Frame.RunState.popReturn?_returns_eq hPop
        have hReturnedReturns : returned.returns = state.returns := by
          simp [ProofOutcome.ReturnsPreserved, Outcome.regular,
            RunState.withEVM, RunState.pushReturn] at hBodyReturns
          rw [hPopReturns] at hBodyReturns
          exact (List.cons.inj hBodyReturns).2
        simpa [ProofOutcome.ReturnsPreserved, Outcome.regular, RunState.withEVM]
          using hReturnedReturns
    | call_leave hLookup hSplit hBody hPop hAttach =>
        rename_i proc args callerStack stack bodyState returned frame
        have hBodyReturns := Block.EvalWithGasOracle.returns_preserved hBody
        have hPopReturns := Frame.RunState.popReturn?_returns_eq hPop
        have hReturnedReturns : returned.returns = state.returns := by
          simp [ProofOutcome.ReturnsPreserved, Outcome.leave,
            RunState.withEVM, RunState.pushReturn] at hBodyReturns
          rw [hPopReturns] at hBodyReturns
          exact (List.cons.inj hBodyReturns).2
        simpa [ProofOutcome.ReturnsPreserved, Outcome.regular, RunState.withEVM]
          using hReturnedReturns
    | call_halt hLookup hSplit hBody =>
        simp [ProofOutcome.ReturnsPreserved, Outcome.halt]
    | terminal hStep =>
        simp [ProofOutcome.ReturnsPreserved, Outcome.halt]

  theorem For.EvalWithGasOracle.returns_preserved {program : Program}
      {oracle : GasOracle} {fuel cursor cursorFinal : Nat}
      {cond : Code} {post body : Block} {state : RunState}
      {outcome : Outcome}
      (hEval :
        For.EvalWithGasOracle program oracle fuel cond post body cursor state
          outcome cursorFinal) :
      ProofOutcome.ReturnsPreserved state outcome := by
    cases hEval with
    | false hCond =>
        simpa [ProofOutcome.ReturnsPreserved, Outcome.regular] using
          code_runConditionStateWithGasOracle_returns_eq hCond
    | body_brk hCond hBody =>
        have hCondReturns :=
          code_runConditionStateWithGasOracle_returns_eq hCond
        have hBodyReturns := Block.EvalWithGasOracle.returns_preserved hBody
        simp [ProofOutcome.ReturnsPreserved, Outcome.regular, Outcome.brk]
          at hBodyReturns ⊢
        exact hBodyReturns.trans hCondReturns
    | body_leave hCond hBody =>
        have hCondReturns :=
          code_runConditionStateWithGasOracle_returns_eq hCond
        have hBodyReturns := Block.EvalWithGasOracle.returns_preserved hBody
        simp [ProofOutcome.ReturnsPreserved, Outcome.leave] at hBodyReturns ⊢
        exact hBodyReturns.trans hCondReturns
    | body_halt hCond hBody =>
        simp [ProofOutcome.ReturnsPreserved, Outcome.halt]
    | regular_post_regular hCond hBody hPost hLoop =>
        have hCondReturns :=
          code_runConditionStateWithGasOracle_returns_eq hCond
        have hBodyReturns := Block.EvalWithGasOracle.returns_preserved hBody
        have hPostReturns := Block.EvalWithGasOracle.returns_preserved hPost
        have hLoopReturns := For.EvalWithGasOracle.returns_preserved hLoop
        cases outcome with
        | mk outState outMode =>
            cases outMode <;>
              simp [ProofOutcome.ReturnsPreserved, Outcome.regular]
                at hBodyReturns hPostReturns hLoopReturns ⊢
            · exact hLoopReturns.trans
                (hPostReturns.trans (hBodyReturns.trans hCondReturns))
            · exact hLoopReturns.trans
                (hPostReturns.trans (hBodyReturns.trans hCondReturns))
            · exact hLoopReturns.trans
                (hPostReturns.trans (hBodyReturns.trans hCondReturns))
            · exact hLoopReturns.trans
                (hPostReturns.trans (hBodyReturns.trans hCondReturns))
    | cont_post_regular hCond hBody hPost hLoop =>
        have hCondReturns :=
          code_runConditionStateWithGasOracle_returns_eq hCond
        have hBodyReturns := Block.EvalWithGasOracle.returns_preserved hBody
        have hPostReturns := Block.EvalWithGasOracle.returns_preserved hPost
        have hLoopReturns := For.EvalWithGasOracle.returns_preserved hLoop
        cases outcome with
        | mk outState outMode =>
            cases outMode <;>
              simp [ProofOutcome.ReturnsPreserved, Outcome.cont, Outcome.regular]
                at hBodyReturns hPostReturns hLoopReturns ⊢
            · exact hLoopReturns.trans
                (hPostReturns.trans (hBodyReturns.trans hCondReturns))
            · exact hLoopReturns.trans
                (hPostReturns.trans (hBodyReturns.trans hCondReturns))
            · exact hLoopReturns.trans
                (hPostReturns.trans (hBodyReturns.trans hCondReturns))
            · exact hLoopReturns.trans
                (hPostReturns.trans (hBodyReturns.trans hCondReturns))
    | regular_post_leave hCond hBody hPost =>
        have hCondReturns :=
          code_runConditionStateWithGasOracle_returns_eq hCond
        have hBodyReturns := Block.EvalWithGasOracle.returns_preserved hBody
        have hPostReturns := Block.EvalWithGasOracle.returns_preserved hPost
        simp [ProofOutcome.ReturnsPreserved, Outcome.regular, Outcome.leave]
          at hBodyReturns hPostReturns ⊢
        exact hPostReturns.trans (hBodyReturns.trans hCondReturns)
    | cont_post_leave hCond hBody hPost =>
        have hCondReturns :=
          code_runConditionStateWithGasOracle_returns_eq hCond
        have hBodyReturns := Block.EvalWithGasOracle.returns_preserved hBody
        have hPostReturns := Block.EvalWithGasOracle.returns_preserved hPost
        simp [ProofOutcome.ReturnsPreserved, Outcome.cont, Outcome.leave]
          at hBodyReturns hPostReturns ⊢
        exact hPostReturns.trans (hBodyReturns.trans hCondReturns)
    | regular_post_halt hCond hBody hPost =>
        simp [ProofOutcome.ReturnsPreserved, Outcome.halt]
    | cont_post_halt hCond hBody hPost =>
        simp [ProofOutcome.ReturnsPreserved, Outcome.halt]
end

namespace ProcedureCall

theorem regular_body_pop_frame_withGasOracle {program : Program}
    {oracle : GasOracle} {fuel cursor cursorFinal : Nat}
    {proc : Proc} {state bodyState returned : RunState}
    {args callerStack stack : EvmYul.Stack Word} {frame : ReturnDest}
    (hBody :
      Block.EvalWithGasOracle program oracle fuel proc.body cursor
        ((state.withEVM { state.evm with stack := args }).pushReturn
          callerStack proc.retc)
        (Outcome.regular bodyState) cursorFinal)
    (hPop : bodyState.popReturn? = some (frame, returned))
    (hAttach : StackFrame.attachReturns? frame bodyState.evm.stack = some stack) :
    frame = { callerStack := callerStack, retc := proc.retc } ∧
      returned.returns = state.returns ∧
      bodyState.evm.stack.length = proc.retc := by
  have hPreserved := Block.EvalWithGasOracle.returns_preserved hBody
  simp [ProofOutcome.ReturnsPreserved, Outcome.regular, RunState.withEVM,
    RunState.pushReturn] at hPreserved
  rcases
    _root_.EvmCompiler.Structured.Preservation.Frame.CallFacts.popReturn?_eq_pushed_frame
        (caller := state) (callerStack := callerStack)
        (retc := proc.retc) hPreserved hPop with
    ⟨hFrame, hReturned⟩
  have hLength :=
    _root_.EvmCompiler.Structured.Preservation.Frame.StackFrameFacts.attachReturns?_length
      hAttach
  subst hFrame
  exact ⟨rfl, hReturned, hLength⟩

theorem leave_body_pop_frame_withGasOracle {program : Program}
    {oracle : GasOracle} {fuel cursor cursorFinal : Nat}
    {proc : Proc} {state bodyState returned : RunState}
    {args callerStack stack : EvmYul.Stack Word} {frame : ReturnDest}
    (hBody :
      Block.EvalWithGasOracle program oracle fuel proc.body cursor
        ((state.withEVM { state.evm with stack := args }).pushReturn
          callerStack proc.retc)
        (Outcome.leave bodyState) cursorFinal)
    (hPop : bodyState.popReturn? = some (frame, returned))
    (hAttach : StackFrame.attachReturns? frame bodyState.evm.stack = some stack) :
    frame = { callerStack := callerStack, retc := proc.retc } ∧
      returned.returns = state.returns ∧
      bodyState.evm.stack.length = proc.retc := by
  have hPreserved := Block.EvalWithGasOracle.returns_preserved hBody
  simp [ProofOutcome.ReturnsPreserved, Outcome.leave, RunState.withEVM,
    RunState.pushReturn] at hPreserved
  rcases
    _root_.EvmCompiler.Structured.Preservation.Frame.CallFacts.popReturn?_eq_pushed_frame
        (caller := state) (callerStack := callerStack)
        (retc := proc.retc) hPreserved hPop with
    ⟨hFrame, hReturned⟩
  have hLength :=
    _root_.EvmCompiler.Structured.Preservation.Frame.StackFrameFacts.attachReturns?_length
      hAttach
  subst hFrame
  exact ⟨rfl, hReturned, hLength⟩

theorem regular_body_then_dispatch_withGasOracle {program : Program}
    {proc : Proc}
    {bodySupply dispatchSupply : LabelSupply} {sites : List CallSite}
    {site : CallSite} {returnDest fuel : Nat}
    {state bodyState returned : RunState}
    {args callerStack stack : EvmYul.Stack Word} {frame : ReturnDest}
    {target : EVMState} {tokens : List Word} {token : Word}
    {pre post : Assembly.Program}
    {oracle : GasOracle} {cursor cursorAfterBody : Nat}
    (hBodyPres :
      ProcBodyPreservesAtSegmentWithGasOracle program proc bodySupply
        dispatchSupply sites fuel pre post)
    (hBody :
      Block.EvalWithGasOracle program oracle fuel proc.body cursor
        ((state.withEVM { state.evm with stack := args }).pushReturn
          callerStack proc.retc)
        (Outcome.regular bodyState) cursorAfterBody)
    (hPop : bodyState.popReturn? = some (frame, returned))
    (hAttach :
      StackFrame.attachReturns? frame bodyState.evm.stack = some stack)
    (hMem : site ∈ sites.filter (CallSite.forProc proc.name))
    (hNoDup :
      ((sites.filter (CallSite.forProc proc.name)).map CallSite.token).Nodup)
    (hToken : site.token = token)
    (hBound : proc.retc < 16)
    (hFits :
      AssemblyProgram.PCFitsFrom pre
        (procSegment program proc bodySupply dispatchSupply sites))
    (hPc : target.pc = Assembly.Program.pcAfter pre)
    (hRel :
      Preservation.Frame.StateRel
        ((state.withEVM { state.evm with stack := args }).pushReturn
          callerStack proc.retc)
        target (token :: tokens))
    (hExact :
      ExactLabels
        (pre ++ procSegment program proc bodySupply dispatchSupply sites ++
          post))
    (hReturnLabel :
      Assembly.Program.labelPc
        (pre ++ procSegment program proc bodySupply dispatchSupply sites ++
          post)
        site.returnLabel = some returnDest) :
    ARunResultWithGasOracle
      (pre ++ procSegment program proc bodySupply dispatchSupply sites ++ post)
      oracle cursor target
      (fun result cursorFinal =>
        match result with
        | .running final =>
            cursorFinal = cursorAfterBody ∧
              Preservation.Frame.StateRel
                (returned.withEVM { bodyState.evm with stack := stack })
                final tokens ∧
              final.pc = EvmYul.UInt256.ofNat returnDest
        | .halted _ => False) := by
  let ctx := bodyCtx program proc
  let bcode := bodyCode program proc bodySupply
  let dcode := dispatchCode proc sites dispatchSupply
  let callState : RunState :=
    (state.withEVM { state.evm with stack := args }).pushReturn
      callerStack proc.retc
  let exitLabel := ProcLabel.exit proc.name
  have hFrameFacts :=
    regular_body_pop_frame_withGasOracle
      (program := program) (oracle := oracle) (fuel := fuel)
      (cursor := cursor) (cursorFinal := cursorAfterBody)
      (proc := proc) (state := state) (bodyState := bodyState)
      (returned := returned) (args := args) (callerStack := callerStack)
      (stack := stack) (frame := frame) hBody hPop hAttach
  rcases hFrameFacts with ⟨_hFrameEq, _hReturnedReturns, hRetc⟩
  have hReturns : bodyState.returns = frame :: returned.returns :=
    _root_.EvmCompiler.Structured.Preservation.Frame.RunState.popReturn?_returns_eq
      hPop
  have hFitsEntry :
      AssemblyProgram.PCFitsFrom pre
        [Assembly.Instr.label (ProcLabel.entry proc.name)] := by
    exact
      AssemblyProgram.PCFitsFrom.left
        (pre := pre)
        (first := [Assembly.Instr.label (ProcLabel.entry proc.name)])
        (second := bcode ++ ([Assembly.Instr.label exitLabel] ++ dcode))
        (by
          simpa [procSegment, bcode, dcode, bodyCode, dispatchCode, exitLabel,
            List.append_assoc] using hFits)
  have hFitsAfterEntry :
      AssemblyProgram.PCFitsFrom
        (pre ++ [Assembly.Instr.label (ProcLabel.entry proc.name)])
        (bcode ++ ([Assembly.Instr.label exitLabel] ++ dcode)) := by
    exact
      AssemblyProgram.PCFitsFrom.right
        (pre := pre)
        (first := [Assembly.Instr.label (ProcLabel.entry proc.name)])
        (second := bcode ++ ([Assembly.Instr.label exitLabel] ++ dcode))
        (by
          simpa [procSegment, bcode, dcode, bodyCode, dispatchCode, exitLabel,
            List.append_assoc] using hFits)
  have hFitsAfterBody :
      AssemblyProgram.PCFitsFrom
        ((pre ++ [Assembly.Instr.label (ProcLabel.entry proc.name)]) ++ bcode)
        ([Assembly.Instr.label exitLabel] ++ dcode) := by
    exact
      AssemblyProgram.PCFitsFrom.right
        (pre := pre ++ [Assembly.Instr.label (ProcLabel.entry proc.name)])
        (first := bcode)
        (second := [Assembly.Instr.label exitLabel] ++ dcode)
        hFitsAfterEntry
  have hFitsExit :
      AssemblyProgram.PCFitsFrom
        ((pre ++ [Assembly.Instr.label (ProcLabel.entry proc.name)]) ++ bcode)
        [Assembly.Instr.label exitLabel] := by
    exact
      AssemblyProgram.PCFitsFrom.left
        (pre := (pre ++ [Assembly.Instr.label (ProcLabel.entry proc.name)]) ++
          bcode)
        (first := [Assembly.Instr.label exitLabel])
        (second := dcode)
        hFitsAfterBody
  have hFitsDispatch :
      AssemblyProgram.PCFitsFrom
        (((pre ++ [Assembly.Instr.label (ProcLabel.entry proc.name)]) ++ bcode) ++
          [Assembly.Instr.label exitLabel])
        dcode := by
    exact
      AssemblyProgram.PCFitsFrom.right
        (pre := (pre ++ [Assembly.Instr.label (ProcLabel.entry proc.name)]) ++
          bcode)
        (first := [Assembly.Instr.label exitLabel])
        (second := dcode)
        hFitsAfterBody
  have hEntryRun :=
    FrameStateRel.label_runResult_at_withGasOracle
      (label := ProcLabel.entry proc.name) (pre := pre)
      (post := bcode ++ [Assembly.Instr.label exitLabel] ++ dcode ++ post)
      (source := callState) (target := target) (tokens := token :: tokens)
      (oracle := oracle) (cursor := cursor)
      (AssemblyProgram.PCFitsFrom.start hFitsEntry) hPc
      (by simpa [callState] using hRel)
  refine
    ARunResultWithGasOracle.bind_running
      (program :=
        pre ++ procSegment program proc bodySupply dispatchSupply sites ++ post)
      (middle := fun afterEntry cursorAfterEntry =>
        cursorAfterEntry = cursor ∧
          Preservation.Frame.StateRel callState afterEntry (token :: tokens) ∧
          afterEntry.pc =
            Assembly.Program.pcAfter
              (pre ++ [Assembly.Instr.label (ProcLabel.entry proc.name)]))
      ?_ ?_
  · simpa [procSegment, bcode, dcode, bodyCode, dispatchCode, exitLabel,
      callState, List.append_assoc] using hEntryRun
  · intro afterEntry cursorAfterEntry hAfterEntry
    rcases hAfterEntry with
      ⟨hCursorAfterEntry, hRelAfterEntry, hPcAfterEntry⟩
    subst cursorAfterEntry
    have hBodyRun :=
      hBodyPres
        (source := callState)
        (outcome := Outcome.regular bodyState) (target := afterEntry)
        (tokens := token :: tokens) (oracle := oracle)
        (cursor := cursor) (cursorFinal := cursorAfterBody)
        hPcAfterEntry hRelAfterEntry
        (by simpa [callState] using hBody)
    have hBodyRunRegular :
        ARunResultWithGasOracle
          (pre ++ procSegment program proc bodySupply dispatchSupply sites ++
            post)
          oracle cursor afterEntry
          (fun result targetCursorAfterBody =>
            match result with
            | .running afterBody =>
                targetCursorAfterBody = cursorAfterBody ∧
                  Preservation.Frame.StateRel bodyState afterBody
                    (token :: tokens) ∧
                  afterBody.pc =
                    Assembly.Program.pcAfter
                      ((pre ++
                          [Assembly.Instr.label (ProcLabel.entry proc.name)]) ++
                        bcode)
            | .halted _ => False) := by
      exact
        ARunResultWithGasOracle.mono
          (by
            simpa [ProcBodyPreservesAtSegmentWithGasOracle, procSegment,
              bodyCode, dispatchCode, ctx, bcode, dcode, exitLabel,
              List.append_assoc] using hBodyRun)
          (by
            intro result targetCursorAfterBody hResult
            rcases hResult with ⟨hCursorAfterBody, hCompiled⟩
            cases result with
            | halted halt =>
                cases hCompiled
            | running afterBody =>
                exact
                  ⟨hCursorAfterBody, by
                    simpa [CompiledOutcomeRel, Outcome.regular, bcode]
                      using hCompiled⟩)
    refine
      ARunResultWithGasOracle.bind_running
        (program :=
          pre ++ procSegment program proc bodySupply dispatchSupply sites ++
            post)
        (middle := fun afterBody targetCursorAfterBody =>
          targetCursorAfterBody = cursorAfterBody ∧
            Preservation.Frame.StateRel bodyState afterBody (token :: tokens) ∧
            afterBody.pc =
              Assembly.Program.pcAfter
                ((pre ++ [Assembly.Instr.label (ProcLabel.entry proc.name)]) ++
                  bcode))
        hBodyRunRegular ?_
    intro afterBody targetCursorAfterBody hAfterBody
    rcases hAfterBody with
      ⟨hCursorAfterBody, hRelAfterBody, hPcAfterBody⟩
    subst targetCursorAfterBody
    have hTail :=
      exit_label_then_dispatch_withGasOracle
        (proc := proc) (dispatchSupply := dispatchSupply) (sites := sites)
        (site := site) (returnDest := returnDest)
        (bodyState := bodyState) (returned := returned)
        (stack := stack) (frame := frame)
        (target := afterBody) (tokens := tokens) (token := token)
        (preExit :=
          (pre ++ [Assembly.Instr.label (ProcLabel.entry proc.name)]) ++ bcode)
        (post := post) (oracle := oracle) (cursor := cursorAfterBody)
        hAttach hReturns hRetc hMem hNoDup hToken hBound hFitsExit
        (by simpa [dispatchCode, dcode] using hFitsDispatch)
        hPcAfterBody hRelAfterBody
        (by
          simpa [procSegment, bcode, dcode, bodyCode, dispatchCode, exitLabel,
            List.append_assoc] using hExact)
        (by
          simpa [procSegment, bcode, dcode, bodyCode, dispatchCode, exitLabel,
            List.append_assoc] using hReturnLabel)
    simpa [procSegment, bcode, dcode, bodyCode, dispatchCode, exitLabel,
      List.append_assoc] using hTail

theorem leave_body_then_dispatch_withGasOracle {program : Program}
    {proc : Proc}
    {bodySupply dispatchSupply : LabelSupply} {sites : List CallSite}
    {site : CallSite} {returnDest fuel : Nat}
    {state bodyState returned : RunState}
    {args callerStack stack : EvmYul.Stack Word} {frame : ReturnDest}
    {target : EVMState} {tokens : List Word} {token : Word}
    {pre post : Assembly.Program}
    {oracle : GasOracle} {cursor cursorAfterBody : Nat}
    (hBodyPres :
      ProcBodyPreservesAtSegmentWithGasOracle program proc bodySupply
        dispatchSupply sites fuel pre post)
    (hBody :
      Block.EvalWithGasOracle program oracle fuel proc.body cursor
        ((state.withEVM { state.evm with stack := args }).pushReturn
          callerStack proc.retc)
        (Outcome.leave bodyState) cursorAfterBody)
    (hPop : bodyState.popReturn? = some (frame, returned))
    (hAttach :
      StackFrame.attachReturns? frame bodyState.evm.stack = some stack)
    (hMem : site ∈ sites.filter (CallSite.forProc proc.name))
    (hNoDup :
      ((sites.filter (CallSite.forProc proc.name)).map CallSite.token).Nodup)
    (hToken : site.token = token)
    (hBound : proc.retc < 16)
    (hFits :
      AssemblyProgram.PCFitsFrom pre
        (procSegment program proc bodySupply dispatchSupply sites))
    (hPc : target.pc = Assembly.Program.pcAfter pre)
    (hRel :
      Preservation.Frame.StateRel
        ((state.withEVM { state.evm with stack := args }).pushReturn
          callerStack proc.retc)
        target (token :: tokens))
    (hExact :
      ExactLabels
        (pre ++ procSegment program proc bodySupply dispatchSupply sites ++
          post))
    (hReturnLabel :
      Assembly.Program.labelPc
        (pre ++ procSegment program proc bodySupply dispatchSupply sites ++
          post)
        site.returnLabel = some returnDest) :
    ARunResultWithGasOracle
      (pre ++ procSegment program proc bodySupply dispatchSupply sites ++ post)
      oracle cursor target
      (fun result cursorFinal =>
        match result with
        | .running final =>
            cursorFinal = cursorAfterBody ∧
              Preservation.Frame.StateRel
                (returned.withEVM { bodyState.evm with stack := stack })
                final tokens ∧
              final.pc = EvmYul.UInt256.ofNat returnDest
        | .halted _ => False) := by
  let ctx := bodyCtx program proc
  let bcode := bodyCode program proc bodySupply
  let dcode := dispatchCode proc sites dispatchSupply
  let callState : RunState :=
    (state.withEVM { state.evm with stack := args }).pushReturn
      callerStack proc.retc
  let exitLabel := ProcLabel.exit proc.name
  have hFrameFacts :=
    leave_body_pop_frame_withGasOracle
      (program := program) (oracle := oracle) (fuel := fuel)
      (cursor := cursor) (cursorFinal := cursorAfterBody)
      (proc := proc) (state := state) (bodyState := bodyState)
      (returned := returned) (args := args) (callerStack := callerStack)
      (stack := stack) (frame := frame) hBody hPop hAttach
  rcases hFrameFacts with ⟨_hFrameEq, _hReturnedReturns, hRetc⟩
  have hReturns : bodyState.returns = frame :: returned.returns :=
    _root_.EvmCompiler.Structured.Preservation.Frame.RunState.popReturn?_returns_eq
      hPop
  have hFitsEntry :
      AssemblyProgram.PCFitsFrom pre
        [Assembly.Instr.label (ProcLabel.entry proc.name)] := by
    exact
      AssemblyProgram.PCFitsFrom.left
        (pre := pre)
        (first := [Assembly.Instr.label (ProcLabel.entry proc.name)])
        (second := bcode ++ ([Assembly.Instr.label exitLabel] ++ dcode))
        (by
          simpa [procSegment, bcode, dcode, bodyCode, dispatchCode, exitLabel,
            List.append_assoc] using hFits)
  have hFitsAfterEntry :
      AssemblyProgram.PCFitsFrom
        (pre ++ [Assembly.Instr.label (ProcLabel.entry proc.name)])
        (bcode ++ ([Assembly.Instr.label exitLabel] ++ dcode)) := by
    exact
      AssemblyProgram.PCFitsFrom.right
        (pre := pre)
        (first := [Assembly.Instr.label (ProcLabel.entry proc.name)])
        (second := bcode ++ ([Assembly.Instr.label exitLabel] ++ dcode))
        (by
          simpa [procSegment, bcode, dcode, bodyCode, dispatchCode, exitLabel,
            List.append_assoc] using hFits)
  have hFitsAfterBody :
      AssemblyProgram.PCFitsFrom
        ((pre ++ [Assembly.Instr.label (ProcLabel.entry proc.name)]) ++ bcode)
        ([Assembly.Instr.label exitLabel] ++ dcode) := by
    exact
      AssemblyProgram.PCFitsFrom.right
        (pre := pre ++ [Assembly.Instr.label (ProcLabel.entry proc.name)])
        (first := bcode)
        (second := [Assembly.Instr.label exitLabel] ++ dcode)
        hFitsAfterEntry
  have hFitsExit :
      AssemblyProgram.PCFitsFrom
        ((pre ++ [Assembly.Instr.label (ProcLabel.entry proc.name)]) ++ bcode)
        [Assembly.Instr.label exitLabel] := by
    exact
      AssemblyProgram.PCFitsFrom.left
        (pre := (pre ++ [Assembly.Instr.label (ProcLabel.entry proc.name)]) ++
          bcode)
        (first := [Assembly.Instr.label exitLabel])
        (second := dcode)
        hFitsAfterBody
  have hFitsDispatch :
      AssemblyProgram.PCFitsFrom
        (((pre ++ [Assembly.Instr.label (ProcLabel.entry proc.name)]) ++ bcode) ++
          [Assembly.Instr.label exitLabel])
        dcode := by
    exact
      AssemblyProgram.PCFitsFrom.right
        (pre := (pre ++ [Assembly.Instr.label (ProcLabel.entry proc.name)]) ++
          bcode)
        (first := [Assembly.Instr.label exitLabel])
        (second := dcode)
        hFitsAfterBody
  have hExitPc :
      Assembly.Program.labelPc
        (pre ++ procSegment program proc bodySupply dispatchSupply sites ++ post)
        exitLabel =
          some
            (Assembly.Program.byteLength
              ((pre ++ [Assembly.Instr.label (ProcLabel.entry proc.name)]) ++
                bcode)) := by
    have hHere :=
      hExact.labelPc_at
        ((pre ++ [Assembly.Instr.label (ProcLabel.entry proc.name)]) ++ bcode)
        exitLabel
        (dcode ++ post)
        (by
          simp [procSegment, bcode, dcode, bodyCode, dispatchCode, exitLabel,
            List.append_assoc])
    simpa [bcode, dcode, exitLabel] using hHere
  have hExitPcBody :
      Assembly.Program.labelPc
        ((pre ++ [Assembly.Instr.label (ProcLabel.entry proc.name)]) ++
          bcode ++ ([Assembly.Instr.label exitLabel] ++ dcode ++ post))
        exitLabel =
          some
            (Assembly.Program.byteLength
              ((pre ++ [Assembly.Instr.label (ProcLabel.entry proc.name)]) ++
                bcode)) := by
    simpa [procSegment, bcode, dcode, bodyCode, dispatchCode, exitLabel,
      List.append_assoc] using hExitPc
  have hEntryRun :=
    FrameStateRel.label_runResult_at_withGasOracle
      (label := ProcLabel.entry proc.name) (pre := pre)
      (post := bcode ++ [Assembly.Instr.label exitLabel] ++ dcode ++ post)
      (source := callState) (target := target) (tokens := token :: tokens)
      (oracle := oracle) (cursor := cursor)
      (AssemblyProgram.PCFitsFrom.start hFitsEntry) hPc
      (by simpa [callState] using hRel)
  refine
    ARunResultWithGasOracle.bind_running
      (program :=
        pre ++ procSegment program proc bodySupply dispatchSupply sites ++ post)
      (middle := fun afterEntry cursorAfterEntry =>
        cursorAfterEntry = cursor ∧
          Preservation.Frame.StateRel callState afterEntry (token :: tokens) ∧
          afterEntry.pc =
            Assembly.Program.pcAfter
              (pre ++ [Assembly.Instr.label (ProcLabel.entry proc.name)]))
      ?_ ?_
  · simpa [procSegment, bcode, dcode, bodyCode, dispatchCode, exitLabel,
      callState, List.append_assoc] using hEntryRun
  · intro afterEntry cursorAfterEntry hAfterEntry
    rcases hAfterEntry with
      ⟨hCursorAfterEntry, hRelAfterEntry, hPcAfterEntry⟩
    subst cursorAfterEntry
    have hBodyRun :=
      hBodyPres
        (source := callState)
        (outcome := Outcome.leave bodyState) (target := afterEntry)
        (tokens := token :: tokens) (oracle := oracle)
        (cursor := cursor) (cursorFinal := cursorAfterBody)
        hPcAfterEntry hRelAfterEntry
        (by simpa [callState] using hBody)
    have hBodyRunLeave :
        ARunResultWithGasOracle
          (pre ++ procSegment program proc bodySupply dispatchSupply sites ++
            post)
          oracle cursor afterEntry
          (fun result targetCursorAfterBody =>
            match result with
            | .running afterBody =>
                targetCursorAfterBody = cursorAfterBody ∧
                  Preservation.Frame.StateRel bodyState afterBody
                    (token :: tokens) ∧
                  afterBody.pc =
                    Assembly.Program.pcAfter
                      ((pre ++
                          [Assembly.Instr.label (ProcLabel.entry proc.name)]) ++
                        bcode)
            | .halted _ => False) := by
      exact
        ARunResultWithGasOracle.mono
          (by
            simpa [ProcBodyPreservesAtSegmentWithGasOracle, procSegment,
              bodyCode, dispatchCode, ctx, bcode, dcode, exitLabel,
              List.append_assoc] using hBodyRun)
          (by
            intro result targetCursorAfterBody hResult
            rcases hResult with ⟨hCursorAfterBody, hCompiled⟩
            cases result with
            | halted halt =>
                cases hCompiled
            | running afterBody =>
                rcases hCompiled with
                  ⟨label, dest, hCtxLeave, hLabelPc, hRelAfter, hPcAfter⟩
                simp [bodyCtx] at hCtxLeave
                subst label
                have hLabelPcNorm :
                    Assembly.Program.labelPc
                      ((pre ++
                          [Assembly.Instr.label (ProcLabel.entry proc.name)]) ++
                        bcode ++
                          ([Assembly.Instr.label exitLabel] ++ dcode ++ post))
                      exitLabel = some dest := by
                  simpa [bodyCode, dispatchCode, bcode, dcode, exitLabel,
                    List.append_assoc] using hLabelPc
                rw [hExitPcBody] at hLabelPcNorm
                cases hLabelPcNorm
                exact ⟨hCursorAfterBody, hRelAfter, by
                  simpa [Assembly.Program.pcAfter] using hPcAfter⟩)
    refine
      ARunResultWithGasOracle.bind_running
        (program :=
          pre ++ procSegment program proc bodySupply dispatchSupply sites ++
            post)
        (middle := fun afterBody targetCursorAfterBody =>
          targetCursorAfterBody = cursorAfterBody ∧
            Preservation.Frame.StateRel bodyState afterBody (token :: tokens) ∧
            afterBody.pc =
              Assembly.Program.pcAfter
                ((pre ++ [Assembly.Instr.label (ProcLabel.entry proc.name)]) ++
                  bcode))
        hBodyRunLeave ?_
    intro afterBody targetCursorAfterBody hAfterBody
    rcases hAfterBody with
      ⟨hCursorAfterBody, hRelAfterBody, hPcAfterBody⟩
    subst targetCursorAfterBody
    have hTail :=
      exit_label_then_dispatch_withGasOracle
        (proc := proc) (dispatchSupply := dispatchSupply) (sites := sites)
        (site := site) (returnDest := returnDest)
        (bodyState := bodyState) (returned := returned)
        (stack := stack) (frame := frame)
        (target := afterBody) (tokens := tokens) (token := token)
        (preExit :=
          (pre ++ [Assembly.Instr.label (ProcLabel.entry proc.name)]) ++ bcode)
        (post := post) (oracle := oracle) (cursor := cursorAfterBody)
        hAttach hReturns hRetc hMem hNoDup hToken hBound hFitsExit
        (by simpa [dispatchCode, dcode] using hFitsDispatch)
        hPcAfterBody hRelAfterBody
        (by
          simpa [procSegment, bcode, dcode, bodyCode, dispatchCode, exitLabel,
            List.append_assoc] using hExact)
        (by
          simpa [procSegment, bcode, dcode, bodyCode, dispatchCode, exitLabel,
            List.append_assoc] using hReturnLabel)
    simpa [procSegment, bcode, dcode, bodyCode, dispatchCode, exitLabel,
      List.append_assoc] using hTail

theorem halt_body_from_entry_withGasOracle {program : Program} {proc : Proc}
    {bodySupply dispatchSupply : LabelSupply} {sites : List CallSite}
    {fuel : Nat} {state bodyState : RunState} {kind : Assembly.HaltKind}
    {args callerStack : EvmYul.Stack Word}
    {target : EVMState} {tokens : List Word} {token : Word}
    {pre post : Assembly.Program}
    {oracle : GasOracle} {cursor cursorAfterBody : Nat}
    (hBodyPres :
      ProcBodyPreservesAtSegmentWithGasOracle program proc bodySupply
        dispatchSupply sites fuel pre post)
    (hBody :
      Block.EvalWithGasOracle program oracle fuel proc.body cursor
        ((state.withEVM { state.evm with stack := args }).pushReturn
          callerStack proc.retc)
        (Outcome.halt kind bodyState) cursorAfterBody)
    (hFits :
      AssemblyProgram.PCFitsFrom pre
        (procSegment program proc bodySupply dispatchSupply sites))
    (hPc : target.pc = Assembly.Program.pcAfter pre)
    (hRel :
      Preservation.Frame.StateRel
        ((state.withEVM { state.evm with stack := args }).pushReturn
          callerStack proc.retc)
        target (token :: tokens))
    (_hExact :
      ExactLabels
        (pre ++ procSegment program proc bodySupply dispatchSupply sites ++
          post)) :
    ARunResultWithGasOracle
      (pre ++ procSegment program proc bodySupply dispatchSupply sites ++ post)
      oracle cursor target
      (fun result cursorFinal =>
        cursorFinal = cursorAfterBody ∧
          CompiledOutcomeRel
            (pre ++ procSegment program proc bodySupply dispatchSupply sites ++
              post)
            (bodyCtx program proc)
            (Assembly.Program.pcAfter
              (pre ++ procSegment program proc bodySupply dispatchSupply sites))
            (Outcome.halt kind bodyState) result tokens) := by
  let ctx := bodyCtx program proc
  let bcode := bodyCode program proc bodySupply
  let dcode := dispatchCode proc sites dispatchSupply
  let callState : RunState :=
    (state.withEVM { state.evm with stack := args }).pushReturn
      callerStack proc.retc
  let exitLabel := ProcLabel.exit proc.name
  have hFitsEntry :
      AssemblyProgram.PCFitsFrom pre
        [Assembly.Instr.label (ProcLabel.entry proc.name)] := by
    exact
      AssemblyProgram.PCFitsFrom.left
        (pre := pre)
        (first := [Assembly.Instr.label (ProcLabel.entry proc.name)])
        (second := bcode ++ ([Assembly.Instr.label exitLabel] ++ dcode))
        (by
          simpa [procSegment, bcode, dcode, bodyCode, dispatchCode, exitLabel,
            List.append_assoc] using hFits)
  have hEntryRun :=
    FrameStateRel.label_runResult_at_withGasOracle
      (label := ProcLabel.entry proc.name) (pre := pre)
      (post := bcode ++ [Assembly.Instr.label exitLabel] ++ dcode ++ post)
      (source := callState) (target := target) (tokens := token :: tokens)
      (oracle := oracle) (cursor := cursor)
      (AssemblyProgram.PCFitsFrom.start hFitsEntry) hPc
      (by simpa [callState] using hRel)
  refine
    ARunResultWithGasOracle.bind_running
      (program :=
        pre ++ procSegment program proc bodySupply dispatchSupply sites ++ post)
      (middle := fun afterEntry cursorAfterEntry =>
        cursorAfterEntry = cursor ∧
          Preservation.Frame.StateRel callState afterEntry (token :: tokens) ∧
          afterEntry.pc =
            Assembly.Program.pcAfter
              (pre ++ [Assembly.Instr.label (ProcLabel.entry proc.name)]))
      ?_ ?_
  · simpa [procSegment, bcode, dcode, bodyCode, dispatchCode, exitLabel,
      callState, List.append_assoc] using hEntryRun
  · intro afterEntry cursorAfterEntry hAfterEntry
    rcases hAfterEntry with
      ⟨hCursorAfterEntry, hRelAfterEntry, hPcAfterEntry⟩
    subst cursorAfterEntry
    have hBodyRun :=
      hBodyPres
        (source := callState)
        (outcome := Outcome.halt kind bodyState) (target := afterEntry)
        (tokens := token :: tokens) (oracle := oracle)
        (cursor := cursor) (cursorFinal := cursorAfterBody)
        hPcAfterEntry hRelAfterEntry
        (by simpa [callState] using hBody)
    exact
      ARunResultWithGasOracle.mono
        (by
          simpa [ProcBodyPreservesAtSegmentWithGasOracle, procSegment,
            bodyCode, dispatchCode, ctx, bcode, dcode, exitLabel,
            List.append_assoc] using hBodyRun)
        (by
          intro result targetCursorFinal hResult
          rcases hResult with ⟨hCursorFinal, hCompiled⟩
          cases result with
          | running afterBody =>
              cases hCompiled
          | halted halt =>
              exact
                ⟨hCursorFinal, by
                  simpa [CompiledOutcomeRel, Outcome.halt] using hCompiled⟩)

end ProcedureCall

namespace ProcedureCall

theorem call_regular_segments_withGasOracle {program : Program}
    {ctx : CompileContext}
    {proc : Proc} {bodySupply dispatchSupply : LabelSupply}
    {sites : List CallSite} {site : CallSite} {fuel : Nat}
    {state bodyState returned : RunState}
    {args callerStack stack : EvmYul.Stack Word} {frame : ReturnDest}
    {target : EVMState} {tokens : List Word} {token : Word}
    {asm : Assembly.Program} {oracle : GasOracle}
    {cursor cursorAfterBody : Nat}
    (callSeg :
      CodeSegment asm (callSiteCode proc args token site.returnLabel))
    (procSeg :
      CodeSegment asm
        (procSegment program proc bodySupply dispatchSupply sites))
    (hBodyPres :
      ProcBodyPreservesAtSegmentWithGasOracle program proc bodySupply
        dispatchSupply sites fuel procSeg.pre procSeg.post)
    (hSplit :
      StackFrame.splitArgs? proc.argc state.evm.stack =
        some (args, callerStack))
    (hBody :
      Block.EvalWithGasOracle program oracle fuel proc.body cursor
        ((state.withEVM { state.evm with stack := args }).pushReturn
          callerStack proc.retc)
        (Outcome.regular bodyState) cursorAfterBody)
    (hPop : bodyState.popReturn? = some (frame, returned))
    (hAttach :
      StackFrame.attachReturns? frame bodyState.evm.stack = some stack)
    (hMem : site ∈ sites.filter (CallSite.forProc proc.name))
    (hNoDup :
      ((sites.filter (CallSite.forProc proc.name)).map CallSite.token).Nodup)
    (hToken : site.token = token)
    (hArgBound : args.length ≤ 16)
    (hBound : proc.retc < 16)
    (hPc : target.pc = callSeg.startPc)
    (hRel : Preservation.Frame.StateRel state target tokens)
    (hExact : ExactLabels asm) :
    ARunResultWithGasOracle asm oracle cursor target
      (fun result targetCursorFinal =>
        targetCursorFinal = cursorAfterBody ∧
          CompiledOutcomeRel asm ctx callSeg.fallthroughPc
            (Outcome.regular
              (returned.withEVM { bodyState.evm with stack := stack }))
            result tokens) := by
  let jumpCode := callJumpCode proc args token
  let returnCode : Assembly.Program := [Assembly.Instr.label site.returnLabel]
  let procCode := procSegment program proc bodySupply dispatchSupply sites
  have hCallAsm :
      asm = callSeg.pre ++ jumpCode ++ returnCode ++ callSeg.post := by
    calc
      asm =
          callSeg.pre ++ callSiteCode proc args token site.returnLabel ++
            callSeg.post := callSeg.hAsm
      _ = callSeg.pre ++ jumpCode ++ returnCode ++ callSeg.post := by
            simp [callSiteCode, jumpCode, returnCode, List.append_assoc]
  have hProcAsm :
      asm = procSeg.pre ++ procCode ++ procSeg.post := by
    simpa [procCode] using procSeg.hAsm
  have hCallFits :
      AssemblyProgram.PCFitsFrom callSeg.pre (jumpCode ++ returnCode) := by
    simpa [callSiteCode, jumpCode, returnCode, List.append_assoc] using
      callSeg.hFits
  have hFitsJump :
      AssemblyProgram.PCFitsFrom callSeg.pre jumpCode := by
    exact
      AssemblyProgram.PCFitsFrom.left
        (pre := callSeg.pre) (first := jumpCode) (second := returnCode)
        hCallFits
  have hFitsAfterJump :
      AssemblyProgram.PCFitsFrom (callSeg.pre ++ jumpCode) returnCode := by
    exact
      AssemblyProgram.PCFitsFrom.right
        (pre := callSeg.pre) (first := jumpCode) (second := returnCode)
        hCallFits
  have hEntryPcAsm :
      Assembly.Program.labelPc asm (ProcLabel.entry proc.name) =
        some (Assembly.Program.byteLength procSeg.pre) := by
    have hHere :=
      hExact.labelPc_at procSeg.pre (ProcLabel.entry proc.name)
        (bodyCode program proc bodySupply ++
          [Assembly.Instr.label (ProcLabel.exit proc.name)] ++
          dispatchCode proc sites dispatchSupply ++ procSeg.post)
        (by
          simpa [procCode, procSegment, bodyCode, dispatchCode,
            List.append_assoc] using procSeg.hAsm)
    simpa using hHere
  have hEntryPcCall :
      Assembly.Program.labelPc
        (callSeg.pre ++ jumpCode ++ returnCode ++ callSeg.post)
        (ProcLabel.entry proc.name) =
          some (Assembly.Program.byteLength procSeg.pre) := by
    rw [← hCallAsm]
    exact hEntryPcAsm
  have hReturnPcAsm :
      Assembly.Program.labelPc asm site.returnLabel =
        some (Assembly.Program.byteLength (callSeg.pre ++ jumpCode)) := by
    have hHere :=
      hExact.labelPc_at (callSeg.pre ++ jumpCode) site.returnLabel
        callSeg.post
        (by
          simpa [callSiteCode, jumpCode, returnCode, List.append_assoc]
            using callSeg.hAsm)
    simpa using hHere
  have hReturnPcProc :
      Assembly.Program.labelPc (procSeg.pre ++ procCode ++ procSeg.post)
        site.returnLabel =
          some (Assembly.Program.byteLength (callSeg.pre ++ jumpCode)) := by
    rw [← hProcAsm]
    exact hReturnPcAsm
  have hExactProc :
      ExactLabels (procSeg.pre ++ procCode ++ procSeg.post) := by
    exact ExactLabels.cast_asm hProcAsm hExact
  have hCallEntry :=
    FrameStateRel.source_callEntry_after_prologue_and_jump_withGasOracle
      (source := state) (target := target) (tokens := tokens)
      (argc := proc.argc) (retc := proc.retc) (args := args)
      (callerStack := callerStack) (token := token)
      (entryLabel := ProcLabel.entry proc.name)
      (entryDest := Assembly.Program.byteLength procSeg.pre)
      (pre := callSeg.pre) (post := returnCode ++ callSeg.post)
      (oracle := oracle) (cursor := cursor)
      (by simpa [jumpCode, callJumpCode, List.append_assoc] using hFitsJump)
      (by simpa [CodeSegment.startPc] using hPc) hRel hSplit hArgBound
      (by
        simpa [callSiteCode, callJumpCode, jumpCode, returnCode,
          List.append_assoc]
          using hEntryPcCall)
  refine
    ARunResultWithGasOracle.bind_running
      (program := asm) (oracle := oracle) (cursor := cursor)
      (state := target)
      (middle := fun afterJump targetCursorAfterJump =>
        targetCursorAfterJump = cursor ∧
          Preservation.Frame.StateRel
            ((state.withEVM { state.evm with stack := args }).pushReturn
              callerStack proc.retc)
            afterJump (token :: tokens) ∧
          afterJump.pc = Assembly.Program.pcAfter procSeg.pre)
      ?_ ?_
  · exact
      ARunResultWithGasOracle.mono
        (by
          rw [hCallAsm]
          simpa [callJumpCode, jumpCode, returnCode, List.append_assoc]
            using hCallEntry)
        (by
          intro result targetCursorAfterJump hResult
          cases result with
          | halted halt =>
              cases hResult
          | running afterJump =>
              rcases hResult with
                ⟨hCursorAfterJump, hRelAfterJump, hPcAfterJump⟩
              exact ⟨hCursorAfterJump, hRelAfterJump, by
                simpa [Assembly.Program.pcAfter] using hPcAfterJump⟩)
  · intro afterJump targetCursorAfterJump hAfterJump
    rcases hAfterJump with
      ⟨hTargetCursorAfterJump, hRelAfterJump, hPcAfterJump⟩
    subst targetCursorAfterJump
    have hBodyDispatch :=
      regular_body_then_dispatch_withGasOracle
        (program := program) (proc := proc) (bodySupply := bodySupply)
        (dispatchSupply := dispatchSupply) (sites := sites)
        (site := site)
        (returnDest := Assembly.Program.byteLength (callSeg.pre ++ jumpCode))
        (fuel := fuel) (state := state) (bodyState := bodyState)
        (returned := returned) (args := args) (callerStack := callerStack)
        (stack := stack) (frame := frame) (target := afterJump)
        (tokens := tokens) (token := token) (pre := procSeg.pre)
        (post := procSeg.post) (oracle := oracle) (cursor := cursor)
        (cursorAfterBody := cursorAfterBody)
        hBodyPres hBody hPop hAttach hMem hNoDup hToken hBound
        (by simpa [procCode] using procSeg.hFits)
        hPcAfterJump hRelAfterJump hExactProc hReturnPcProc
    refine
      ARunResultWithGasOracle.bind_running
        (program := asm) (oracle := oracle) (cursor := cursor)
        (state := afterJump)
        (middle := fun afterDispatch targetCursorAfterDispatch =>
          targetCursorAfterDispatch = cursorAfterBody ∧
            Preservation.Frame.StateRel
              (returned.withEVM { bodyState.evm with stack := stack })
              afterDispatch tokens ∧
            afterDispatch.pc =
              Assembly.Program.pcAfter (callSeg.pre ++ jumpCode))
        ?_ ?_
    · exact
        ARunResultWithGasOracle.mono
          (by
            rw [hProcAsm]
            simpa [procCode] using hBodyDispatch)
          (by
            intro result targetCursorAfterDispatch hResult
            cases result with
            | halted halt =>
                cases hResult
            | running afterDispatch =>
                rcases hResult with
                  ⟨hCursorAfterDispatch, hRelAfterDispatch,
                    hPcAfterDispatch⟩
                exact ⟨hCursorAfterDispatch, hRelAfterDispatch, by
                  simpa [Assembly.Program.pcAfter] using hPcAfterDispatch⟩)
    · intro afterDispatch targetCursorAfterDispatch hAfterDispatch
      rcases hAfterDispatch with
        ⟨hTargetCursorAfterDispatch, hRelAfterDispatch, hPcAfterDispatch⟩
      subst targetCursorAfterDispatch
      have hReturnRun :=
        FrameStateRel.label_runResult_at_withGasOracle
          (label := site.returnLabel) (pre := callSeg.pre ++ jumpCode)
          (post := callSeg.post)
          (source :=
            returned.withEVM { bodyState.evm with stack := stack })
          (target := afterDispatch) (tokens := tokens)
          (oracle := oracle) (cursor := cursorAfterBody)
          (AssemblyProgram.PCFitsFrom.start hFitsAfterJump)
          hPcAfterDispatch hRelAfterDispatch
      exact
        ARunResultWithGasOracle.mono
          (by
            rw [hCallAsm]
            simpa [callSiteCode, callJumpCode, jumpCode, returnCode,
              List.append_assoc]
              using hReturnRun)
          (by
            intro result targetCursorFinal hResult
            cases result with
            | halted halt =>
                cases hResult
            | running final =>
                rcases hResult with
                  ⟨hCursorFinal, hRelFinal, hPcFinal⟩
                exact ⟨hCursorFinal, by
                  simpa [CodeSegment.fallthroughPc, callSiteCode,
                    callJumpCode, jumpCode, returnCode, List.append_assoc]
                    using And.intro hRelFinal hPcFinal⟩)

theorem call_leave_segments_withGasOracle {program : Program}
    {ctx : CompileContext}
    {proc : Proc} {bodySupply dispatchSupply : LabelSupply}
    {sites : List CallSite} {site : CallSite} {fuel : Nat}
    {state bodyState returned : RunState}
    {args callerStack stack : EvmYul.Stack Word} {frame : ReturnDest}
    {target : EVMState} {tokens : List Word} {token : Word}
    {asm : Assembly.Program} {oracle : GasOracle}
    {cursor cursorAfterBody : Nat}
    (callSeg :
      CodeSegment asm (callSiteCode proc args token site.returnLabel))
    (procSeg :
      CodeSegment asm
        (procSegment program proc bodySupply dispatchSupply sites))
    (hBodyPres :
      ProcBodyPreservesAtSegmentWithGasOracle program proc bodySupply
        dispatchSupply sites fuel procSeg.pre procSeg.post)
    (hSplit :
      StackFrame.splitArgs? proc.argc state.evm.stack =
        some (args, callerStack))
    (hBody :
      Block.EvalWithGasOracle program oracle fuel proc.body cursor
        ((state.withEVM { state.evm with stack := args }).pushReturn
          callerStack proc.retc)
        (Outcome.leave bodyState) cursorAfterBody)
    (hPop : bodyState.popReturn? = some (frame, returned))
    (hAttach :
      StackFrame.attachReturns? frame bodyState.evm.stack = some stack)
    (hMem : site ∈ sites.filter (CallSite.forProc proc.name))
    (hNoDup :
      ((sites.filter (CallSite.forProc proc.name)).map CallSite.token).Nodup)
    (hToken : site.token = token)
    (hArgBound : args.length ≤ 16)
    (hBound : proc.retc < 16)
    (hPc : target.pc = callSeg.startPc)
    (hRel : Preservation.Frame.StateRel state target tokens)
    (hExact : ExactLabels asm) :
    ARunResultWithGasOracle asm oracle cursor target
      (fun result targetCursorFinal =>
        targetCursorFinal = cursorAfterBody ∧
          CompiledOutcomeRel asm ctx callSeg.fallthroughPc
            (Outcome.regular
              (returned.withEVM { bodyState.evm with stack := stack }))
            result tokens) := by
  let jumpCode := callJumpCode proc args token
  let returnCode : Assembly.Program := [Assembly.Instr.label site.returnLabel]
  let procCode := procSegment program proc bodySupply dispatchSupply sites
  have hCallAsm :
      asm = callSeg.pre ++ jumpCode ++ returnCode ++ callSeg.post := by
    calc
      asm =
          callSeg.pre ++ callSiteCode proc args token site.returnLabel ++
            callSeg.post := callSeg.hAsm
      _ = callSeg.pre ++ jumpCode ++ returnCode ++ callSeg.post := by
            simp [callSiteCode, jumpCode, returnCode, List.append_assoc]
  have hProcAsm :
      asm = procSeg.pre ++ procCode ++ procSeg.post := by
    simpa [procCode] using procSeg.hAsm
  have hCallFits :
      AssemblyProgram.PCFitsFrom callSeg.pre (jumpCode ++ returnCode) := by
    simpa [callSiteCode, jumpCode, returnCode, List.append_assoc] using
      callSeg.hFits
  have hFitsJump :
      AssemblyProgram.PCFitsFrom callSeg.pre jumpCode := by
    exact
      AssemblyProgram.PCFitsFrom.left
        (pre := callSeg.pre) (first := jumpCode) (second := returnCode)
        hCallFits
  have hFitsAfterJump :
      AssemblyProgram.PCFitsFrom (callSeg.pre ++ jumpCode) returnCode := by
    exact
      AssemblyProgram.PCFitsFrom.right
        (pre := callSeg.pre) (first := jumpCode) (second := returnCode)
        hCallFits
  have hEntryPcAsm :
      Assembly.Program.labelPc asm (ProcLabel.entry proc.name) =
        some (Assembly.Program.byteLength procSeg.pre) := by
    have hHere :=
      hExact.labelPc_at procSeg.pre (ProcLabel.entry proc.name)
        (bodyCode program proc bodySupply ++
          [Assembly.Instr.label (ProcLabel.exit proc.name)] ++
          dispatchCode proc sites dispatchSupply ++ procSeg.post)
        (by
          simpa [procCode, procSegment, bodyCode, dispatchCode,
            List.append_assoc] using procSeg.hAsm)
    simpa using hHere
  have hEntryPcCall :
      Assembly.Program.labelPc
        (callSeg.pre ++ jumpCode ++ returnCode ++ callSeg.post)
        (ProcLabel.entry proc.name) =
          some (Assembly.Program.byteLength procSeg.pre) := by
    rw [← hCallAsm]
    exact hEntryPcAsm
  have hReturnPcAsm :
      Assembly.Program.labelPc asm site.returnLabel =
        some (Assembly.Program.byteLength (callSeg.pre ++ jumpCode)) := by
    have hHere :=
      hExact.labelPc_at (callSeg.pre ++ jumpCode) site.returnLabel
        callSeg.post
        (by
          simpa [callSiteCode, jumpCode, returnCode, List.append_assoc]
            using callSeg.hAsm)
    simpa using hHere
  have hReturnPcProc :
      Assembly.Program.labelPc (procSeg.pre ++ procCode ++ procSeg.post)
        site.returnLabel =
          some (Assembly.Program.byteLength (callSeg.pre ++ jumpCode)) := by
    rw [← hProcAsm]
    exact hReturnPcAsm
  have hExactProc :
      ExactLabels (procSeg.pre ++ procCode ++ procSeg.post) := by
    exact ExactLabels.cast_asm hProcAsm hExact
  have hCallEntry :=
    FrameStateRel.source_callEntry_after_prologue_and_jump_withGasOracle
      (source := state) (target := target) (tokens := tokens)
      (argc := proc.argc) (retc := proc.retc) (args := args)
      (callerStack := callerStack) (token := token)
      (entryLabel := ProcLabel.entry proc.name)
      (entryDest := Assembly.Program.byteLength procSeg.pre)
      (pre := callSeg.pre) (post := returnCode ++ callSeg.post)
      (oracle := oracle) (cursor := cursor)
      (by simpa [jumpCode, callJumpCode, List.append_assoc] using hFitsJump)
      (by simpa [CodeSegment.startPc] using hPc) hRel hSplit hArgBound
      (by
        simpa [callSiteCode, callJumpCode, jumpCode, returnCode,
          List.append_assoc]
          using hEntryPcCall)
  refine
    ARunResultWithGasOracle.bind_running
      (program := asm) (oracle := oracle) (cursor := cursor)
      (state := target)
      (middle := fun afterJump targetCursorAfterJump =>
        targetCursorAfterJump = cursor ∧
          Preservation.Frame.StateRel
            ((state.withEVM { state.evm with stack := args }).pushReturn
              callerStack proc.retc)
            afterJump (token :: tokens) ∧
          afterJump.pc = Assembly.Program.pcAfter procSeg.pre)
      ?_ ?_
  · exact
      ARunResultWithGasOracle.mono
        (by
          rw [hCallAsm]
          simpa [callJumpCode, jumpCode, returnCode, List.append_assoc]
            using hCallEntry)
        (by
          intro result targetCursorAfterJump hResult
          cases result with
          | halted halt =>
              cases hResult
          | running afterJump =>
              rcases hResult with
                ⟨hCursorAfterJump, hRelAfterJump, hPcAfterJump⟩
              exact ⟨hCursorAfterJump, hRelAfterJump, by
                simpa [Assembly.Program.pcAfter] using hPcAfterJump⟩)
  · intro afterJump targetCursorAfterJump hAfterJump
    rcases hAfterJump with
      ⟨hTargetCursorAfterJump, hRelAfterJump, hPcAfterJump⟩
    subst targetCursorAfterJump
    have hBodyDispatch :=
      leave_body_then_dispatch_withGasOracle
        (program := program) (proc := proc) (bodySupply := bodySupply)
        (dispatchSupply := dispatchSupply) (sites := sites)
        (site := site)
        (returnDest := Assembly.Program.byteLength (callSeg.pre ++ jumpCode))
        (fuel := fuel) (state := state) (bodyState := bodyState)
        (returned := returned) (args := args) (callerStack := callerStack)
        (stack := stack) (frame := frame) (target := afterJump)
        (tokens := tokens) (token := token) (pre := procSeg.pre)
        (post := procSeg.post) (oracle := oracle) (cursor := cursor)
        (cursorAfterBody := cursorAfterBody)
        hBodyPres hBody hPop hAttach hMem hNoDup hToken hBound
        (by simpa [procCode] using procSeg.hFits)
        hPcAfterJump hRelAfterJump hExactProc hReturnPcProc
    refine
      ARunResultWithGasOracle.bind_running
        (program := asm) (oracle := oracle) (cursor := cursor)
        (state := afterJump)
        (middle := fun afterDispatch targetCursorAfterDispatch =>
          targetCursorAfterDispatch = cursorAfterBody ∧
            Preservation.Frame.StateRel
              (returned.withEVM { bodyState.evm with stack := stack })
              afterDispatch tokens ∧
            afterDispatch.pc =
              Assembly.Program.pcAfter (callSeg.pre ++ jumpCode))
        ?_ ?_
    · exact
        ARunResultWithGasOracle.mono
          (by
            rw [hProcAsm]
            simpa [procCode] using hBodyDispatch)
          (by
            intro result targetCursorAfterDispatch hResult
            cases result with
            | halted halt =>
                cases hResult
            | running afterDispatch =>
                rcases hResult with
                  ⟨hCursorAfterDispatch, hRelAfterDispatch,
                    hPcAfterDispatch⟩
                exact ⟨hCursorAfterDispatch, hRelAfterDispatch, by
                  simpa [Assembly.Program.pcAfter] using hPcAfterDispatch⟩)
    · intro afterDispatch targetCursorAfterDispatch hAfterDispatch
      rcases hAfterDispatch with
        ⟨hTargetCursorAfterDispatch, hRelAfterDispatch, hPcAfterDispatch⟩
      subst targetCursorAfterDispatch
      have hReturnRun :=
        FrameStateRel.label_runResult_at_withGasOracle
          (label := site.returnLabel) (pre := callSeg.pre ++ jumpCode)
          (post := callSeg.post)
          (source :=
            returned.withEVM { bodyState.evm with stack := stack })
          (target := afterDispatch) (tokens := tokens)
          (oracle := oracle) (cursor := cursorAfterBody)
          (AssemblyProgram.PCFitsFrom.start hFitsAfterJump)
          hPcAfterDispatch hRelAfterDispatch
      exact
        ARunResultWithGasOracle.mono
          (by
            rw [hCallAsm]
            simpa [callSiteCode, callJumpCode, jumpCode, returnCode,
              List.append_assoc]
              using hReturnRun)
          (by
            intro result targetCursorFinal hResult
            cases result with
            | halted halt =>
                cases hResult
            | running final =>
                rcases hResult with
                  ⟨hCursorFinal, hRelFinal, hPcFinal⟩
                exact ⟨hCursorFinal, by
                  simpa [CodeSegment.fallthroughPc, callSiteCode,
                    callJumpCode, jumpCode, returnCode, List.append_assoc]
                    using And.intro hRelFinal hPcFinal⟩)

theorem call_halt_segments_withGasOracle {program : Program}
    {ctx : CompileContext}
    {proc : Proc} {bodySupply dispatchSupply : LabelSupply}
    {sites : List CallSite} {site : CallSite} {fuel : Nat}
    {state bodyState : RunState} {kind : Assembly.HaltKind}
    {args callerStack : EvmYul.Stack Word}
    {target : EVMState} {tokens : List Word} {token : Word}
    {asm : Assembly.Program} {oracle : GasOracle}
    {cursor cursorAfterBody : Nat}
    (callSeg :
      CodeSegment asm (callSiteCode proc args token site.returnLabel))
    (procSeg :
      CodeSegment asm
        (procSegment program proc bodySupply dispatchSupply sites))
    (hBodyPres :
      ProcBodyPreservesAtSegmentWithGasOracle program proc bodySupply
        dispatchSupply sites fuel procSeg.pre procSeg.post)
    (hSplit :
      StackFrame.splitArgs? proc.argc state.evm.stack =
        some (args, callerStack))
    (hBody :
      Block.EvalWithGasOracle program oracle fuel proc.body cursor
        ((state.withEVM { state.evm with stack := args }).pushReturn
          callerStack proc.retc)
        (Outcome.halt kind bodyState) cursorAfterBody)
    (hArgBound : args.length ≤ 16)
    (hPc : target.pc = callSeg.startPc)
    (hRel : Preservation.Frame.StateRel state target tokens)
    (hExact : ExactLabels asm) :
    ARunResultWithGasOracle asm oracle cursor target
      (fun result targetCursorFinal =>
        targetCursorFinal = cursorAfterBody ∧
          CompiledOutcomeRel asm ctx callSeg.fallthroughPc
            (Outcome.halt kind bodyState) result tokens) := by
  let jumpCode := callJumpCode proc args token
  let returnCode : Assembly.Program := [Assembly.Instr.label site.returnLabel]
  let procCode := procSegment program proc bodySupply dispatchSupply sites
  have hCallAsm :
      asm = callSeg.pre ++ jumpCode ++ returnCode ++ callSeg.post := by
    calc
      asm =
          callSeg.pre ++ callSiteCode proc args token site.returnLabel ++
            callSeg.post := callSeg.hAsm
      _ = callSeg.pre ++ jumpCode ++ returnCode ++ callSeg.post := by
            simp [callSiteCode, jumpCode, returnCode, List.append_assoc]
  have hProcAsm :
      asm = procSeg.pre ++ procCode ++ procSeg.post := by
    simpa [procCode] using procSeg.hAsm
  have hCallFits :
      AssemblyProgram.PCFitsFrom callSeg.pre (jumpCode ++ returnCode) := by
    simpa [callSiteCode, jumpCode, returnCode, List.append_assoc] using
      callSeg.hFits
  have hFitsJump :
      AssemblyProgram.PCFitsFrom callSeg.pre jumpCode := by
    exact
      AssemblyProgram.PCFitsFrom.left
        (pre := callSeg.pre) (first := jumpCode) (second := returnCode)
        hCallFits
  have hEntryPcAsm :
      Assembly.Program.labelPc asm (ProcLabel.entry proc.name) =
        some (Assembly.Program.byteLength procSeg.pre) := by
    have hHere :=
      hExact.labelPc_at procSeg.pre (ProcLabel.entry proc.name)
        (bodyCode program proc bodySupply ++
          [Assembly.Instr.label (ProcLabel.exit proc.name)] ++
          dispatchCode proc sites dispatchSupply ++ procSeg.post)
        (by
          simpa [procCode, procSegment, bodyCode, dispatchCode,
            List.append_assoc] using procSeg.hAsm)
    simpa using hHere
  have hEntryPcCall :
      Assembly.Program.labelPc
        (callSeg.pre ++ jumpCode ++ returnCode ++ callSeg.post)
        (ProcLabel.entry proc.name) =
          some (Assembly.Program.byteLength procSeg.pre) := by
    rw [← hCallAsm]
    exact hEntryPcAsm
  have hExactProc :
      ExactLabels (procSeg.pre ++ procCode ++ procSeg.post) := by
    exact ExactLabels.cast_asm hProcAsm hExact
  have hCallEntry :=
    FrameStateRel.source_callEntry_after_prologue_and_jump_withGasOracle
      (source := state) (target := target) (tokens := tokens)
      (argc := proc.argc) (retc := proc.retc) (args := args)
      (callerStack := callerStack) (token := token)
      (entryLabel := ProcLabel.entry proc.name)
      (entryDest := Assembly.Program.byteLength procSeg.pre)
      (pre := callSeg.pre) (post := returnCode ++ callSeg.post)
      (oracle := oracle) (cursor := cursor)
      (by simpa [jumpCode, callJumpCode, List.append_assoc] using hFitsJump)
      (by simpa [CodeSegment.startPc] using hPc) hRel hSplit hArgBound
      (by
        simpa [callSiteCode, callJumpCode, jumpCode, returnCode,
          List.append_assoc]
          using hEntryPcCall)
  refine
    ARunResultWithGasOracle.bind_running
      (program := asm) (oracle := oracle) (cursor := cursor)
      (state := target)
      (middle := fun afterJump targetCursorAfterJump =>
        targetCursorAfterJump = cursor ∧
          Preservation.Frame.StateRel
            ((state.withEVM { state.evm with stack := args }).pushReturn
              callerStack proc.retc)
            afterJump (token :: tokens) ∧
          afterJump.pc = Assembly.Program.pcAfter procSeg.pre)
      ?_ ?_
  · exact
      ARunResultWithGasOracle.mono
        (by
          rw [hCallAsm]
          simpa [callJumpCode, jumpCode, returnCode, List.append_assoc]
            using hCallEntry)
        (by
          intro result targetCursorAfterJump hResult
          cases result with
          | halted halt =>
              cases hResult
          | running afterJump =>
              rcases hResult with
                ⟨hCursorAfterJump, hRelAfterJump, hPcAfterJump⟩
              exact ⟨hCursorAfterJump, hRelAfterJump, by
                simpa [Assembly.Program.pcAfter] using hPcAfterJump⟩)
  · intro afterJump targetCursorAfterJump hAfterJump
    rcases hAfterJump with
      ⟨hTargetCursorAfterJump, hRelAfterJump, hPcAfterJump⟩
    subst targetCursorAfterJump
    have hBodyHalt :=
      halt_body_from_entry_withGasOracle
        (program := program) (proc := proc) (bodySupply := bodySupply)
        (dispatchSupply := dispatchSupply) (sites := sites)
        (fuel := fuel) (state := state) (bodyState := bodyState)
        (kind := kind) (args := args) (callerStack := callerStack)
        (target := afterJump) (tokens := tokens) (token := token)
        (pre := procSeg.pre) (post := procSeg.post)
        (oracle := oracle) (cursor := cursor)
        (cursorAfterBody := cursorAfterBody)
        hBodyPres hBody (by simpa [procCode] using procSeg.hFits)
        hPcAfterJump hRelAfterJump hExactProc
    exact
      ARunResultWithGasOracle.mono
        (by
          rw [hProcAsm]
          simpa [procCode] using hBodyHalt)
        (by
          intro result targetCursorFinal hResult
          rcases hResult with ⟨hCursorFinal, hCompiled⟩
          cases result with
          | running afterBody =>
              cases hCompiled
          | halted halt =>
              exact ⟨hCursorFinal, by
                simpa [CompiledOutcomeRel, Outcome.halt] using hCompiled⟩)

theorem call_stmt_segments_withGasOracle {program : Program}
    {ctx : CompileContext}
    {name : Name} {proc : Proc} {supply : LabelSupply}
    {bodySupply dispatchSupply : LabelSupply}
    {sites : List CallSite} {site : CallSite} {fuel : Nat}
    {state : RunState} {outcome : Outcome}
    {target : EVMState} {tokens : List Word}
    {asm : Assembly.Program} {oracle : GasOracle}
    {cursor cursorFinal : Nat}
    (callSeg :
      CodeSegment asm (Stmt.compileFromCtxCore (.call name) ctx supply).code)
    (procSeg :
      CodeSegment asm
        (procSegment program proc bodySupply dispatchSupply sites))
    (hCtxProcs : ctx.procs = program.procs)
    (hLookupCtx : ProcList.lookup? name ctx.procs = some proc)
    (hBodyPres :
      ∀ {bodyFuel : Nat}, bodyFuel < fuel →
        ProcBodyPreservesAtSegmentWithGasOracle program proc bodySupply
          dispatchSupply sites bodyFuel procSeg.pre procSeg.post)
    (hSite :
      site =
        { procName := name
          token := Stmt.callToken supply
          returnLabel := LabelSupply.label supply 0 })
    (hSiteMem : site ∈ sites)
    (hNoDup : (sites.map CallSite.token).Nodup)
    (hArgc : proc.argc ≤ 16)
    (hRetc : proc.retc < 16)
    (hPc : target.pc = callSeg.startPc)
    (hRel : Preservation.Frame.StateRel state target tokens)
    (hExact : ExactLabels asm)
    (hEval :
      Stmt.EvalWithGasOracle program oracle fuel (.call name) cursor state
        outcome cursorFinal) :
    ARunResultWithGasOracle asm oracle cursor target
      (fun result targetCursorFinal =>
        targetCursorFinal = cursorFinal ∧
          CompiledOutcomeRel asm ctx callSeg.fallthroughPc outcome result
            tokens) := by
  subst site
  have hLookupProgram : ProcList.lookup? name program.procs = some proc := by
    simpa [hCtxProcs] using hLookupCtx
  cases hEval with
  | call_regular hLookupEval hSplit hBody hPop hAttach =>
      rename_i evalFuel evalProc args callerStack stack bodyState returned frame
      have hProcEq : proc = evalProc := by
        have hSome : (some proc : Option Proc) = some evalProc := by
          rw [← hLookupProgram, hLookupEval]
        cases hSome
        rfl
      subst evalProc
      have hArgsLen :
          args.length = proc.argc :=
        _root_.EvmCompiler.Structured.Preservation.Frame.StackFrameFacts.splitArgs?_args_length
          hSplit
      have hCodeEq :
          (Stmt.compileFromCtxCore (.call name) ctx supply).code =
            callSiteCode proc args (Stmt.callToken supply)
              (LabelSupply.label supply 0) :=
        compile_call_code_eq_callSiteCode
          (ctx := ctx) (supply := supply) (name := name)
          (proc := proc) (args := args) hLookupCtx hArgsLen
      let callSeg' :
          CodeSegment asm
            (callSiteCode proc args (Stmt.callToken supply)
              (LabelSupply.label supply 0)) :=
        CodeSegment.cast_code hCodeEq callSeg
      have hMemFilter :
          { procName := name
            token := Stmt.callToken supply
            returnLabel := LabelSupply.label supply 0 } ∈
            sites.filter (CallSite.forProc proc.name) :=
        callSite_mem_filter_for_lookup
          (procs := ctx.procs) (name := name) (proc := proc)
          (sites := sites)
          (site :=
            { procName := name
              token := Stmt.callToken supply
              returnLabel := LabelSupply.label supply 0 })
          hLookupCtx hSiteMem rfl
      have hNoDupFilter :
          ((sites.filter (CallSite.forProc proc.name)).map
              CallSite.token).Nodup :=
        _root_.EvmCompiler.Structured.Preservation.DispatchPreservation.nodup_tokens_filter
          (sites := sites) (p := CallSite.forProc proc.name) hNoDup
      have hArgBound : args.length ≤ 16 :=
        arg_bound_of_split (proc := proc) hSplit hArgc
      have hRun :=
        call_regular_segments_withGasOracle
          (program := program) (ctx := ctx) (proc := proc)
          (bodySupply := bodySupply) (dispatchSupply := dispatchSupply)
          (sites := sites)
          (site :=
            { procName := name
              token := Stmt.callToken supply
              returnLabel := LabelSupply.label supply 0 })
          (fuel := evalFuel) (state := state) (bodyState := bodyState)
          (returned := returned) (args := args)
          (callerStack := callerStack) (stack := stack)
          (frame := frame) (target := target) (tokens := tokens)
          (token := Stmt.callToken supply) (asm := asm)
          (oracle := oracle) (cursor := cursor)
          (cursorAfterBody := cursorFinal)
          callSeg' procSeg (hBodyPres (Nat.lt_succ_self evalFuel)) hSplit
          hBody hPop hAttach hMemFilter hNoDupFilter rfl hArgBound hRetc
          (by simpa [callSeg', CodeSegment.startPc] using hPc)
          hRel hExact
      exact
        ARunResultWithGasOracle.mono hRun
          (by
            intro result targetCursorFinal hResult
            simpa [callSeg', CodeSegment.fallthroughPc, hCodeEq]
              using hResult)
  | call_leave hLookupEval hSplit hBody hPop hAttach =>
      rename_i evalFuel evalProc args callerStack stack bodyState returned frame
      have hProcEq : proc = evalProc := by
        have hSome : (some proc : Option Proc) = some evalProc := by
          rw [← hLookupProgram, hLookupEval]
        cases hSome
        rfl
      subst evalProc
      have hArgsLen :
          args.length = proc.argc :=
        _root_.EvmCompiler.Structured.Preservation.Frame.StackFrameFacts.splitArgs?_args_length
          hSplit
      have hCodeEq :
          (Stmt.compileFromCtxCore (.call name) ctx supply).code =
            callSiteCode proc args (Stmt.callToken supply)
              (LabelSupply.label supply 0) :=
        compile_call_code_eq_callSiteCode
          (ctx := ctx) (supply := supply) (name := name)
          (proc := proc) (args := args) hLookupCtx hArgsLen
      let callSeg' :
          CodeSegment asm
            (callSiteCode proc args (Stmt.callToken supply)
              (LabelSupply.label supply 0)) :=
        CodeSegment.cast_code hCodeEq callSeg
      have hMemFilter :
          { procName := name
            token := Stmt.callToken supply
            returnLabel := LabelSupply.label supply 0 } ∈
            sites.filter (CallSite.forProc proc.name) :=
        callSite_mem_filter_for_lookup
          (procs := ctx.procs) (name := name) (proc := proc)
          (sites := sites)
          (site :=
            { procName := name
              token := Stmt.callToken supply
              returnLabel := LabelSupply.label supply 0 })
          hLookupCtx hSiteMem rfl
      have hNoDupFilter :
          ((sites.filter (CallSite.forProc proc.name)).map
              CallSite.token).Nodup :=
        _root_.EvmCompiler.Structured.Preservation.DispatchPreservation.nodup_tokens_filter
          (sites := sites) (p := CallSite.forProc proc.name) hNoDup
      have hArgBound : args.length ≤ 16 :=
        arg_bound_of_split (proc := proc) hSplit hArgc
      have hRun :=
        call_leave_segments_withGasOracle
          (program := program) (ctx := ctx) (proc := proc)
          (bodySupply := bodySupply) (dispatchSupply := dispatchSupply)
          (sites := sites)
          (site :=
            { procName := name
              token := Stmt.callToken supply
              returnLabel := LabelSupply.label supply 0 })
          (fuel := evalFuel) (state := state) (bodyState := bodyState)
          (returned := returned) (args := args)
          (callerStack := callerStack) (stack := stack)
          (frame := frame) (target := target) (tokens := tokens)
          (token := Stmt.callToken supply) (asm := asm)
          (oracle := oracle) (cursor := cursor)
          (cursorAfterBody := cursorFinal)
          callSeg' procSeg (hBodyPres (Nat.lt_succ_self evalFuel)) hSplit
          hBody hPop hAttach hMemFilter hNoDupFilter rfl hArgBound hRetc
          (by simpa [callSeg', CodeSegment.startPc] using hPc)
          hRel hExact
      exact
        ARunResultWithGasOracle.mono hRun
          (by
            intro result targetCursorFinal hResult
            simpa [callSeg', CodeSegment.fallthroughPc, hCodeEq]
              using hResult)
  | call_halt hLookupEval hSplit hBody =>
      rename_i evalFuel evalProc args callerStack bodyState kind
      have hProcEq : proc = evalProc := by
        have hSome : (some proc : Option Proc) = some evalProc := by
          rw [← hLookupProgram, hLookupEval]
        cases hSome
        rfl
      subst evalProc
      have hArgsLen :
          args.length = proc.argc :=
        _root_.EvmCompiler.Structured.Preservation.Frame.StackFrameFacts.splitArgs?_args_length
          hSplit
      have hCodeEq :
          (Stmt.compileFromCtxCore (.call name) ctx supply).code =
            callSiteCode proc args (Stmt.callToken supply)
              (LabelSupply.label supply 0) :=
        compile_call_code_eq_callSiteCode
          (ctx := ctx) (supply := supply) (name := name)
          (proc := proc) (args := args) hLookupCtx hArgsLen
      let callSeg' :
          CodeSegment asm
            (callSiteCode proc args (Stmt.callToken supply)
              (LabelSupply.label supply 0)) :=
        CodeSegment.cast_code hCodeEq callSeg
      have hArgBound : args.length ≤ 16 :=
        arg_bound_of_split (proc := proc) hSplit hArgc
      have hRun :=
        call_halt_segments_withGasOracle
          (program := program) (ctx := ctx) (proc := proc)
          (bodySupply := bodySupply) (dispatchSupply := dispatchSupply)
          (sites := sites)
          (site :=
            { procName := name
              token := Stmt.callToken supply
              returnLabel := LabelSupply.label supply 0 })
          (fuel := evalFuel) (state := state) (bodyState := bodyState)
          (kind := kind) (args := args) (callerStack := callerStack)
          (target := target) (tokens := tokens)
          (token := Stmt.callToken supply) (asm := asm)
          (oracle := oracle) (cursor := cursor)
          (cursorAfterBody := cursorFinal)
          callSeg' procSeg (hBodyPres (Nat.lt_succ_self evalFuel)) hSplit
          hBody hArgBound
          (by simpa [callSeg', CodeSegment.startPc] using hPc)
          hRel hExact
      exact
        ARunResultWithGasOracle.mono hRun
          (by
            intro result targetCursorFinal hResult
            simpa [callSeg', CodeSegment.fallthroughPc, hCodeEq]
              using hResult)

theorem call_stmt_of_segments_withGasOracle {program : Program}
    {ctx : CompileContext}
    {name : Name} {proc : Proc} {supply : LabelSupply}
    {bodySupply dispatchSupply : LabelSupply}
    {sites : List CallSite} {site : CallSite} {fuel : Nat}
    {state : RunState} {outcome : Outcome}
    {target : EVMState} {tokens : List Word}
    {asm : Assembly.Program} {oracle : GasOracle}
    {cursor cursorFinal : Nat}
    (callSeg :
      CodeSegment asm (Stmt.compileFromCtxCore (.call name) ctx supply).code)
    (procSeg :
      CodeSegment asm
        (procSegment program proc bodySupply dispatchSupply sites))
    (hCtxProcs : ctx.procs = program.procs)
    (hLookupCtx : ProcList.lookup? name ctx.procs = some proc)
    (hBodyPres :
      BlockPreservesWithGasOracle program (bodyCtx program proc) bodySupply
        proc.body)
    (hSite :
      site =
        { procName := name
          token := Stmt.callToken supply
          returnLabel := LabelSupply.label supply 0 })
    (hSiteMem : site ∈ sites)
    (hNoDup : (sites.map CallSite.token).Nodup)
    (hArgc : proc.argc ≤ 16)
    (hRetc : proc.retc < 16)
    (hPc : target.pc = callSeg.startPc)
    (hRel : Preservation.Frame.StateRel state target tokens)
    (hExact : ExactLabels asm)
    (hEval :
      Stmt.EvalWithGasOracle program oracle fuel (.call name) cursor state
        outcome cursorFinal) :
    ARunResultWithGasOracle asm oracle cursor target
      (fun result targetCursorFinal =>
        targetCursorFinal = cursorFinal ∧
          CompiledOutcomeRel asm ctx callSeg.fallthroughPc outcome result
            tokens) := by
  exact
    call_stmt_segments_withGasOracle
      (program := program) (ctx := ctx) (name := name) (proc := proc)
      (supply := supply) (bodySupply := bodySupply)
      (dispatchSupply := dispatchSupply) (sites := sites) (site := site)
      (fuel := fuel) (state := state) (outcome := outcome)
      (target := target) (tokens := tokens) (asm := asm)
      (oracle := oracle) (cursor := cursor) (cursorFinal := cursorFinal)
      callSeg procSeg hCtxProcs hLookupCtx
      (fun {bodyFuel} _hLt =>
        procBodyPreservesAtSegment_of_local_withGasOracle
          (program := program) (proc := proc) (bodySupply := bodySupply)
          (dispatchSupply := dispatchSupply) (sites := sites)
          (fuel := bodyFuel) (pre := procSeg.pre) (post := procSeg.post)
          (blockPreservesWithGasOracleAtFuel_of_preserves hBodyPres)
          procSeg.hFits
          (ExactLabels.cast_asm procSeg.hAsm hExact))
      hSite hSiteMem hNoDup hArgc hRetc hPc hRel hExact hEval

end ProcedureCall

namespace ProcedureLayoutPreservation

abbrev CallsIncluded (sourceSites globalSites : List CallSite) : Prop :=
  _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.CallsIncluded
    sourceSites globalSites

private theorem procSegment_eq_procedurePreservation {program : Program}
    {proc : Proc} {bodySupply dispatchSupply : LabelSupply}
    {sites : List CallSite} :
    _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.procSegment
        program proc bodySupply dispatchSupply sites =
      ProcedureCall.procSegment program proc bodySupply dispatchSupply sites := by
  simp [ProcedureCall.procSegment,
    _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.procSegment,
    ProcedureCall.bodyCode,
    _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.bodyCode,
    ProcedureCall.bodyCtx,
    _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.bodyCtx,
    ProcedureCall.dispatchCode,
    _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.dispatchCode]

def StmtPreservesInProgramLayoutWithGasOracle {program : Program}
    (layout :
      _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.ProgramLayout
        program)
    (ctx : CompileContext) (supply : LabelSupply) (stmt : Stmt) : Prop :=
  ∀ {fuel : Nat} {source : RunState} {outcome : Outcome}
    {target : EVMState} {tokens : List Word}
    {oracle : GasOracle} {cursor cursorFinal : Nat},
    program.WF →
      ctx.procs = program.procs →
      CallsIncluded (Stmt.compileFromCtxCore stmt ctx supply).calls
        layout.sites →
      ContextLabelsResolve layout.asm ctx →
      (segment :
        CodeSegment layout.asm
          (Stmt.compileFromCtxCore stmt ctx supply).code) →
      target.pc = segment.startPc →
      Preservation.Frame.StateRel source target tokens →
      Stmt.EvalWithGasOracle program oracle fuel stmt cursor source outcome
        cursorFinal →
      ARunResultWithGasOracle layout.asm oracle cursor target
        (fun result targetCursorFinal =>
          targetCursorFinal = cursorFinal ∧
            CompiledOutcomeRel layout.asm ctx segment.fallthroughPc outcome
              result tokens)

def BlockPreservesInProgramLayoutWithGasOracle {program : Program}
    (layout :
      _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.ProgramLayout
        program)
    (ctx : CompileContext) (supply : LabelSupply) (block : Block) : Prop :=
  ∀ {fuel : Nat} {source : RunState} {outcome : Outcome}
    {target : EVMState} {tokens : List Word}
    {oracle : GasOracle} {cursor cursorFinal : Nat},
    program.WF →
      ctx.procs = program.procs →
      CallsIncluded (Block.compileFromCtx block ctx supply).calls
        layout.sites →
      ContextLabelsResolve layout.asm ctx →
      (segment :
        CodeSegment layout.asm (Block.compileFromCtx block ctx supply).code) →
      target.pc = segment.startPc →
      Preservation.Frame.StateRel source target tokens →
      Block.EvalWithGasOracle program oracle fuel block cursor source outcome
        cursorFinal →
      ARunResultWithGasOracle layout.asm oracle cursor target
        (fun result targetCursorFinal =>
          targetCursorFinal = cursorFinal ∧
            CompiledOutcomeRel layout.asm ctx segment.fallthroughPc outcome
              result tokens)

theorem call_stmt_of_programLayout_withGasOracle {program : Program}
    {ctx : CompileContext} {name : Name} {proc : Proc}
    {supply : LabelSupply}
    {fuel : Nat} {state : RunState} {outcome : Outcome}
    {target : EVMState} {tokens : List Word}
    {oracle : GasOracle} {cursor cursorFinal : Nat}
    (layout :
      _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.ProgramLayout
        program)
    (hProgramWF : program.WF)
    (hCalls :
      CallsIncluded (Stmt.compileFromCtxCore (.call name) ctx supply).calls
        layout.sites)
    (callSeg :
      CodeSegment layout.asm
        (Stmt.compileFromCtxCore (.call name) ctx supply).code)
    (hCtxProcs : ctx.procs = program.procs)
    (hLookupCtx : ProcList.lookup? name ctx.procs = some proc)
    (hProcPreserves :
      ∀ {name : Name} {proc : Proc}
        (hLookup : ProcList.lookup? name program.procs = some proc),
        BlockPreservesWithGasOracle program (ProcedureCall.bodyCtx program proc)
          (layout.procLayout hLookup).bodySupply proc.body)
    (hPc : target.pc = callSeg.startPc)
    (hRel : Preservation.Frame.StateRel state target tokens)
    (hEval :
      Stmt.EvalWithGasOracle program oracle fuel (.call name) cursor state
        outcome cursorFinal) :
    ARunResultWithGasOracle layout.asm oracle cursor target
      (fun result targetCursorFinal =>
        targetCursorFinal = cursorFinal ∧
          CompiledOutcomeRel layout.asm ctx callSeg.fallthroughPc outcome result
            tokens) := by
  have hLookupProgram : ProcList.lookup? name program.procs = some proc := by
    simpa [hCtxProcs] using hLookupCtx
  have hProcWF : Proc.WF proc :=
    Program.procWF_of_lookup? hProgramWF hLookupProgram
  let procLayout := layout.procLayout hLookupProgram
  have hBodyPresAt :
      BlockPreservesWithGasOracle program (ProcedureCall.bodyCtx program proc)
        procLayout.bodySupply proc.body := by
    change
      BlockPreservesWithGasOracle program (ProcedureCall.bodyCtx program proc)
        (layout.procLayout hLookupProgram).bodySupply proc.body
    exact hProcPreserves hLookupProgram
  let procSeg :
      CodeSegment layout.asm
        (ProcedureCall.procSegment program proc procLayout.bodySupply
          procLayout.dispatchSupply layout.sites) :=
    CodeSegment.cast_code
      (procSegment_eq_procedurePreservation
        (program := program) (proc := proc)
        (bodySupply := procLayout.bodySupply)
        (dispatchSupply := procLayout.dispatchSupply)
        (sites := layout.sites))
      procLayout.segment
  exact
    ProcedureCall.call_stmt_of_segments_withGasOracle
      (program := program) (ctx := ctx) (name := name) (proc := proc)
      (supply := supply) (bodySupply := procLayout.bodySupply)
      (dispatchSupply := procLayout.dispatchSupply) (sites := layout.sites)
      (site :=
        { procName := name
          token := Stmt.callToken supply
          returnLabel := LabelSupply.label supply 0 })
      (fuel := fuel) (state := state) (outcome := outcome)
      (target := target) (tokens := tokens) (asm := layout.asm)
      (oracle := oracle) (cursor := cursor) (cursorFinal := cursorFinal)
      callSeg procSeg hCtxProcs hLookupCtx
      hBodyPresAt
      rfl
      (_root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.generated_callSite_mem_of_included
        (ctx := ctx) (supply := supply) (name := name) (proc := proc)
        (sites := layout.sites) hLookupCtx hCalls)
      layout.noDupTokens hProcWF.1 hProcWF.2.1 hPc hRel
      layout.exactLabels hEval

theorem call_stmt_of_programLayout_eval_withGasOracle {program : Program}
    {ctx : CompileContext} {name : Name} {supply : LabelSupply}
    {fuel : Nat} {state : RunState} {outcome : Outcome}
    {target : EVMState} {tokens : List Word}
    {oracle : GasOracle} {cursor cursorFinal : Nat}
    (layout :
      _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.ProgramLayout
        program)
    (hProgramWF : program.WF)
    (hCtxProcs : ctx.procs = program.procs)
    (hCalls :
      CallsIncluded (Stmt.compileFromCtxCore (.call name) ctx supply).calls
        layout.sites)
    (callSeg :
      CodeSegment layout.asm
        (Stmt.compileFromCtxCore (.call name) ctx supply).code)
    (hPc : target.pc = callSeg.startPc)
    (hRel : Preservation.Frame.StateRel state target tokens)
    (hProcPreserves :
      ∀ {name : Name} {proc : Proc}
        (hLookup : ProcList.lookup? name program.procs = some proc),
        BlockPreservesWithGasOracle program (ProcedureCall.bodyCtx program proc)
          (layout.procLayout hLookup).bodySupply proc.body)
    (hEval :
      Stmt.EvalWithGasOracle program oracle fuel (.call name) cursor state
        outcome cursorFinal) :
    ARunResultWithGasOracle layout.asm oracle cursor target
      (fun result targetCursorFinal =>
        targetCursorFinal = cursorFinal ∧
          CompiledOutcomeRel layout.asm ctx callSeg.fallthroughPc outcome result
            tokens) := by
  cases hEval with
  | call_regular hLookup hSplit hBody hPop hAttach =>
      rename_i evalFuel evalProc args callerStack stack bodyState returned frame
      have hLookupCtx : ProcList.lookup? name ctx.procs = some evalProc := by
        simpa [hCtxProcs] using hLookup
      exact
        call_stmt_of_programLayout_withGasOracle
          (program := program) (ctx := ctx) (name := name)
          (proc := evalProc) (supply := supply) (fuel := evalFuel + 1)
          (state := state)
          (outcome :=
            Outcome.regular
              (returned.withEVM { bodyState.evm with stack := stack }))
          (target := target) (tokens := tokens) (oracle := oracle)
          (cursor := cursor) (cursorFinal := cursorFinal)
          layout hProgramWF hCalls callSeg hCtxProcs hLookupCtx
          hProcPreserves hPc hRel
          (Stmt.EvalWithGasOracle.call_regular hLookup hSplit hBody hPop
            hAttach)
  | call_leave hLookup hSplit hBody hPop hAttach =>
      rename_i evalFuel evalProc args callerStack stack bodyState returned frame
      have hLookupCtx : ProcList.lookup? name ctx.procs = some evalProc := by
        simpa [hCtxProcs] using hLookup
      exact
        call_stmt_of_programLayout_withGasOracle
          (program := program) (ctx := ctx) (name := name)
          (proc := evalProc) (supply := supply) (fuel := evalFuel + 1)
          (state := state)
          (outcome :=
            Outcome.regular
              (returned.withEVM { bodyState.evm with stack := stack }))
          (target := target) (tokens := tokens) (oracle := oracle)
          (cursor := cursor) (cursorFinal := cursorFinal)
          layout hProgramWF hCalls callSeg hCtxProcs hLookupCtx
          hProcPreserves hPc hRel
          (Stmt.EvalWithGasOracle.call_leave hLookup hSplit hBody hPop
            hAttach)
  | call_halt hLookup hSplit hBody =>
      rename_i evalFuel evalProc args callerStack bodyState kind
      have hLookupCtx : ProcList.lookup? name ctx.procs = some evalProc := by
        simpa [hCtxProcs] using hLookup
      exact
        call_stmt_of_programLayout_withGasOracle
          (program := program) (ctx := ctx) (name := name)
          (proc := evalProc) (supply := supply) (fuel := evalFuel + 1)
          (state := state) (outcome := Outcome.halt kind bodyState)
          (target := target) (tokens := tokens) (oracle := oracle)
          (cursor := cursor) (cursorFinal := cursorFinal)
          layout hProgramWF hCalls callSeg hCtxProcs hLookupCtx
          hProcPreserves hPc hRel
          (Stmt.EvalWithGasOracle.call_halt hLookup hSplit hBody)

theorem preserves_call_in_programLayout_withGasOracle {program : Program}
    (layout :
      _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.ProgramLayout
        program)
    (hProcPreserves :
      ∀ {name : Name} {proc : Proc}
        (hLookup : ProcList.lookup? name program.procs = some proc),
        BlockPreservesWithGasOracle program (ProcedureCall.bodyCtx program proc)
          (layout.procLayout hLookup).bodySupply proc.body)
    {ctx : CompileContext} {supply : LabelSupply} {name : Name} :
    StmtPreservesInProgramLayoutWithGasOracle layout ctx supply
      (.call name) := by
  intro fuel source outcome target tokens oracle cursor cursorFinal hProgramWF
    hCtxProcs hCalls _hResolve segment hPc hRel hEval
  exact
    call_stmt_of_programLayout_eval_withGasOracle
      (program := program) (ctx := ctx) (name := name) (supply := supply)
      (fuel := fuel) (state := source) (outcome := outcome)
      (target := target) (tokens := tokens) (oracle := oracle)
      (cursor := cursor) (cursorFinal := cursorFinal)
      layout hProgramWF hCtxProcs hCalls segment hPc hRel hProcPreserves
      hEval

theorem stmt_preserves_in_programLayout_of_local_withGasOracle
    {program : Program}
    {layout :
      _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.ProgramLayout
        program}
    {ctx : CompileContext} {supply : LabelSupply} {stmt : Stmt}
    (hLocal : StmtPreservesWithGasOracle program ctx supply stmt) :
    StmtPreservesInProgramLayoutWithGasOracle layout ctx supply stmt := by
  intro fuel source outcome target tokens oracle cursor cursorFinal _hProgramWF
    _hCtxProcs _hCalls hResolve segment hPc hRel hEval
  have hResolveSeg :
      ContextLabelsResolve
        (segment.pre ++ (Stmt.compileFromCtxCore stmt ctx supply).code ++
          segment.post) ctx :=
    ContextLabelsResolve.cast_asm segment.hAsm hResolve
  have hExactSeg :
      ExactLabels
        (segment.pre ++ (Stmt.compileFromCtxCore stmt ctx supply).code ++
          segment.post) :=
    ExactLabels.cast_asm segment.hAsm layout.exactLabels
  have hRun :=
    hLocal (pre := segment.pre) (post := segment.post) (fuel := fuel)
      (source := source) (outcome := outcome) (target := target)
      (tokens := tokens) (oracle := oracle) (cursor := cursor)
      (cursorFinal := cursorFinal)
      segment.hFits hResolveSeg hExactSeg
      (by simpa [CodeSegment.startPc] using hPc) hRel hEval
  exact
    ARunResultWithGasOracle.cast_program_mono segment.hAsm.symm hRun
      (by
        intro result targetCursorFinal hResult
        simpa [segment.hAsm, CodeSegment.fallthroughPc] using hResult)

theorem block_preserves_in_programLayout_of_local_withGasOracle
    {program : Program}
    {layout :
      _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.ProgramLayout
        program}
    {ctx : CompileContext} {supply : LabelSupply} {block : Block}
    (hLocal : BlockPreservesWithGasOracle program ctx supply block) :
    BlockPreservesInProgramLayoutWithGasOracle layout ctx supply block := by
  intro fuel source outcome target tokens oracle cursor cursorFinal _hProgramWF
    _hCtxProcs _hCalls hResolve segment hPc hRel hEval
  have hResolveSeg :
      ContextLabelsResolve
        (segment.pre ++ (Block.compileFromCtx block ctx supply).code ++
          segment.post) ctx :=
    ContextLabelsResolve.cast_asm segment.hAsm hResolve
  have hExactSeg :
      ExactLabels
        (segment.pre ++ (Block.compileFromCtx block ctx supply).code ++
          segment.post) :=
    ExactLabels.cast_asm segment.hAsm layout.exactLabels
  have hRun :=
    hLocal (pre := segment.pre) (post := segment.post) (fuel := fuel)
      (source := source) (outcome := outcome) (target := target)
      (tokens := tokens) (oracle := oracle) (cursor := cursor)
      (cursorFinal := cursorFinal)
      segment.hFits hResolveSeg hExactSeg
      (by simpa [CodeSegment.startPc] using hPc) hRel hEval
  exact
    ARunResultWithGasOracle.cast_program_mono segment.hAsm.symm hRun
      (by
        intro result targetCursorFinal hResult
        simpa [segment.hAsm, CodeSegment.fallthroughPc] using hResult)

theorem preserves_nil_in_programLayout_withGasOracle {program : Program}
    (layout :
      _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.ProgramLayout
        program)
    {ctx : CompileContext} {supply : LabelSupply} :
    BlockPreservesInProgramLayoutWithGasOracle layout ctx supply
      { stmts := [] } := by
  intro fuel source outcome target tokens oracle cursor cursorFinal _hProgramWF
    _hCtxProcs _hCalls _hResolve segment hPc hRel hEval
  cases hEval
  exact
    ARunResultWithGasOracle.pure
      (by
        exact
          ⟨ rfl
          , by
              simpa [Block.compileFromCtx, CompiledOutcomeRel,
                CodeSegment.startPc, CodeSegment.fallthroughPc,
                Outcome.regular] using And.intro hRel hPc
          ⟩)

theorem preserves_cons_in_programLayout_withGasOracle {program : Program}
    {layout :
      _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.ProgramLayout
        program}
    {ctx : CompileContext} {supply : LabelSupply}
    {stmt : Stmt} {rest : List Stmt}
    (hStmt :
      StmtPreservesInProgramLayoutWithGasOracle layout ctx supply stmt)
    (hRest :
      BlockPreservesInProgramLayoutWithGasOracle layout ctx
        (Stmt.compileFromCtxCore stmt ctx supply).next { stmts := rest }) :
    BlockPreservesInProgramLayoutWithGasOracle layout ctx supply
      { stmts := stmt :: rest } := by
  intro fuel source outcome target tokens oracle cursor cursorFinal hProgramWF
    hCtxProcs hCalls hResolve segment hPc hRel hEval
  let compiledStmt := Stmt.compileFromCtxCore stmt ctx supply
  let compiledRest :=
    Block.compileFromCtx { stmts := rest } ctx compiledStmt.next
  have hCodeEq :
      (Block.compileFromCtx { stmts := stmt :: rest } ctx supply).code =
        compiledStmt.code ++ compiledRest.code := by
    simp [Block.compileFromCtx, CompileResult.append,
      compiledStmt, compiledRest]
  have hCallsEq :
      (Block.compileFromCtx { stmts := stmt :: rest } ctx supply).calls =
        compiledStmt.calls ++ compiledRest.calls := by
    simp [Block.compileFromCtx, CompileResult.append,
      compiledStmt, compiledRest]
  let appendSeg :
      CodeSegment layout.asm (compiledStmt.code ++ compiledRest.code) :=
    CodeSegment.cast_code hCodeEq segment
  let stmtSeg : CodeSegment layout.asm compiledStmt.code :=
    CodeSegment.left appendSeg
  let restSeg : CodeSegment layout.asm compiledRest.code :=
    CodeSegment.right appendSeg
  have hCallsAppend :
      CallsIncluded (compiledStmt.calls ++ compiledRest.calls) layout.sites := by
    simpa [hCallsEq] using hCalls
  have hStmtCalls : CallsIncluded compiledStmt.calls layout.sites :=
    _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.CallsIncluded.left
      hCallsAppend
  have hRestCalls : CallsIncluded compiledRest.calls layout.sites :=
    _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.CallsIncluded.right
      hCallsAppend
  have hStmtPc : target.pc = stmtSeg.startPc := by
    simpa [stmtSeg, appendSeg, CodeSegment.startPc, CodeSegment.left,
      CodeSegment.cast_code] using hPc
  have hRestFallthrough :
      restSeg.fallthroughPc = segment.fallthroughPc := by
    simp [restSeg, appendSeg, CodeSegment.fallthroughPc, CodeSegment.right,
      CodeSegment.cast_code, hCodeEq, List.append_assoc]
  cases hEval with
  | cons_regular hStmtEval hRestEval =>
      rename_i innerFuel cursorMid mid
      have hStmtRun :=
        hStmt (fuel := innerFuel) (source := source)
          (outcome := Outcome.regular mid) (target := target)
          (tokens := tokens) (oracle := oracle) (cursor := cursor)
          (cursorFinal := cursorMid) hProgramWF hCtxProcs
          (by simpa [compiledStmt] using hStmtCalls)
          hResolve (by simpa [compiledStmt] using stmtSeg)
          hStmtPc hRel hStmtEval
      have hStmtRunRegular :
          ARunResultWithGasOracle layout.asm oracle cursor target
            (fun result targetCursorMid =>
              match result with
              | .running targetMid =>
                  targetCursorMid = cursorMid ∧
                    Preservation.Frame.StateRel mid targetMid tokens ∧
                    targetMid.pc = restSeg.startPc
              | .halted _ => False) := by
        exact
          ARunResultWithGasOracle.mono hStmtRun
            (by
              intro result targetCursorMid hResult
              rcases hResult with ⟨hCursorMid, hCompiled⟩
              cases result with
              | halted halt =>
                  cases hCompiled
              | running targetMid =>
                  exact ⟨hCursorMid, by
                    simpa [stmtSeg, restSeg, appendSeg,
                      CodeSegment.startPc, CodeSegment.fallthroughPc,
                      CodeSegment.left, CodeSegment.right,
                      CodeSegment.cast_code, CompiledOutcomeRel,
                      Outcome.regular, List.append_assoc] using hCompiled⟩)
      refine
        ARunResultWithGasOracle.bind_running
          (program := layout.asm) (oracle := oracle) (cursor := cursor)
          (state := target)
          (middle := fun targetMid targetCursorMid =>
            targetCursorMid = cursorMid ∧
              Preservation.Frame.StateRel mid targetMid tokens ∧
              targetMid.pc = restSeg.startPc)
          hStmtRunRegular ?_
      intro targetMid targetCursorMid hMid
      rcases hMid with ⟨hTargetCursorMid, hRelMid, hPcMid⟩
      subst targetCursorMid
      have hRestRun :=
        hRest (fuel := innerFuel) (source := mid) (outcome := outcome)
          (target := targetMid) (tokens := tokens) (oracle := oracle)
          (cursor := cursorMid) (cursorFinal := cursorFinal)
          hProgramWF hCtxProcs
          (by simpa [compiledRest] using hRestCalls)
          hResolve (by simpa [compiledRest] using restSeg)
          hPcMid hRelMid hRestEval
      exact
        ARunResultWithGasOracle.mono hRestRun
          (by
            intro result targetCursorFinal hResult
            simpa [hRestFallthrough] using hResult)
  | cons_brk hStmtEval =>
      rename_i innerFuel outState
      have hStmtRun :=
        hStmt (fuel := innerFuel) (source := source)
          (outcome := Outcome.brk outState) (target := target)
          (tokens := tokens) (oracle := oracle) (cursor := cursor)
          (cursorFinal := cursorFinal) hProgramWF hCtxProcs
          (by simpa [compiledStmt] using hStmtCalls)
          hResolve (by simpa [compiledStmt] using stmtSeg)
          hStmtPc hRel hStmtEval
      exact
        ARunResultWithGasOracle.mono hStmtRun
          (by
            intro result targetCursorFinal hResult
            rcases hResult with ⟨hCursorFinal, hCompiled⟩
            cases result with
            | running target' =>
                exact ⟨hCursorFinal, by
                  simpa [CompiledOutcomeRel, Outcome.brk] using hCompiled⟩
            | halted halt =>
                cases hCompiled)
  | cons_cont hStmtEval =>
      rename_i innerFuel outState
      have hStmtRun :=
        hStmt (fuel := innerFuel) (source := source)
          (outcome := Outcome.cont outState) (target := target)
          (tokens := tokens) (oracle := oracle) (cursor := cursor)
          (cursorFinal := cursorFinal) hProgramWF hCtxProcs
          (by simpa [compiledStmt] using hStmtCalls)
          hResolve (by simpa [compiledStmt] using stmtSeg)
          hStmtPc hRel hStmtEval
      exact
        ARunResultWithGasOracle.mono hStmtRun
          (by
            intro result targetCursorFinal hResult
            rcases hResult with ⟨hCursorFinal, hCompiled⟩
            cases result with
            | running target' =>
                exact ⟨hCursorFinal, by
                  simpa [CompiledOutcomeRel, Outcome.cont] using hCompiled⟩
            | halted halt =>
                cases hCompiled)
  | cons_leave hStmtEval =>
      rename_i innerFuel outState
      have hStmtRun :=
        hStmt (fuel := innerFuel) (source := source)
          (outcome := Outcome.leave outState) (target := target)
          (tokens := tokens) (oracle := oracle) (cursor := cursor)
          (cursorFinal := cursorFinal) hProgramWF hCtxProcs
          (by simpa [compiledStmt] using hStmtCalls)
          hResolve (by simpa [compiledStmt] using stmtSeg)
          hStmtPc hRel hStmtEval
      exact
        ARunResultWithGasOracle.mono hStmtRun
          (by
            intro result targetCursorFinal hResult
            rcases hResult with ⟨hCursorFinal, hCompiled⟩
            cases result with
            | running target' =>
                exact ⟨hCursorFinal, by
                  simpa [CompiledOutcomeRel, Outcome.leave] using hCompiled⟩
            | halted halt =>
                cases hCompiled)
  | cons_halt hStmtEval =>
      rename_i innerFuel outState kind
      have hStmtRun :=
        hStmt (fuel := innerFuel) (source := source)
          (outcome := Outcome.halt kind outState) (target := target)
          (tokens := tokens) (oracle := oracle) (cursor := cursor)
          (cursorFinal := cursorFinal) hProgramWF hCtxProcs
          (by simpa [compiledStmt] using hStmtCalls)
          hResolve (by simpa [compiledStmt] using stmtSeg)
          hStmtPc hRel hStmtEval
      exact
        ARunResultWithGasOracle.mono hStmtRun
          (by
            intro result targetCursorFinal hResult
            rcases hResult with ⟨hCursorFinal, hCompiled⟩
            cases result with
            | running target' =>
                cases hCompiled
            | halted halt =>
                exact ⟨hCursorFinal, by
                  simpa [CompiledOutcomeRel, Outcome.halt] using hCompiled⟩)

def BlockPreservesInProgramLayoutWithGasOracleAtFuel {program : Program}
    (layout :
      _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.ProgramLayout
        program)
    (fuel : Nat)
    (ctx : CompileContext) (supply : LabelSupply) (block : Block) : Prop :=
  ∀ {source : RunState} {outcome : Outcome}
    {target : EVMState} {tokens : List Word}
    {oracle : GasOracle} {cursor cursorFinal : Nat},
    program.WF →
      ctx.procs = program.procs →
      CallsIncluded (Block.compileFromCtx block ctx supply).calls
        layout.sites →
      ContextLabelsResolve layout.asm ctx →
      (segment :
        CodeSegment layout.asm (Block.compileFromCtx block ctx supply).code) →
      target.pc = segment.startPc →
      Preservation.Frame.StateRel source target tokens →
      Block.EvalWithGasOracle program oracle fuel block cursor source outcome
        cursorFinal →
      ARunResultWithGasOracle layout.asm oracle cursor target
        (fun result targetCursorFinal =>
          targetCursorFinal = cursorFinal ∧
            CompiledOutcomeRel layout.asm ctx segment.fallthroughPc outcome
              result tokens)

theorem procBodyPreservesAtSegment_of_programLayout_withGasOracle
    {program : Program}
    {layout :
      _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.ProgramLayout
        program}
    {proc : Proc} {bodySupply dispatchSupply : LabelSupply} {fuel : Nat}
    (procSeg :
      CodeSegment layout.asm
        (ProcedureCall.procSegment program proc bodySupply dispatchSupply
          layout.sites))
    (hBodyPres :
      BlockPreservesInProgramLayoutWithGasOracleAtFuel layout fuel
        (ProcedureCall.bodyCtx program proc) bodySupply proc.body)
    (hProgramWF : program.WF)
    (hBodyCalls :
      CallsIncluded
        (Block.compileFromCtx proc.body (ProcedureCall.bodyCtx program proc)
          bodySupply).calls
        layout.sites) :
    ProcedureCall.ProcBodyPreservesAtSegmentWithGasOracle program proc
      bodySupply dispatchSupply layout.sites fuel procSeg.pre
      procSeg.post := by
  intro source outcome target tokens oracle cursor cursorFinal hPc hRel hEval
  let ctx := ProcedureCall.bodyCtx program proc
  let bcode := ProcedureCall.bodyCode program proc bodySupply
  let dcode := ProcedureCall.dispatchCode proc layout.sites dispatchSupply
  let exitLabel := ProcLabel.exit proc.name
  have hFitsAfterEntry :
      AssemblyProgram.PCFitsFrom
        (procSeg.pre ++ [Assembly.Instr.label (ProcLabel.entry proc.name)])
        (bcode ++ ([Assembly.Instr.label exitLabel] ++ dcode)) := by
    exact
      AssemblyProgram.PCFitsFrom.right
        (pre := procSeg.pre)
        (first := [Assembly.Instr.label (ProcLabel.entry proc.name)])
        (second := bcode ++ ([Assembly.Instr.label exitLabel] ++ dcode))
        (by
          simpa [ProcedureCall.procSegment, bcode, dcode,
            ProcedureCall.bodyCode, ProcedureCall.dispatchCode, exitLabel,
            List.append_assoc] using procSeg.hFits)
  have hFitsBody :
      AssemblyProgram.PCFitsFrom
        (procSeg.pre ++ [Assembly.Instr.label (ProcLabel.entry proc.name)])
        bcode := by
    exact
      AssemblyProgram.PCFitsFrom.left
        (pre := procSeg.pre ++
          [Assembly.Instr.label (ProcLabel.entry proc.name)])
        (first := bcode)
        (second := [Assembly.Instr.label exitLabel] ++ dcode)
        hFitsAfterEntry
  have hExitPc :
      Assembly.Program.labelPc layout.asm exitLabel =
        some
          (Assembly.Program.byteLength
            ((procSeg.pre ++
              [Assembly.Instr.label (ProcLabel.entry proc.name)]) ++
                bcode)) := by
    have hHere :=
      layout.exactLabels.labelPc_at
        ((procSeg.pre ++ [Assembly.Instr.label (ProcLabel.entry proc.name)]) ++
          bcode)
        exitLabel
        (dcode ++ procSeg.post)
        (by
          simpa [ProcedureCall.procSegment, bcode, dcode,
            ProcedureCall.bodyCode, ProcedureCall.dispatchCode, exitLabel,
            List.append_assoc] using procSeg.hAsm)
    simpa [bcode, dcode, exitLabel] using hHere
  have hResolveBody : ContextLabelsResolve layout.asm ctx := by
    refine ⟨?_, ?_, ?_⟩
    · intro label h
      simp [ctx, ProcedureCall.bodyCtx] at h
    · intro label h
      simp [ctx, ProcedureCall.bodyCtx] at h
    · intro label h
      simp [ctx, ProcedureCall.bodyCtx] at h
      cases h
      refine
        ⟨ Assembly.Program.byteLength
            ((procSeg.pre ++
              [Assembly.Instr.label (ProcLabel.entry proc.name)]) ++ bcode)
        , ?_ ⟩
      simpa [exitLabel] using hExitPc
  let bodySeg : CodeSegment layout.asm bcode :=
    { pre := procSeg.pre ++ [Assembly.Instr.label (ProcLabel.entry proc.name)]
      post := [Assembly.Instr.label exitLabel] ++ dcode ++ procSeg.post
      hAsm := by
        simpa [ProcedureCall.procSegment, bcode, dcode,
          ProcedureCall.bodyCode, ProcedureCall.dispatchCode, exitLabel,
          List.append_assoc] using procSeg.hAsm
      hFits := by
        simpa [ProcedureCall.bodyCode, ctx, bcode] using hFitsBody }
  have hRun :=
    hBodyPres (source := source) (outcome := outcome)
      (target := target) (tokens := tokens) (oracle := oracle)
      (cursor := cursor) (cursorFinal := cursorFinal)
      hProgramWF (by simp [ProcedureCall.bodyCtx])
      (by simpa [ctx, bcode, ProcedureCall.bodyCode] using hBodyCalls)
      hResolveBody bodySeg
      (by simpa [bodySeg, CodeSegment.startPc] using hPc)
      hRel hEval
  exact
    ARunResultWithGasOracle.cast_program_mono procSeg.hAsm hRun
      (by
        intro result targetCursorFinal hResult
        rcases hResult with ⟨hCursorFinal, hCompiled⟩
        refine ⟨hCursorFinal, ?_⟩
        have hExitPcSegment :
            Assembly.Program.labelPc
              (procSeg.pre ++
                ProcedureCall.procSegment program proc bodySupply
                  dispatchSupply layout.sites ++ procSeg.post)
              exitLabel =
                some
                  (Assembly.Program.byteLength
                    ((procSeg.pre ++
                      [Assembly.Instr.label
                        (ProcLabel.entry proc.name)]) ++ bcode)) := by
          have hLabelEq :
              Assembly.Program.labelPc
                (procSeg.pre ++
                  ProcedureCall.procSegment program proc bodySupply
                    dispatchSupply layout.sites ++ procSeg.post)
                exitLabel =
                  Assembly.Program.labelPc layout.asm exitLabel :=
            congrArg (fun asm => Assembly.Program.labelPc asm exitLabel)
              procSeg.hAsm.symm
          rw [hLabelEq]
          exact hExitPc
        cases outcome with
        | mk outState mode =>
            cases mode with
            | regular =>
                cases result with
                | running targetState =>
                    simpa [CompiledOutcomeRel, bodySeg,
                      CodeSegment.fallthroughPc, ProcedureCall.bodyCode,
                      bcode, List.append_assoc] using hCompiled
                | halted halt =>
                    simp [CompiledOutcomeRel] at hCompiled ⊢
            | brk =>
                cases result with
                | running targetState =>
                    simp [CompiledOutcomeRel, ProcedureCall.bodyCtx]
                      at hCompiled ⊢
                | halted halt =>
                    simp [CompiledOutcomeRel] at hCompiled ⊢
            | cont =>
                cases result with
                | running targetState =>
                    simp [CompiledOutcomeRel, ProcedureCall.bodyCtx]
                      at hCompiled ⊢
                | halted halt =>
                    simp [CompiledOutcomeRel] at hCompiled ⊢
            | leave =>
                cases result with
                | halted halt =>
                    simp [CompiledOutcomeRel] at hCompiled ⊢
                | running targetState =>
                    rcases hCompiled with
                      ⟨label, dest, hCtxLeave, hLabelPc, hRelResult,
                        hPcResult⟩
                    simp [ProcedureCall.bodyCtx] at hCtxLeave
                    subst label
                    have hDest :
                        dest =
                          Assembly.Program.byteLength
                            ((procSeg.pre ++
                              [Assembly.Instr.label
                                (ProcLabel.entry proc.name)]) ++ bcode) := by
                      rw [hExitPc] at hLabelPc
                      cases hLabelPc
                      rfl
                    subst dest
                    exact
                      ⟨exitLabel,
                        Assembly.Program.byteLength
                          ((procSeg.pre ++
                            [Assembly.Instr.label
                              (ProcLabel.entry proc.name)]) ++ bcode),
                        by simp [ProcedureCall.bodyCtx, exitLabel],
                        hExitPcSegment, hRelResult, hPcResult⟩
            | halt kind =>
                cases result with
                | running targetState =>
                    simp [CompiledOutcomeRel] at hCompiled ⊢
                | halted halt =>
                    exact hCompiled)

def StmtPreservesInProgramLayoutWithGasOracleUpTo {program : Program}
    (layout :
      _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.ProgramLayout
        program)
    (maxFuel : Nat)
    (ctx : CompileContext) (supply : LabelSupply) (stmt : Stmt) : Prop :=
  ∀ {fuel : Nat} {source : RunState} {outcome : Outcome}
    {target : EVMState} {tokens : List Word}
    {oracle : GasOracle} {cursor cursorFinal : Nat},
    fuel < maxFuel →
      program.WF →
      ctx.procs = program.procs →
      CallsIncluded (Stmt.compileFromCtxCore stmt ctx supply).calls
        layout.sites →
      ContextLabelsResolve layout.asm ctx →
      (segment :
        CodeSegment layout.asm
          (Stmt.compileFromCtxCore stmt ctx supply).code) →
      target.pc = segment.startPc →
      Preservation.Frame.StateRel source target tokens →
      Stmt.EvalWithGasOracle program oracle fuel stmt cursor source outcome
        cursorFinal →
      ARunResultWithGasOracle layout.asm oracle cursor target
        (fun result targetCursorFinal =>
          targetCursorFinal = cursorFinal ∧
            CompiledOutcomeRel layout.asm ctx segment.fallthroughPc outcome
              result tokens)

def BlockPreservesInProgramLayoutWithGasOracleUpTo {program : Program}
    (layout :
      _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.ProgramLayout
        program)
    (maxFuel : Nat)
    (ctx : CompileContext) (supply : LabelSupply) (block : Block) : Prop :=
  ∀ {fuel : Nat} {source : RunState} {outcome : Outcome}
    {target : EVMState} {tokens : List Word}
    {oracle : GasOracle} {cursor cursorFinal : Nat},
    fuel < maxFuel →
      program.WF →
      ctx.procs = program.procs →
      CallsIncluded (Block.compileFromCtx block ctx supply).calls
        layout.sites →
      ContextLabelsResolve layout.asm ctx →
      (segment :
        CodeSegment layout.asm (Block.compileFromCtx block ctx supply).code) →
      target.pc = segment.startPc →
      Preservation.Frame.StateRel source target tokens →
      Block.EvalWithGasOracle program oracle fuel block cursor source outcome
        cursorFinal →
      ARunResultWithGasOracle layout.asm oracle cursor target
        (fun result targetCursorFinal =>
          targetCursorFinal = cursorFinal ∧
            CompiledOutcomeRel layout.asm ctx segment.fallthroughPc outcome
              result tokens)

structure CallObligationUpToWithGasOracle {program : Program}
    (layout :
      _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.ProgramLayout
        program)
    (maxFuel : Nat) : Prop where
  preserves :
    ∀ {ctx : CompileContext} {supply : LabelSupply} {name : Name},
      StmtPreservesInProgramLayoutWithGasOracleUpTo layout maxFuel ctx supply
        (.call name)

def CallObligationForAllFuelWithGasOracle {program : Program}
    (layout :
      _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.ProgramLayout
        program) : Prop :=
  ∀ maxFuel, CallObligationUpToWithGasOracle layout maxFuel

theorem callObligationUpTo_zero_withGasOracle {program : Program}
    (layout :
      _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.ProgramLayout
        program) :
    CallObligationUpToWithGasOracle layout 0 := by
  constructor
  intro ctx supply name fuel source outcome target tokens oracle cursor
    cursorFinal hLt
  omega

theorem stmtPreservesInProgramLayoutWithGasOracleUpTo_mono
    {program : Program}
    {layout :
      _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.ProgramLayout
        program}
    {small big : Nat}
    {ctx : CompileContext} {supply : LabelSupply} {stmt : Stmt}
    (hLe : small ≤ big)
    (hPreserves :
      StmtPreservesInProgramLayoutWithGasOracleUpTo layout big ctx supply
        stmt) :
    StmtPreservesInProgramLayoutWithGasOracleUpTo layout small ctx supply
      stmt := by
  intro fuel source outcome target tokens oracle cursor cursorFinal hLt
  exact hPreserves (by omega)

theorem blockPreservesInProgramLayoutWithGasOracleUpTo_mono
    {program : Program}
    {layout :
      _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.ProgramLayout
        program}
    {small big : Nat}
    {ctx : CompileContext} {supply : LabelSupply} {block : Block}
    (hLe : small ≤ big)
    (hPreserves :
      BlockPreservesInProgramLayoutWithGasOracleUpTo layout big ctx supply
        block) :
    BlockPreservesInProgramLayoutWithGasOracleUpTo layout small ctx supply
      block := by
  intro fuel source outcome target tokens oracle cursor cursorFinal hLt
  exact hPreserves (by omega)

theorem blockPreservesInProgramLayoutWithGasOracleAtFuel_of_upTo
    {program : Program}
    {layout :
      _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.ProgramLayout
        program}
    {maxFuel fuel : Nat}
    {ctx : CompileContext} {supply : LabelSupply} {block : Block}
    (hLt : fuel < maxFuel)
    (hPreserves :
      BlockPreservesInProgramLayoutWithGasOracleUpTo layout maxFuel ctx supply
        block) :
    BlockPreservesInProgramLayoutWithGasOracleAtFuel layout fuel ctx supply
      block := by
  intro source outcome target tokens oracle cursor cursorFinal hProgramWF
    hCtxProcs hCalls hResolve segment hPc hRel hEval
  exact
    hPreserves (fuel := fuel) (source := source) (outcome := outcome)
      (target := target) (tokens := tokens) (oracle := oracle)
      (cursor := cursor) (cursorFinal := cursorFinal)
      hLt hProgramWF hCtxProcs hCalls hResolve segment hPc hRel hEval

theorem callObligationUpToWithGasOracle_mono {program : Program}
    {layout :
      _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.ProgramLayout
        program}
    {small big : Nat}
    (hLe : small ≤ big)
    (hCall : CallObligationUpToWithGasOracle layout big) :
    CallObligationUpToWithGasOracle layout small := by
  constructor
  intro ctx supply name
  exact
    stmtPreservesInProgramLayoutWithGasOracleUpTo_mono
      (layout := layout) (small := small) (big := big)
      (ctx := ctx) (supply := supply) (stmt := .call name) hLe
      hCall.preserves

theorem stmt_preserves_upTo_of_preserves_withGasOracle {program : Program}
    {layout :
      _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.ProgramLayout
        program}
    {maxFuel : Nat}
    {ctx : CompileContext} {supply : LabelSupply} {stmt : Stmt}
    (hPreserves :
      StmtPreservesInProgramLayoutWithGasOracle layout ctx supply stmt) :
    StmtPreservesInProgramLayoutWithGasOracleUpTo layout maxFuel ctx supply
      stmt := by
  intro fuel source outcome target tokens oracle cursor cursorFinal _hLt
    hProgramWF hCtxProcs hCalls hResolve segment hPc hRel hEval
  exact
    hPreserves hProgramWF hCtxProcs hCalls hResolve segment hPc hRel hEval

theorem block_preserves_upTo_of_preserves_withGasOracle {program : Program}
    {layout :
      _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.ProgramLayout
        program}
    {maxFuel : Nat}
    {ctx : CompileContext} {supply : LabelSupply} {block : Block}
    (hPreserves :
      BlockPreservesInProgramLayoutWithGasOracle layout ctx supply block) :
    BlockPreservesInProgramLayoutWithGasOracleUpTo layout maxFuel ctx supply
      block := by
  intro fuel source outcome target tokens oracle cursor cursorFinal _hLt
    hProgramWF hCtxProcs hCalls hResolve segment hPc hRel hEval
  exact
    hPreserves hProgramWF hCtxProcs hCalls hResolve segment hPc hRel hEval

set_option maxHeartbeats 800000 in
theorem preserves_if_in_programLayout_upTo_withGasOracle {program : Program}
    {layout :
      _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.ProgramLayout
        program}
    {maxFuel : Nat}
    {ctx : CompileContext} {supply : LabelSupply}
    {cond : Code} {body : Block}
    (hCondSafe : Code.RunnerSafeWithGasOracle cond)
    (hCondFrame : Code.FrameSafeWithGasOracle cond)
    (hBody :
      BlockPreservesInProgramLayoutWithGasOracleUpTo layout maxFuel ctx
        (LabelSupply.next supply) body) :
    StmtPreservesInProgramLayoutWithGasOracleUpTo layout maxFuel ctx supply
      (.if_ cond body) := by
  intro fuel source outcome target tokens oracle cursor cursorFinal hLt
    hProgramWF hCtxProcs hCalls hResolve segment hPc hRel hEval
  let pre := segment.pre
  let post := segment.post
  let bodyLabel := LabelSupply.label supply 0
  let endLabel := LabelSupply.label supply 1
  let compiledBody := Block.compileFromCtx body ctx (LabelSupply.next supply)
  let preAfterJumpi : Assembly.Program :=
    pre ++ cond.toAssembly ++ [Assembly.Instr.jumpi bodyLabel]
  let preBodyLabel : Assembly.Program :=
    pre ++ cond.toAssembly ++
      [Assembly.Instr.jumpi bodyLabel, Assembly.Instr.jump endLabel]
  let preBody : Assembly.Program :=
    pre ++ cond.toAssembly ++
      [ Assembly.Instr.jumpi bodyLabel
      , Assembly.Instr.jump endLabel
      , Assembly.Instr.label bodyLabel
      ]
  let preEndLabel : Assembly.Program :=
    pre ++ cond.toAssembly ++
      [ Assembly.Instr.jumpi bodyLabel
      , Assembly.Instr.jump endLabel
      , Assembly.Instr.label bodyLabel
      ] ++
      compiledBody.code
  have hLocalAsm :
      pre ++ (Stmt.compileFromCtxCore (.if_ cond body) ctx supply).code ++
        post =
        layout.asm := by
    simpa [pre, post] using segment.hAsm.symm
  have hFitsIf :
      AssemblyProgram.PCFitsFrom pre
        (cond.toAssembly ++
          [ Assembly.Instr.jumpi bodyLabel
          , Assembly.Instr.jump endLabel
          , Assembly.Instr.label bodyLabel
          ] ++
          compiledBody.code ++ [Assembly.Instr.label endLabel]) := by
    simpa [pre, Stmt.compileFromCtxCore, bodyLabel, endLabel, compiledBody]
      using segment.hFits
  have hCondAsmFits :
      AssemblyProgram.PCFitsFrom pre cond.toAssembly :=
    AssemblyProgram.PCFitsFrom.left (pre := pre)
      (first := cond.toAssembly)
      (second :=
        [ Assembly.Instr.jumpi bodyLabel
        , Assembly.Instr.jump endLabel
        , Assembly.Instr.label bodyLabel
        ] ++ compiledBody.code ++ [Assembly.Instr.label endLabel])
      (by simpa [List.append_assoc] using hFitsIf)
  have hCondFits : Code.PCFitsFrom pre cond :=
    Code.PCFitsFrom.of_assembly hCondAsmFits
  have hJumpEndFit : PCFits preAfterJumpi := by
    have hPrefix :
        AssemblyProgram.PCFitsFrom pre
          (cond.toAssembly ++ [Assembly.Instr.jumpi bodyLabel]) :=
      AssemblyProgram.PCFitsFrom.left (pre := pre)
        (first := cond.toAssembly ++ [Assembly.Instr.jumpi bodyLabel])
        (second :=
          [Assembly.Instr.jump endLabel, Assembly.Instr.label bodyLabel] ++
            compiledBody.code ++ [Assembly.Instr.label endLabel])
        (by simpa [List.append_assoc] using hFitsIf)
    simpa [preAfterJumpi, List.append_assoc] using
      AssemblyProgram.PCFitsFrom.end hPrefix
  have hBodyLabelFit : PCFits preBodyLabel := by
    have hPrefix :
        AssemblyProgram.PCFitsFrom pre
          (cond.toAssembly ++
            [Assembly.Instr.jumpi bodyLabel, Assembly.Instr.jump endLabel]) :=
      AssemblyProgram.PCFitsFrom.left (pre := pre)
        (first :=
          cond.toAssembly ++
            [Assembly.Instr.jumpi bodyLabel, Assembly.Instr.jump endLabel])
        (second :=
          [Assembly.Instr.label bodyLabel] ++ compiledBody.code ++
            [Assembly.Instr.label endLabel])
        (by simpa [List.append_assoc] using hFitsIf)
    simpa [preBodyLabel, List.append_assoc] using
      AssemblyProgram.PCFitsFrom.end hPrefix
  have hEndLabelFit : PCFits preEndLabel := by
    have hPrefix :
        AssemblyProgram.PCFitsFrom pre
          (cond.toAssembly ++
            [ Assembly.Instr.jumpi bodyLabel
            , Assembly.Instr.jump endLabel
            , Assembly.Instr.label bodyLabel
            ] ++ compiledBody.code) :=
      AssemblyProgram.PCFitsFrom.left (pre := pre)
        (first :=
          cond.toAssembly ++
            [ Assembly.Instr.jumpi bodyLabel
            , Assembly.Instr.jump endLabel
            , Assembly.Instr.label bodyLabel
            ] ++ compiledBody.code)
        (second := [Assembly.Instr.label endLabel])
        (by simpa [List.append_assoc] using hFitsIf)
    simpa [preEndLabel, List.append_assoc] using
      AssemblyProgram.PCFitsFrom.end hPrefix
  have hBodyFits :
      AssemblyProgram.PCFitsFrom preBody compiledBody.code := by
    have hAfterBodyLabel :
        AssemblyProgram.PCFitsFrom preBody
          (compiledBody.code ++ [Assembly.Instr.label endLabel]) := by
      simpa [preBody, List.append_assoc] using
        AssemblyProgram.PCFitsFrom.right (pre := pre)
          (first :=
            cond.toAssembly ++
              [ Assembly.Instr.jumpi bodyLabel
              , Assembly.Instr.jump endLabel
              , Assembly.Instr.label bodyLabel
              ])
          (second := compiledBody.code ++ [Assembly.Instr.label endLabel])
          (by simpa [List.append_assoc] using hFitsIf)
    exact
      AssemblyProgram.PCFitsFrom.left (pre := preBody)
        (first := compiledBody.code)
        (second := [Assembly.Instr.label endLabel]) hAfterBodyLabel
  have hExactIf :
      ExactLabels
        (pre ++ cond.toAssembly ++
          [ Assembly.Instr.jumpi bodyLabel
          , Assembly.Instr.jump endLabel
          , Assembly.Instr.label bodyLabel
          ] ++
          compiledBody.code ++ [Assembly.Instr.label endLabel] ++ post) := by
    have hExactLocal :
        ExactLabels
          (pre ++ (Stmt.compileFromCtxCore (.if_ cond body) ctx supply).code ++
            post) :=
      ExactLabels.cast_asm hLocalAsm.symm layout.exactLabels
    simpa [Stmt.compileFromCtxCore, bodyLabel, endLabel, compiledBody,
      List.append_assoc] using hExactLocal
  have hBodyLabel :
      Assembly.Program.labelPc
          (pre ++ cond.toAssembly ++
            [Assembly.Instr.jumpi bodyLabel] ++
            ([Assembly.Instr.jump endLabel, Assembly.Instr.label bodyLabel] ++
              compiledBody.code ++ [Assembly.Instr.label endLabel] ++ post))
          bodyLabel =
        some (Assembly.Program.byteLength preBodyLabel) := by
    have hHere :=
      hExactIf.labelPc_at preBodyLabel bodyLabel
        (compiledBody.code ++ [Assembly.Instr.label endLabel] ++ post)
        (by simp [preBodyLabel, List.append_assoc])
    simpa [preBodyLabel, List.append_assoc] using hHere
  have hEndLabel :
      Assembly.Program.labelPc
          (preAfterJumpi ++ [Assembly.Instr.jump endLabel] ++
            ([Assembly.Instr.label bodyLabel] ++ compiledBody.code) ++
            [Assembly.Instr.label endLabel] ++ post)
          endLabel =
        some (Assembly.Program.byteLength preEndLabel) := by
    have hHere :=
      hExactIf.labelPc_at preEndLabel endLabel post
        (by simp [preEndLabel, List.append_assoc])
    simpa [preAfterJumpi, preEndLabel, List.append_assoc] using hHere
  have hBodyCalls : CallsIncluded compiledBody.calls layout.sites := by
    simpa [Stmt.compileFromCtxCore, bodyLabel, endLabel, compiledBody]
      using hCalls
  let bodySeg : CodeSegment layout.asm compiledBody.code :=
    { pre := preBody
      post := [Assembly.Instr.label endLabel] ++ post
      hAsm := by
        simpa [Stmt.compileFromCtxCore, bodyLabel, endLabel, compiledBody,
          pre, post, preBody, List.append_assoc] using segment.hAsm
      hFits := hBodyFits }
  cases hEval with
  | if_false hCondRun =>
      rename_i stateAfterCond
      have hCondJump :=
        FrameStateRel.runCondition_jumpi_result_ctx_withGasOracle
          (cond := cond) (label := bodyLabel)
          (dest := Assembly.Program.byteLength preBodyLabel)
          (pre := pre)
          (post :=
            [Assembly.Instr.jump endLabel, Assembly.Instr.label bodyLabel] ++
              compiledBody.code ++ [Assembly.Instr.label endLabel] ++ post)
          (oracle := oracle) (cursor := cursor)
          hCondSafe hCondFrame hCondFits
          (by simpa [pre, CodeSegment.startPc] using hPc)
          hRel hBodyLabel hCondRun
      have hCondFalseLocal :
          ARunResultWithGasOracle
            (pre ++
              (Stmt.compileFromCtxCore (.if_ cond body) ctx supply).code ++
                post)
            oracle cursor target
            (fun result targetCursorAfterCond =>
              match result with
              | .running targetAfterCond =>
                  targetCursorAfterCond = cursorFinal ∧
                    Frame.StateRel stateAfterCond targetAfterCond tokens ∧
                      targetAfterCond.pc =
                        Assembly.Program.pcAfter preAfterJumpi
              | .halted _ => False) := by
        exact ARunResultWithGasOracle.mono
          (by
            simpa [Stmt.compileFromCtxCore, bodyLabel, endLabel, compiledBody,
              preAfterJumpi, List.append_assoc] using hCondJump)
          (by
            intro result targetCursorAfterCond hResult
            cases result with
            | halted halt =>
                cases hResult
            | running targetAfterCond =>
                simpa [preAfterJumpi] using hResult)
      have hCondFalse :
          ARunResultWithGasOracle layout.asm oracle cursor target
            (fun result targetCursorAfterCond =>
              match result with
              | .running targetAfterCond =>
                  targetCursorAfterCond = cursorFinal ∧
                    Frame.StateRel stateAfterCond targetAfterCond tokens ∧
                      targetAfterCond.pc =
                        Assembly.Program.pcAfter preAfterJumpi
              | .halted _ => False) :=
        ARunResultWithGasOracle.cast_program hLocalAsm hCondFalseLocal
      refine
        ARunResultWithGasOracle.bind_running
          (program := layout.asm) (oracle := oracle) (cursor := cursor)
          (state := target)
          (middle := fun targetAfterCond targetCursorAfterCond =>
            targetCursorAfterCond = cursorFinal ∧
              Frame.StateRel stateAfterCond targetAfterCond tokens ∧
                targetAfterCond.pc = Assembly.Program.pcAfter preAfterJumpi)
          hCondFalse ?_
      intro targetAfterCond targetCursorAfterCond hAfterCond
      rcases hAfterCond with
        ⟨hTargetCursorAfterCond, hRelAfterCond, hPcAfterCond⟩
      subst targetCursorAfterCond
      have hJumpEnd :=
        FrameStateRel.jump_then_label_runResult_at_withGasOracle
          (label := endLabel) (pre := preAfterJumpi)
          (between := [Assembly.Instr.label bodyLabel] ++ compiledBody.code)
          (post := post) (oracle := oracle) (cursor := cursorFinal)
          hJumpEndFit
          (by simpa [preAfterJumpi, preEndLabel, List.append_assoc]
            using hEndLabelFit)
          hPcAfterCond hRelAfterCond
          (by simpa [preAfterJumpi, preEndLabel, List.append_assoc]
            using hEndLabel)
      have hJumpEndLocal :
          ARunResultWithGasOracle
            (pre ++
              (Stmt.compileFromCtxCore (.if_ cond body) ctx supply).code ++
                post)
            oracle cursorFinal targetAfterCond
            (fun result targetCursorFinal =>
              targetCursorFinal = cursorFinal ∧
                CompiledOutcomeRel layout.asm ctx segment.fallthroughPc
                  (Outcome.regular stateAfterCond) result tokens) := by
        exact ARunResultWithGasOracle.mono
          (by
            simpa [Stmt.compileFromCtxCore, bodyLabel, endLabel, compiledBody,
              preAfterJumpi, preEndLabel, List.append_assoc] using hJumpEnd)
          (by
            intro result targetCursorFinal hResult
            cases result with
            | halted halt =>
                cases hResult
            | running targetFinal =>
                rcases hResult with ⟨hCursor, hTargetRel, hTargetPc⟩
                exact
                  ⟨ hCursor
                  , by
                      simpa [pre, post, Stmt.compileFromCtxCore, bodyLabel,
                        endLabel, compiledBody, preAfterJumpi, preEndLabel,
                        CompiledOutcomeRel, Outcome.regular,
                        CodeSegment.fallthroughPc, List.append_assoc]
                        using And.intro hTargetRel hTargetPc
                  ⟩)
      exact ARunResultWithGasOracle.cast_program hLocalAsm hJumpEndLocal
  | if_true hCondRun hBodyEval =>
      rename_i bodyFuel cursorAfterCond stateAfterCond
      have hBodyLt : bodyFuel < maxFuel := by omega
      have hCondJump :=
        FrameStateRel.runCondition_jumpi_result_ctx_withGasOracle
          (cond := cond) (label := bodyLabel)
          (dest := Assembly.Program.byteLength preBodyLabel)
          (pre := pre)
          (post :=
            [Assembly.Instr.jump endLabel, Assembly.Instr.label bodyLabel] ++
              compiledBody.code ++ [Assembly.Instr.label endLabel] ++ post)
          (oracle := oracle) (cursor := cursor)
          hCondSafe hCondFrame hCondFits
          (by simpa [pre, CodeSegment.startPc] using hPc)
          hRel hBodyLabel hCondRun
      have hCondTrueLocal :
          ARunResultWithGasOracle
            (pre ++
              (Stmt.compileFromCtxCore (.if_ cond body) ctx supply).code ++
                post)
            oracle cursor target
            (fun result targetCursorAfterCond =>
              match result with
              | .running targetAfterCond =>
                  targetCursorAfterCond = cursorAfterCond ∧
                    Frame.StateRel stateAfterCond targetAfterCond tokens ∧
                      targetAfterCond.pc =
                        Assembly.Program.pcAfter preBodyLabel
              | .halted _ => False) := by
        exact ARunResultWithGasOracle.mono
          (by
            simpa [Stmt.compileFromCtxCore, bodyLabel, endLabel, compiledBody,
              preBodyLabel, List.append_assoc] using hCondJump)
          (by
            intro result targetCursorAfterCond hResult
            cases result with
            | halted halt =>
                cases hResult
            | running targetAfterCond =>
                simpa [preBodyLabel] using hResult)
      have hCondTrue :
          ARunResultWithGasOracle layout.asm oracle cursor target
            (fun result targetCursorAfterCond =>
              match result with
              | .running targetAfterCond =>
                  targetCursorAfterCond = cursorAfterCond ∧
                    Frame.StateRel stateAfterCond targetAfterCond tokens ∧
                      targetAfterCond.pc =
                        Assembly.Program.pcAfter preBodyLabel
              | .halted _ => False) :=
        ARunResultWithGasOracle.cast_program hLocalAsm hCondTrueLocal
      refine
        ARunResultWithGasOracle.bind_running
          (program := layout.asm) (oracle := oracle) (cursor := cursor)
          (state := target)
          (middle := fun targetAfterCond targetCursorAfterCond =>
            targetCursorAfterCond = cursorAfterCond ∧
              Frame.StateRel stateAfterCond targetAfterCond tokens ∧
                targetAfterCond.pc = Assembly.Program.pcAfter preBodyLabel)
          hCondTrue ?_
      intro targetAfterCond targetCursorAfterCond hAfterCond
      rcases hAfterCond with
        ⟨hTargetCursorAfterCond, hRelAfterCond, hPcAfterCond⟩
      subst targetCursorAfterCond
      have hBodyLabelRun :=
        FrameStateRel.label_runResult_at_withGasOracle
          (label := bodyLabel) (pre := preBodyLabel)
          (post := compiledBody.code ++ [Assembly.Instr.label endLabel] ++ post)
          (oracle := oracle) (cursor := cursorAfterCond)
          hBodyLabelFit hPcAfterCond hRelAfterCond
      have hBodyLabelRunLocal :
          ARunResultWithGasOracle
            (pre ++
              (Stmt.compileFromCtxCore (.if_ cond body) ctx supply).code ++
                post)
            oracle cursorAfterCond targetAfterCond
            (fun result targetCursorAtBody =>
              match result with
              | .running targetAtBody =>
                  targetCursorAtBody = cursorAfterCond ∧
                    Frame.StateRel stateAfterCond targetAtBody tokens ∧
                      targetAtBody.pc = Assembly.Program.pcAfter preBody
              | .halted _ => False) := by
        exact ARunResultWithGasOracle.mono
          (by
            simpa [Stmt.compileFromCtxCore, bodyLabel, endLabel, compiledBody,
              preBodyLabel, preBody, List.append_assoc] using hBodyLabelRun)
          (by
            intro result targetCursorAtBody hResult
            cases result with
            | halted halt =>
                cases hResult
            | running targetAtBody =>
                simpa [preBody] using hResult)
      have hBodyLabelRun' :
          ARunResultWithGasOracle layout.asm oracle cursorAfterCond
            targetAfterCond
            (fun result targetCursorAtBody =>
              match result with
              | .running targetAtBody =>
                  targetCursorAtBody = cursorAfterCond ∧
                    Frame.StateRel stateAfterCond targetAtBody tokens ∧
                      targetAtBody.pc = Assembly.Program.pcAfter preBody
              | .halted _ => False) :=
        ARunResultWithGasOracle.cast_program hLocalAsm hBodyLabelRunLocal
      refine
        ARunResultWithGasOracle.bind_running
          (program := layout.asm) (oracle := oracle)
          (cursor := cursorAfterCond) (state := targetAfterCond)
          (middle := fun targetAtBody targetCursorAtBody =>
            targetCursorAtBody = cursorAfterCond ∧
              Frame.StateRel stateAfterCond targetAtBody tokens ∧
                targetAtBody.pc = Assembly.Program.pcAfter preBody)
          hBodyLabelRun' ?_
      intro targetAtBody targetCursorAtBody hAtBody
      rcases hAtBody with ⟨hCursorAtBody, hRelAtBody, hPcAtBody⟩
      subst targetCursorAtBody
      have hBodyRun :=
        hBody (fuel := bodyFuel) (source := stateAfterCond) (outcome := outcome)
          (target := targetAtBody) (tokens := tokens) (oracle := oracle)
          (cursor := cursorAfterCond) (cursorFinal := cursorFinal)
          hBodyLt hProgramWF hCtxProcs hBodyCalls hResolve bodySeg
          (by simpa [bodySeg, CodeSegment.startPc] using hPcAtBody)
          hRelAtBody hBodyEval
      cases outcome with
      | mk outState outMode =>
          cases outMode with
          | regular =>
              have hBodyRegular :
                  ARunResultWithGasOracle layout.asm oracle cursorAfterCond
                    targetAtBody
                    (fun result targetCursorBeforeEnd =>
                      match result with
                      | .running targetBeforeEnd =>
                          targetCursorBeforeEnd = cursorFinal ∧
                            Frame.StateRel outState targetBeforeEnd tokens ∧
                              targetBeforeEnd.pc =
                                Assembly.Program.pcAfter
                                  (preBody ++ compiledBody.code)
                      | .halted _ => False) := by
                exact ARunResultWithGasOracle.mono hBodyRun (by
                  intro result targetCursorBeforeEnd hResult
                  rcases hResult with ⟨hCursorEnd, hCompiled⟩
                  cases result with
                  | halted halt =>
                      cases hCompiled
                  | running targetBeforeEnd =>
                      exact
                        ⟨ hCursorEnd
                        , by
                            simpa [bodySeg, CodeSegment.fallthroughPc,
                              CompiledOutcomeRel, Outcome.regular,
                              preEndLabel, List.append_assoc]
                              using hCompiled
                        ⟩)
              refine
                ARunResultWithGasOracle.bind_running
                  (program := layout.asm) (oracle := oracle)
                  (cursor := cursorAfterCond) (state := targetAtBody)
                  (middle := fun targetBeforeEnd targetCursorBeforeEnd =>
                    targetCursorBeforeEnd = cursorFinal ∧
                      Frame.StateRel outState targetBeforeEnd tokens ∧
                        targetBeforeEnd.pc =
                          Assembly.Program.pcAfter
                            (preBody ++ compiledBody.code))
                  hBodyRegular ?_
              intro targetBeforeEnd targetCursorBeforeEnd hBeforeEnd
              rcases hBeforeEnd with
                ⟨hCursorBeforeEnd, hRelBeforeEnd, hPcBeforeEnd⟩
              subst targetCursorBeforeEnd
              have hEndRun :=
                FrameStateRel.label_runResult_at_withGasOracle
                  (label := endLabel) (pre := preEndLabel) (post := post)
                  (oracle := oracle) (cursor := cursorFinal)
                  hEndLabelFit
                  (by
                    simpa [preEndLabel, preBody, List.append_assoc]
                      using hPcBeforeEnd)
                  hRelBeforeEnd
              have hEndRunLocal :
                  ARunResultWithGasOracle
                    (pre ++
                      (Stmt.compileFromCtxCore (.if_ cond body) ctx supply).code ++
                        post)
                    oracle cursorFinal targetBeforeEnd
                    (fun result targetCursorFinal =>
                      targetCursorFinal = cursorFinal ∧
                        CompiledOutcomeRel layout.asm ctx
                          segment.fallthroughPc
                          (Outcome.regular outState) result tokens) := by
                exact ARunResultWithGasOracle.mono
                  (by
                    simpa [Stmt.compileFromCtxCore, bodyLabel, endLabel,
                      compiledBody, preEndLabel, List.append_assoc]
                      using hEndRun)
                  (by
                    intro result targetCursorFinal hResult
                    cases result with
                    | halted halt =>
                        cases hResult
                    | running targetFinal =>
                        rcases hResult with ⟨hCursor, hTargetRel, hTargetPc⟩
                        exact
                          ⟨ hCursor
                          , by
                              simpa [pre, post, Stmt.compileFromCtxCore,
                                bodyLabel, endLabel, compiledBody,
                                preEndLabel, CompiledOutcomeRel,
                                Outcome.regular, CodeSegment.fallthroughPc,
                                List.append_assoc]
                                using And.intro hTargetRel hTargetPc
                          ⟩)
              exact
                ARunResultWithGasOracle.cast_program hLocalAsm hEndRunLocal
          | brk =>
              exact ARunResultWithGasOracle.mono hBodyRun (by
                intro result targetCursor hResult
                rcases hResult with ⟨hCursor, hCompiled⟩
                cases result with
                | running target' =>
                    exact ⟨hCursor, by
                      simpa [bodySeg, CodeSegment.fallthroughPc,
                        CompiledOutcomeRel, Outcome.brk] using hCompiled⟩
                | halted halt =>
                    cases hCompiled)
          | cont =>
              exact ARunResultWithGasOracle.mono hBodyRun (by
                intro result targetCursor hResult
                rcases hResult with ⟨hCursor, hCompiled⟩
                cases result with
                | running target' =>
                    exact ⟨hCursor, by
                      simpa [bodySeg, CodeSegment.fallthroughPc,
                        CompiledOutcomeRel, Outcome.cont] using hCompiled⟩
                | halted halt =>
                    cases hCompiled)
          | leave =>
              exact ARunResultWithGasOracle.mono hBodyRun (by
                intro result targetCursor hResult
                rcases hResult with ⟨hCursor, hCompiled⟩
                cases result with
                | running target' =>
                    exact ⟨hCursor, by
                      simpa [bodySeg, CodeSegment.fallthroughPc,
                        CompiledOutcomeRel, Outcome.leave] using hCompiled⟩
                | halted halt =>
                    cases hCompiled)
          | halt kind =>
              exact ARunResultWithGasOracle.mono hBodyRun (by
                intro result targetCursor hResult
                rcases hResult with ⟨hCursor, hCompiled⟩
                cases result with
                | running target' =>
                    cases hCompiled
                | halted halt =>
                    exact ⟨hCursor, by
                      simpa [bodySeg, CodeSegment.fallthroughPc,
                        CompiledOutcomeRel, Outcome.halt] using hCompiled⟩)

def SwitchCasesPreservesInProgramLayoutWithGasOracleAtFuel
    {program : Program}
    (layout :
      _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.ProgramLayout
        program)
    (fuel : Nat) (ctx : CompileContext)
    (endLabel : Assembly.Label) (base supply : LabelSupply) :
    Nat → List (Word × Block) → Prop
  | _idx, [] => True
  | idx, (_value, body) :: rest =>
      let bodySupply := supply
      let compiledBody := Block.compileFromCtx body ctx bodySupply
      BlockPreservesInProgramLayoutWithGasOracleAtFuel layout fuel ctx
        bodySupply body ∧
        SwitchCasesPreservesInProgramLayoutWithGasOracleAtFuel layout fuel ctx
          endLabel base compiledBody.next (idx + 1) rest

def SwitchDefaultPreservesInProgramLayoutWithGasOracleAtFuel
    {program : Program}
    (layout :
      _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.ProgramLayout
        program)
    (fuel : Nat) (ctx : CompileContext)
    (supply : LabelSupply) : Option Block → Prop
  | none => True
  | some body =>
      BlockPreservesInProgramLayoutWithGasOracleAtFuel layout fuel ctx supply
        body

def SwitchCasesPreservesInProgramLayoutWithGasOracleUpTo
    {program : Program}
    (layout :
      _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.ProgramLayout
        program)
    (maxFuel : Nat) (ctx : CompileContext)
    (endLabel : Assembly.Label) (base supply : LabelSupply) :
    Nat → List (Word × Block) → Prop
  | _idx, [] => True
  | idx, (_value, body) :: rest =>
      let bodySupply := supply
      let compiledBody := Block.compileFromCtx body ctx bodySupply
      BlockPreservesInProgramLayoutWithGasOracleUpTo layout maxFuel ctx
        bodySupply body ∧
        SwitchCasesPreservesInProgramLayoutWithGasOracleUpTo layout maxFuel ctx
          endLabel base compiledBody.next (idx + 1) rest

def SwitchDefaultPreservesInProgramLayoutWithGasOracleUpTo
    {program : Program}
    (layout :
      _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.ProgramLayout
        program)
    (maxFuel : Nat) (ctx : CompileContext)
    (supply : LabelSupply) : Option Block → Prop
  | none => True
  | some body =>
      BlockPreservesInProgramLayoutWithGasOracleUpTo layout maxFuel ctx supply
        body

theorem switchCasesPreservesInProgramLayoutWithGasOracleAtFuel_head
    {program : Program}
    {layout :
      _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.ProgramLayout
        program}
    {fuel : Nat} {ctx : CompileContext}
    {endLabel : Assembly.Label} {base supply : LabelSupply} {idx : Nat}
    {value : Word} {body : Block} {rest : List (Word × Block)}
    (hCases :
      SwitchCasesPreservesInProgramLayoutWithGasOracleAtFuel layout fuel ctx
        endLabel base supply idx ((value, body) :: rest)) :
    BlockPreservesInProgramLayoutWithGasOracleAtFuel layout fuel ctx supply
      body := by
  exact hCases.1

theorem switchCasesPreservesInProgramLayoutWithGasOracleAtFuel_tail
    {program : Program}
    {layout :
      _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.ProgramLayout
        program}
    {fuel : Nat} {ctx : CompileContext}
    {endLabel : Assembly.Label} {base supply : LabelSupply} {idx : Nat}
    {value : Word} {body : Block} {rest : List (Word × Block)}
    (hCases :
      SwitchCasesPreservesInProgramLayoutWithGasOracleAtFuel layout fuel ctx
        endLabel base supply idx ((value, body) :: rest)) :
    SwitchCasesPreservesInProgramLayoutWithGasOracleAtFuel layout fuel ctx
      endLabel base (Block.compileFromCtx body ctx supply).next (idx + 1)
      rest := by
  exact hCases.2

theorem switchDefaultPreservesInProgramLayoutWithGasOracleAtFuel_some
    {program : Program}
    {layout :
      _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.ProgramLayout
        program}
    {fuel : Nat} {ctx : CompileContext}
    {supply : LabelSupply} {body : Block}
    (hDefault :
      SwitchDefaultPreservesInProgramLayoutWithGasOracleAtFuel layout fuel ctx
        supply (some body)) :
    BlockPreservesInProgramLayoutWithGasOracleAtFuel layout fuel ctx supply
      body := by
  exact hDefault

theorem switchCasesPreservesInProgramLayoutWithGasOracleUpTo_head
    {program : Program}
    {layout :
      _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.ProgramLayout
        program}
    {maxFuel : Nat} {ctx : CompileContext}
    {endLabel : Assembly.Label} {base supply : LabelSupply} {idx : Nat}
    {value : Word} {body : Block} {rest : List (Word × Block)}
    (hCases :
      SwitchCasesPreservesInProgramLayoutWithGasOracleUpTo layout maxFuel ctx
        endLabel base supply idx ((value, body) :: rest)) :
    BlockPreservesInProgramLayoutWithGasOracleUpTo layout maxFuel ctx supply
      body := by
  exact hCases.1

theorem switchCasesPreservesInProgramLayoutWithGasOracleUpTo_tail
    {program : Program}
    {layout :
      _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.ProgramLayout
        program}
    {maxFuel : Nat} {ctx : CompileContext}
    {endLabel : Assembly.Label} {base supply : LabelSupply} {idx : Nat}
    {value : Word} {body : Block} {rest : List (Word × Block)}
    (hCases :
      SwitchCasesPreservesInProgramLayoutWithGasOracleUpTo layout maxFuel ctx
        endLabel base supply idx ((value, body) :: rest)) :
    SwitchCasesPreservesInProgramLayoutWithGasOracleUpTo layout maxFuel ctx
      endLabel base (Block.compileFromCtx body ctx supply).next (idx + 1)
      rest := by
  exact hCases.2

theorem switchDefaultPreservesInProgramLayoutWithGasOracleUpTo_some
    {program : Program}
    {layout :
      _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.ProgramLayout
        program}
    {maxFuel : Nat} {ctx : CompileContext}
    {supply : LabelSupply} {body : Block}
    (hDefault :
      SwitchDefaultPreservesInProgramLayoutWithGasOracleUpTo layout maxFuel ctx
        supply (some body)) :
    BlockPreservesInProgramLayoutWithGasOracleUpTo layout maxFuel ctx supply
      body := by
  exact hDefault

theorem switchCasesPreservesInProgramLayoutWithGasOracleAtFuel_of_upTo
    {program : Program}
    {layout :
      _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.ProgramLayout
        program}
    {maxFuel fuel : Nat} {ctx : CompileContext}
    {endLabel : Assembly.Label} {base supply : LabelSupply} {idx : Nat}
    {cases : List (Word × Block)}
    (hLt : fuel < maxFuel)
    (hCases :
      SwitchCasesPreservesInProgramLayoutWithGasOracleUpTo layout maxFuel ctx
        endLabel base supply idx cases) :
    SwitchCasesPreservesInProgramLayoutWithGasOracleAtFuel layout fuel ctx
      endLabel base supply idx cases := by
  induction cases generalizing supply idx with
  | nil =>
      trivial
  | cons head rest ih =>
      rcases head with ⟨value, body⟩
      constructor
      · exact
          blockPreservesInProgramLayoutWithGasOracleAtFuel_of_upTo
            (layout := layout) (maxFuel := maxFuel) (fuel := fuel)
            (ctx := ctx) (supply := supply) (block := body)
            hLt
            (switchCasesPreservesInProgramLayoutWithGasOracleUpTo_head
              hCases)
      · exact
          ih
            (by
              simpa using
                switchCasesPreservesInProgramLayoutWithGasOracleUpTo_tail
                  hCases)

theorem switchDefaultPreservesInProgramLayoutWithGasOracleAtFuel_of_upTo
    {program : Program}
    {layout :
      _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.ProgramLayout
        program}
    {maxFuel fuel : Nat} {ctx : CompileContext}
    {supply : LabelSupply} {defaultBody : Option Block}
    (hLt : fuel < maxFuel)
    (hDefault :
      SwitchDefaultPreservesInProgramLayoutWithGasOracleUpTo layout maxFuel ctx
        supply defaultBody) :
    SwitchDefaultPreservesInProgramLayoutWithGasOracleAtFuel layout fuel ctx
      supply defaultBody := by
  cases defaultBody with
  | none =>
      trivial
  | some body =>
      exact
        blockPreservesInProgramLayoutWithGasOracleAtFuel_of_upTo
          (layout := layout) (maxFuel := maxFuel) (fuel := fuel)
          (ctx := ctx) (supply := supply) (block := body)
          hLt
          (switchDefaultPreservesInProgramLayoutWithGasOracleUpTo_some
            hDefault)

theorem switchCasesPreservesInProgramLayoutWithGasOracleUpTo_of_all
    {program : Program}
    {layout :
      _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.ProgramLayout
        program}
    {maxFuel : Nat} {ctx : CompileContext}
    {endLabel : Assembly.Label} {base supply : LabelSupply} {idx : Nat}
    {cases : List (Word × Block)}
    (hAll :
      ∀ bodySupply value body,
        (value, body) ∈ cases →
          BlockPreservesInProgramLayoutWithGasOracleUpTo layout maxFuel ctx
            bodySupply body) :
    SwitchCasesPreservesInProgramLayoutWithGasOracleUpTo layout maxFuel ctx
      endLabel base supply idx cases := by
  induction cases generalizing supply idx with
  | nil =>
      trivial
  | cons head rest ih =>
      rcases head with ⟨value, body⟩
      constructor
      · exact hAll supply value body (by simp)
      · exact ih
          (by
            intro bodySupply value' body' hMem
            exact hAll bodySupply value' body' (by simp [hMem]))

theorem labeled_body_tail_result_ctx_in_programLayout_withGasOracle
    {program : Program}
    {layout :
      _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.ProgramLayout
        program}
    {ctx : CompileContext} {bodySupply : LabelSupply} {body : Block}
    {betweenEnd : Assembly.Program}
    {caseLabel endLabel : Assembly.Label}
    {fuel : Nat} {source : RunState} {outcome : Outcome}
    {target : EVMState} {tokens : List Word}
    {stack : EvmYul.Stack Word} {value : Word}
    {oracle : GasOracle} {cursor cursorFinal : Nat}
    (hBody :
      BlockPreservesInProgramLayoutWithGasOracleAtFuel layout fuel ctx
        bodySupply body)
    (segment :
      CodeSegment layout.asm
        ([Assembly.Instr.label caseLabel, Assembly.Instr.prim .pop] ++
          (Block.compileFromCtx body ctx bodySupply).code ++
          [Assembly.Instr.jump endLabel] ++ betweenEnd ++
          [Assembly.Instr.label endLabel]))
    (hProgramWF : program.WF)
    (hCtxProcs : ctx.procs = program.procs)
    (hBodyCalls :
      _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.CallsIncluded
        (Block.compileFromCtx body ctx bodySupply).calls layout.sites)
    (hResolve : ContextLabelsResolve layout.asm ctx)
    (hPc : target.pc = segment.startPc)
    (hRel : Frame.StateRel source target tokens)
    (hPop : source.evm.stack.pop = some (stack, value))
    (hBodyEval :
      Block.EvalWithGasOracle program oracle fuel body cursor
        (source.withEVM { source.evm with stack := stack }) outcome
        cursorFinal) :
    ARunResultWithGasOracle layout.asm oracle cursor target
      (fun result targetCursorFinal =>
        targetCursorFinal = cursorFinal ∧
          CompiledOutcomeRel layout.asm ctx segment.fallthroughPc outcome result
            tokens) := by
  let pre := segment.pre
  let post := segment.post
  let compiledBody := Block.compileFromCtx body ctx bodySupply
  let code : Assembly.Program :=
    [Assembly.Instr.label caseLabel, Assembly.Instr.prim .pop] ++
      compiledBody.code ++ [Assembly.Instr.jump endLabel] ++ betweenEnd ++
      [Assembly.Instr.label endLabel]
  let preAfterLabel : Assembly.Program := pre ++ [Assembly.Instr.label caseLabel]
  let preBody : Assembly.Program :=
    preAfterLabel ++ [Assembly.Instr.prim .pop]
  let preAfterBody : Assembly.Program := preBody ++ compiledBody.code
  let preEndLabel : Assembly.Program :=
    preAfterBody ++ [Assembly.Instr.jump endLabel] ++ betweenEnd
  have hLocalAsm :
      pre ++ code ++ post = layout.asm := by
    simpa [pre, post, code, compiledBody] using segment.hAsm.symm
  have hFitsCode : AssemblyProgram.PCFitsFrom pre code := by
    simpa [pre, code, compiledBody] using segment.hFits
  have hFitLabel : PCFits pre :=
    AssemblyProgram.PCFitsFrom.start hFitsCode
  have hFitPop : PCFits preAfterLabel := by
    have hPrefix :
        AssemblyProgram.PCFitsFrom pre [Assembly.Instr.label caseLabel] :=
      AssemblyProgram.PCFitsFrom.left (pre := pre)
        (first := [Assembly.Instr.label caseLabel])
        (second :=
          [Assembly.Instr.prim .pop] ++ compiledBody.code ++
            [Assembly.Instr.jump endLabel] ++ betweenEnd ++
            [Assembly.Instr.label endLabel])
        (by simpa [code, compiledBody, List.append_assoc] using hFitsCode)
    simpa [preAfterLabel] using AssemblyProgram.PCFitsFrom.end hPrefix
  have hBodyFits :
      AssemblyProgram.PCFitsFrom preBody compiledBody.code := by
    have hAfterPop :
        AssemblyProgram.PCFitsFrom preBody
          (compiledBody.code ++ [Assembly.Instr.jump endLabel] ++
            betweenEnd ++ [Assembly.Instr.label endLabel]) := by
      simpa [preAfterLabel, preBody, code, compiledBody, List.append_assoc]
        using
          AssemblyProgram.PCFitsFrom.right (pre := pre)
            (first :=
              [Assembly.Instr.label caseLabel, Assembly.Instr.prim .pop])
            (second :=
              compiledBody.code ++ [Assembly.Instr.jump endLabel] ++
                betweenEnd ++ [Assembly.Instr.label endLabel])
            (by simpa [code, compiledBody, List.append_assoc] using hFitsCode)
    exact
      AssemblyProgram.PCFitsFrom.left (pre := preBody)
        (first := compiledBody.code)
        (second :=
          [Assembly.Instr.jump endLabel] ++ betweenEnd ++
            [Assembly.Instr.label endLabel])
        (by simpa [List.append_assoc] using hAfterPop)
  have hFitJumpEnd : PCFits preAfterBody := by
    simpa [preAfterBody, List.append_assoc] using
      AssemblyProgram.PCFitsFrom.end hBodyFits
  have hFitEndLabel : PCFits preEndLabel := by
    have hPrefix :
        AssemblyProgram.PCFitsFrom pre
          ([Assembly.Instr.label caseLabel, Assembly.Instr.prim .pop] ++
            compiledBody.code ++ [Assembly.Instr.jump endLabel] ++
            betweenEnd) :=
      AssemblyProgram.PCFitsFrom.left (pre := pre)
        (first :=
          [Assembly.Instr.label caseLabel, Assembly.Instr.prim .pop] ++
            compiledBody.code ++ [Assembly.Instr.jump endLabel] ++
            betweenEnd)
        (second := [Assembly.Instr.label endLabel])
        (by simpa [code, compiledBody, List.append_assoc] using hFitsCode)
    simpa [preAfterLabel, preBody, preAfterBody, preEndLabel,
      List.append_assoc] using AssemblyProgram.PCFitsFrom.end hPrefix
  have hExactLocal : ExactLabels (pre ++ code ++ post) :=
    ExactLabels.cast_asm hLocalAsm.symm layout.exactLabels
  have hEndLabel :
      Assembly.Program.labelPc
          (pre ++ code ++ post)
          endLabel =
        some (Assembly.Program.byteLength preEndLabel) := by
    have hHere :=
      hExactLocal.labelPc_at preEndLabel endLabel post
        (by
          simp [preAfterLabel, preBody, preAfterBody, preEndLabel, code,
            compiledBody, List.append_assoc])
    simpa [preAfterLabel, preBody, preAfterBody, preEndLabel, code,
      compiledBody, List.append_assoc] using hHere
  let bodySeg : CodeSegment layout.asm compiledBody.code :=
    { pre := preBody
      post :=
        [Assembly.Instr.jump endLabel] ++ betweenEnd ++
          [Assembly.Instr.label endLabel] ++ post
      hAsm := by
        simpa [pre, post, preAfterLabel, preBody, code, compiledBody,
          List.append_assoc] using segment.hAsm
      hFits := hBodyFits }
  have hLabelRun :=
    FrameStateRel.label_runResult_at_withGasOracle
      (label := caseLabel) (pre := pre)
      (post :=
        [Assembly.Instr.prim .pop] ++ compiledBody.code ++
          [Assembly.Instr.jump endLabel] ++ betweenEnd ++
          [Assembly.Instr.label endLabel] ++ post)
      (oracle := oracle) (cursor := cursor)
      hFitLabel (by simpa [pre, CodeSegment.startPc] using hPc) hRel
  have hLabelRunLocal :
      ARunResultWithGasOracle (pre ++ code ++ post) oracle cursor target
        (fun result targetCursorAfterLabel =>
          match result with
          | .running targetAfterLabel =>
              targetCursorAfterLabel = cursor ∧
                Frame.StateRel source targetAfterLabel tokens ∧
                  targetAfterLabel.pc = Assembly.Program.pcAfter preAfterLabel
          | .halted _ => False) := by
    exact ARunResultWithGasOracle.mono
      (by
        simpa [code, preAfterLabel, compiledBody, List.append_assoc]
          using hLabelRun)
      (by
        intro result targetCursorAfterLabel hResult
        cases result with
        | halted halt =>
            cases hResult
        | running targetAfterLabel =>
            simpa [preAfterLabel] using hResult)
  have hLabelRun' :
      ARunResultWithGasOracle layout.asm oracle cursor target
        (fun result targetCursorAfterLabel =>
          match result with
          | .running targetAfterLabel =>
              targetCursorAfterLabel = cursor ∧
                Frame.StateRel source targetAfterLabel tokens ∧
                  targetAfterLabel.pc = Assembly.Program.pcAfter preAfterLabel
          | .halted _ => False) :=
    ARunResultWithGasOracle.cast_program hLocalAsm hLabelRunLocal
  refine
    ARunResultWithGasOracle.bind_running
      (program := layout.asm)
      (middle := fun targetAfterLabel targetCursorAfterLabel =>
        targetCursorAfterLabel = cursor ∧
          Frame.StateRel source targetAfterLabel tokens ∧
            targetAfterLabel.pc = Assembly.Program.pcAfter preAfterLabel)
      hLabelRun' ?_
  intro targetAfterLabel targetCursorAfterLabel hAfterLabel
  rcases hAfterLabel with ⟨hCursorAfterLabel, hRelAfterLabel, hPcAfterLabel⟩
  subst targetCursorAfterLabel
  rcases FrameStateRel.pop_stepResult_at_withGasOracle
      (pre := preAfterLabel)
      (post :=
        compiledBody.code ++ [Assembly.Instr.jump endLabel] ++ betweenEnd ++
          [Assembly.Instr.label endLabel] ++ post)
      (source := source) (target := targetAfterLabel) (tokens := tokens)
      (stack := stack) (value := value)
      (oracle := oracle) (cursor := cursor)
      (by simpa [preAfterLabel, List.append_assoc] using hFitPop)
      hPcAfterLabel hRelAfterLabel hPop with
    ⟨targetAfterPop, hPopStep, hRelAfterPop, hPcAfterPop⟩
  have hPopRunLocal :
      ARunResultWithGasOracle (pre ++ code ++ post) oracle cursor
        targetAfterLabel
        (fun result targetCursorAfterPop =>
          match result with
          | .running targetAfterPop' =>
              targetCursorAfterPop = cursor ∧
                Frame.StateRel
                  (source.withEVM { source.evm with stack := stack })
                  targetAfterPop' tokens ∧
                  targetAfterPop'.pc = Assembly.Program.pcAfter preBody
          | .halted _ => False) := by
    have hRun :
        ARunResultWithGasOracle
          (preAfterLabel ++ [Assembly.Instr.prim .pop] ++
            (compiledBody.code ++ [Assembly.Instr.jump endLabel] ++
              betweenEnd ++ [Assembly.Instr.label endLabel] ++ post))
          oracle cursor targetAfterLabel
          (fun result targetCursorAfterPop =>
            match result with
            | .running targetAfterPop' =>
                targetCursorAfterPop = cursor ∧
                  Frame.StateRel
                    (source.withEVM { source.evm with stack := stack })
                    targetAfterPop' tokens ∧
                    targetAfterPop'.pc = Assembly.Program.pcAfter preBody
            | .halted _ => False) := by
      refine ⟨1, .running targetAfterPop, cursor, ?_, ?_⟩
      · unfold Assembly.GasParametric.sourceRunNResultWithGasOracle
        rw [hPopStep]
        rfl
      · exact
          ⟨rfl, hRelAfterPop,
            by simpa [preBody, List.append_assoc] using hPcAfterPop⟩
    simpa [preAfterLabel, preBody, code, compiledBody, List.append_assoc]
      using hRun
  have hPopRun' :
      ARunResultWithGasOracle layout.asm oracle cursor targetAfterLabel
        (fun result targetCursorAfterPop =>
          match result with
          | .running targetAfterPop' =>
              targetCursorAfterPop = cursor ∧
                Frame.StateRel
                  (source.withEVM { source.evm with stack := stack })
                  targetAfterPop' tokens ∧
                  targetAfterPop'.pc = Assembly.Program.pcAfter preBody
          | .halted _ => False) :=
    ARunResultWithGasOracle.cast_program hLocalAsm hPopRunLocal
  refine
    ARunResultWithGasOracle.bind_running
      (program := layout.asm)
      (middle := fun targetAfterPop targetCursorAfterPop =>
        targetCursorAfterPop = cursor ∧
          Frame.StateRel
            (source.withEVM { source.evm with stack := stack })
            targetAfterPop tokens ∧
            targetAfterPop.pc = Assembly.Program.pcAfter preBody)
      hPopRun' ?_
  intro targetAfterPop targetCursorAfterPop hAfterPop
  rcases hAfterPop with
    ⟨hCursorAfterPop, hRelAfterPop', hPcAfterPop'⟩
  subst targetCursorAfterPop
  have hBodyRun :=
    hBody
      (source := source.withEVM { source.evm with stack := stack })
      (outcome := outcome) (target := targetAfterPop) (tokens := tokens)
      (oracle := oracle) (cursor := cursor) (cursorFinal := cursorFinal)
      hProgramWF hCtxProcs hBodyCalls hResolve bodySeg
      (by simpa [bodySeg, CodeSegment.startPc] using hPcAfterPop')
      hRelAfterPop' hBodyEval
  cases outcome with
  | mk outState outMode =>
      cases outMode with
      | regular =>
          have hBodyRegular :
              ARunResultWithGasOracle layout.asm oracle cursor targetAfterPop
                (fun result targetCursorBeforeEnd =>
                  match result with
                  | .running targetBeforeEnd =>
                      targetCursorBeforeEnd = cursorFinal ∧
                        Frame.StateRel outState targetBeforeEnd tokens ∧
                          targetBeforeEnd.pc =
                            Assembly.Program.pcAfter preAfterBody
                  | .halted _ => False) := by
            exact ARunResultWithGasOracle.mono hBodyRun (by
              intro result targetCursorBeforeEnd hResult
              rcases hResult with ⟨hCursorBeforeEnd, hCompiled⟩
              cases result with
              | halted halt =>
                  cases hCompiled
              | running targetBeforeEnd =>
                  exact
                    ⟨hCursorBeforeEnd, by
                      simpa [bodySeg, CodeSegment.fallthroughPc,
                        CompiledOutcomeRel, Outcome.regular, preAfterBody,
                        List.append_assoc] using hCompiled⟩)
          refine
            ARunResultWithGasOracle.bind_running
              (program := layout.asm)
              (middle := fun targetBeforeEnd targetCursorBeforeEnd =>
                targetCursorBeforeEnd = cursorFinal ∧
                  Frame.StateRel outState targetBeforeEnd tokens ∧
                    targetBeforeEnd.pc =
                      Assembly.Program.pcAfter preAfterBody)
              hBodyRegular ?_
          intro targetBeforeEnd targetCursorBeforeEnd hBeforeEnd
          rcases hBeforeEnd with
            ⟨hCursorBeforeEnd, hRelBeforeEnd, hPcBeforeEnd⟩
          subst targetCursorBeforeEnd
          have hEndRun :=
            FrameStateRel.jump_then_label_runResult_at_withGasOracle
              (label := endLabel) (pre := preAfterBody)
              (between := betweenEnd) (post := post)
              (oracle := oracle) (cursor := cursorFinal)
              hFitJumpEnd
              (by
                simpa [preAfterBody, preEndLabel, List.append_assoc]
                  using hFitEndLabel)
              hPcBeforeEnd hRelBeforeEnd
              (by
                simpa [preAfterLabel, preBody, preAfterBody, preEndLabel,
                  code, compiledBody, List.append_assoc] using hEndLabel)
          have hEndRunLocal :
              ARunResultWithGasOracle (pre ++ code ++ post) oracle cursorFinal
                targetBeforeEnd
                (fun result targetCursorFinal' =>
                  targetCursorFinal' = cursorFinal ∧
                    CompiledOutcomeRel layout.asm ctx segment.fallthroughPc
                      (Outcome.regular outState) result tokens) := by
            exact ARunResultWithGasOracle.mono
              (by
                simpa [preAfterLabel, preBody, preAfterBody, code,
                  compiledBody, List.append_assoc] using hEndRun)
              (by
                intro result targetCursorFinal' hResult
                cases result with
                | halted halt =>
                    cases hResult
                | running targetFinal =>
                    rcases hResult with ⟨hCursor, hTargetRel, hTargetPc⟩
                    exact
                      ⟨hCursor, by
                        simpa [pre, post, code, compiledBody, preAfterLabel,
                          preBody, preAfterBody, preEndLabel,
                          CompiledOutcomeRel, Outcome.regular,
                          CodeSegment.fallthroughPc, List.append_assoc]
                          using And.intro hTargetRel hTargetPc⟩)
          exact
            ARunResultWithGasOracle.cast_program hLocalAsm hEndRunLocal
      | brk =>
          exact ARunResultWithGasOracle.mono hBodyRun (by
            intro result targetCursor hResult
            rcases hResult with ⟨hCursor, hCompiled⟩
            cases result with
            | running target' =>
                exact
                  ⟨hCursor, by
                    simpa [bodySeg, CodeSegment.fallthroughPc,
                      CompiledOutcomeRel, Outcome.brk] using hCompiled⟩
            | halted halt =>
                cases hCompiled)
      | cont =>
          exact ARunResultWithGasOracle.mono hBodyRun (by
            intro result targetCursor hResult
            rcases hResult with ⟨hCursor, hCompiled⟩
            cases result with
            | running target' =>
                exact
                  ⟨hCursor, by
                    simpa [bodySeg, CodeSegment.fallthroughPc,
                      CompiledOutcomeRel, Outcome.cont] using hCompiled⟩
            | halted halt =>
                cases hCompiled)
      | leave =>
          exact ARunResultWithGasOracle.mono hBodyRun (by
            intro result targetCursor hResult
            rcases hResult with ⟨hCursor, hCompiled⟩
            cases result with
            | running target' =>
                exact
                  ⟨hCursor, by
                    simpa [bodySeg, CodeSegment.fallthroughPc,
                      CompiledOutcomeRel, Outcome.leave] using hCompiled⟩
            | halted halt =>
                cases hCompiled)
      | halt kind =>
          exact ARunResultWithGasOracle.mono hBodyRun (by
            intro result targetCursor hResult
            rcases hResult with ⟨hCursor, hCompiled⟩
            cases result with
            | running target' =>
                cases hCompiled
            | halted halt =>
                exact
                  ⟨hCursor, by
                    simpa [bodySeg, CodeSegment.fallthroughPc,
                      CompiledOutcomeRel, Outcome.halt] using hCompiled⟩)

private theorem switchTestCode_runWithGasOracle_eq_run_forProgramLayout
    {probe : Word} (oracle : GasOracle) (cursor : Nat)
    {state : EvmYul.EVM.State} :
    Code.runWithGasOracle (Stmt.switchTestCode probe) oracle cursor state =
      (do
        let final ← Code.run (Stmt.switchTestCode probe) state
        pure (final, cursor)) := by
  simp [Stmt.switchTestCode, Code.runWithGasOracle, Code.run,
    BasicInstr.stepWithGasOracle, BasicOp.stepWithGasOracle,
    BasicInstr.step, BasicOp.step, BasicOp.toPrimOp,
    Assembly.Target.stepInstr,
    Assembly.GasParametric.Target.stepInstrWithGasOracle,
    Assembly.GasParametric.PrimOp.stepWithGasOracle,
    Bind.bind, Except.bind]
  cases hDup : Assembly.PrimOp.step .dup1 state <;>
    simp [pure, Except.pure]
  rename_i afterDup
  cases hEq :
      Assembly.PrimOp.step .eq
        (EvmYul.EVM.State.replaceStackAndIncrPC afterDup
          (afterDup.stack.push probe) 33) <;>
    simp

private theorem switchTestCode_runConditionStateWithGasOracle_of_plain_forProgramLayout
    {probe : Word} {oracle : GasOracle} {cursor : Nat}
    {source final : RunState} {cond : Bool}
    (hRun :
      Code.runConditionState (Stmt.switchTestCode probe) source =
        .ok (final, cond)) :
    Code.runConditionStateWithGasOracle (Stmt.switchTestCode probe) oracle
        cursor source =
      .ok (final, cond, cursor) := by
  unfold Code.runConditionStateWithGasOracle
  unfold EvmCompiler.Structured.Code.runConditionState at hRun
  unfold Code.runConditionWithGasOracle
  unfold EvmCompiler.Structured.Code.runCondition at hRun
  rw [switchTestCode_runWithGasOracle_eq_run_forProgramLayout]
  cases hCode : Code.run (Stmt.switchTestCode probe) source.evm with
  | error err =>
      rw [hCode] at hRun
      simp [Bind.bind, Except.bind] at hRun
  | ok evmAfterCode =>
      rw [hCode] at hRun
      simp [Bind.bind, Except.bind]
      cases hPop : Code.popCondition evmAfterCode with
      | error err =>
          simp [hPop, Bind.bind, Except.bind] at hRun ⊢
      | ok popResult =>
          rcases popResult with ⟨evmAfterPop, condAfterPop⟩
          simp [hPop, Bind.bind, Except.bind] at hRun ⊢
          rcases hRun with ⟨hFinal, hCond⟩
          cases hFinal
          cases hCond
          simp [hPop, pure, Except.pure]

private theorem switchTest_runConditionState_withGasOracle_forProgramLayout
    {source : RunState} {stack : EvmYul.Stack Word} {value probe : Word}
    (oracle : GasOracle) (cursor : Nat)
    (hPop : source.evm.stack.pop = some (stack, value)) :
    ∃ final,
      Code.runConditionStateWithGasOracle (Stmt.switchTestCode probe) oracle
          cursor source =
        .ok (final, probe = value, cursor) ∧
      final.returns = source.returns ∧
      final.evm.stack = source.evm.stack ∧
      eraseControl final.evm = eraseControl source.evm := by
  rcases EvmCompiler.Structured.Preservation.SwitchPreservation.test_runConditionState
      (source := source) (stack := stack) (value := value) (probe := probe)
      hPop with
    ⟨final, hRun, hReturns, hStack, hErase⟩
  exact
    ⟨ final
    , switchTestCode_runConditionStateWithGasOracle_of_plain_forProgramLayout
        (oracle := oracle) (cursor := cursor) hRun
    , hReturns, hStack, hErase
    ⟩

private theorem switchTest_jumpi_result_ctx_withGasOracle_forProgramLayout
    {pre post : Assembly.Program}
    {label : Assembly.Label} {dest : Nat}
    {source : RunState} {target : EVMState} {tokens : List Word}
    {stack : EvmYul.Stack Word} {value probe : Word}
    {oracle : GasOracle} {cursor : Nat}
    (hFits : Code.PCFitsFrom pre (Stmt.switchTestCode probe))
    (hPc : target.pc = Assembly.Program.pcAfter pre)
    (hRel : Frame.StateRel source target tokens)
    (hLabel :
      Assembly.Program.labelPc
          (pre ++ (Stmt.switchTestCode probe).toAssembly ++
            [Assembly.Instr.jumpi label] ++ post) label = some dest)
    (hPop : source.evm.stack.pop = some (stack, value)) :
    ARunResultWithGasOracle
      (pre ++ (Stmt.switchTestCode probe).toAssembly ++
        [Assembly.Instr.jumpi label] ++ post)
      oracle cursor target
      (fun result cursorFinal =>
        match result with
        | .running target' =>
            cursorFinal = cursor ∧
              Frame.StateRel source target' tokens ∧
                target'.pc =
                  if probe = value then
                    EvmYul.UInt256.ofNat dest
                  else
                    Assembly.Program.pcAfter
                      (pre ++ (Stmt.switchTestCode probe).toAssembly ++
                        [Assembly.Instr.jumpi label])
        | .halted _ => False) := by
  rcases switchTest_runConditionState_withGasOracle_forProgramLayout
      (source := source) (stack := stack) (value := value) (probe := probe)
      oracle cursor hPop with
    ⟨final, hRun, hReturns, hStack, hErase⟩
  have hRunJump :=
    FrameStateRel.runCondition_jumpi_result_ctx_withGasOracle
      (source := source) (final := final) (target := target)
      (tokens := tokens) (cond := Stmt.switchTestCode probe)
      (label := label) (dest := dest) (pre := pre) (post := post)
      (condTrue := probe = value) (oracle := oracle) (cursor := cursor)
      (cursor' := cursor)
      (Code.runnerSafeWithGasOracle_of_runnerSafe
        (EvmCompiler.Structured.Preservation.Code.switchTestCode_runnerSafe
          probe))
      (Code.switchTestCode_frameSafeWithGasOracle probe)
      hFits hPc hRel hLabel hRun
  exact ARunResultWithGasOracle.mono hRunJump (by
    intro result cursorFinal hResult
    cases result with
    | halted halt =>
        cases hResult
    | running target' =>
        rcases hResult with ⟨hCursor, hFinalRel, hTargetPc⟩
        refine ⟨hCursor, ?_, ?_⟩
        · refine ⟨?_, ?_⟩
          · rw [← hStack, ← hReturns]
            exact hFinalRel.stackRel
          · calc
              eraseControl target'
                  = eraseControl { final.evm with stack := target'.stack } :=
                      hFinalRel.dataRel
              _ = eraseControl { source.evm with stack := target'.stack } := by
                      exact eraseControl_with_stack_congr hErase
        · simpa [Bool.decide_eq_true] using hTargetPc)

private theorem switchTest_true_result_ctx_withGasOracle_forProgramLayout
    {pre post : Assembly.Program}
    {label : Assembly.Label} {dest : Nat}
    {source : RunState} {target : EVMState} {tokens : List Word}
    {stack : EvmYul.Stack Word} {value probe : Word}
    {oracle : GasOracle} {cursor : Nat}
    (hEq : probe = value)
    (hFits : Code.PCFitsFrom pre (Stmt.switchTestCode probe))
    (hPc : target.pc = Assembly.Program.pcAfter pre)
    (hRel : Frame.StateRel source target tokens)
    (hLabel :
      Assembly.Program.labelPc
          (pre ++ (Stmt.switchTestCode probe).toAssembly ++
            [Assembly.Instr.jumpi label] ++ post) label = some dest)
    (hPop : source.evm.stack.pop = some (stack, value)) :
    ARunResultWithGasOracle
      (pre ++ (Stmt.switchTestCode probe).toAssembly ++
        [Assembly.Instr.jumpi label] ++ post)
      oracle cursor target
      (fun result cursorFinal =>
        match result with
        | .running target' =>
            cursorFinal = cursor ∧
              Frame.StateRel source target' tokens ∧
                target'.pc = EvmYul.UInt256.ofNat dest
        | .halted _ => False) := by
  exact ARunResultWithGasOracle.mono
    (switchTest_jumpi_result_ctx_withGasOracle_forProgramLayout
      (pre := pre) (post := post) (label := label) (dest := dest)
      (source := source) (target := target) (tokens := tokens)
      (stack := stack) (value := value) (probe := probe)
      (oracle := oracle) (cursor := cursor)
      hFits hPc hRel hLabel hPop)
    (by
      intro result cursorFinal hResult
      cases result with
      | halted halt =>
          cases hResult
      | running target' =>
          simpa [hEq] using hResult)

private theorem switchTest_false_result_ctx_withGasOracle_forProgramLayout
    {pre post : Assembly.Program}
    {label : Assembly.Label} {dest : Nat}
    {source : RunState} {target : EVMState} {tokens : List Word}
    {stack : EvmYul.Stack Word} {value probe : Word}
    {oracle : GasOracle} {cursor : Nat}
    (hNe : probe ≠ value)
    (hFits : Code.PCFitsFrom pre (Stmt.switchTestCode probe))
    (hPc : target.pc = Assembly.Program.pcAfter pre)
    (hRel : Frame.StateRel source target tokens)
    (hLabel :
      Assembly.Program.labelPc
          (pre ++ (Stmt.switchTestCode probe).toAssembly ++
            [Assembly.Instr.jumpi label] ++ post) label = some dest)
    (hPop : source.evm.stack.pop = some (stack, value)) :
    ARunResultWithGasOracle
      (pre ++ (Stmt.switchTestCode probe).toAssembly ++
        [Assembly.Instr.jumpi label] ++ post)
      oracle cursor target
      (fun result cursorFinal =>
        match result with
        | .running target' =>
            cursorFinal = cursor ∧
              Frame.StateRel source target' tokens ∧
                target'.pc =
                  Assembly.Program.pcAfter
                    (pre ++ (Stmt.switchTestCode probe).toAssembly ++
                      [Assembly.Instr.jumpi label])
        | .halted _ => False) := by
  exact ARunResultWithGasOracle.mono
    (switchTest_jumpi_result_ctx_withGasOracle_forProgramLayout
      (pre := pre) (post := post) (label := label) (dest := dest)
      (source := source) (target := target) (tokens := tokens)
      (stack := stack) (value := value) (probe := probe)
      (oracle := oracle) (cursor := cursor)
      hFits hPc hRel hLabel hPop)
    (by
      intro result cursorFinal hResult
      cases result with
      | halted halt =>
          cases hResult
      | running target' =>
          simpa [hNe] using hResult)

theorem head_case_from_tests_result_ctx_in_programLayout_withGasOracle
    {program : Program}
    {layout :
      _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.ProgramLayout
        program}
    {ctx : CompileContext} {base supply : LabelSupply} {idx : Nat}
    {probe : Word} {body : Block} {rest : List (Word × Block)}
    {defaultBody : Option Block}
    {casePrefix : Assembly.Program}
    {defaultLabel endLabel : Assembly.Label}
    {fuel : Nat} {source : RunState} {outcome : Outcome}
    {target : EVMState} {tokens : List Word}
    {stack : EvmYul.Stack Word} {value : Word}
    {oracle : GasOracle} {cursor cursorFinal : Nat}
    (hBody :
      BlockPreservesInProgramLayoutWithGasOracleAtFuel layout fuel ctx supply
        body)
    (hEq : probe = value)
    (segment :
      CodeSegment layout.asm
        (Stmt.switchTest base idx probe ++
          Stmt.switchTests base (idx + 1) rest ++
          [Assembly.Instr.jump defaultLabel] ++
          casePrefix ++
          [ Assembly.Instr.label (LabelSupply.label base (idx + 2))
          , Assembly.Instr.prim .pop ] ++
          (Block.compileFromCtx body ctx supply).code ++
          [Assembly.Instr.jump endLabel] ++
          (SwitchCases.compileFromCtx rest ctx endLabel base
            (Block.compileFromCtx body ctx supply).next (idx + 1)).code ++
          (SwitchDefault.compileFromCtx defaultBody ctx endLabel defaultLabel
            (SwitchCases.compileFromCtx rest ctx endLabel base
              (Block.compileFromCtx body ctx supply).next (idx + 1)).next).code ++
          [Assembly.Instr.label endLabel]))
    (hProgramWF : program.WF)
    (hCtxProcs : ctx.procs = program.procs)
    (hBodyCalls :
      _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.CallsIncluded
        (Block.compileFromCtx body ctx supply).calls layout.sites)
    (hResolve : ContextLabelsResolve layout.asm ctx)
    (hPc : target.pc = segment.startPc)
    (hRel : Frame.StateRel source target tokens)
    (hPop : source.evm.stack.pop = some (stack, value))
    (hBodyEval :
      Block.EvalWithGasOracle program oracle fuel body cursor
        (source.withEVM { source.evm with stack := stack }) outcome
        cursorFinal) :
    ARunResultWithGasOracle layout.asm oracle cursor target
      (fun result targetCursorFinal =>
        targetCursorFinal = cursorFinal ∧
          CompiledOutcomeRel layout.asm ctx segment.fallthroughPc outcome result
            tokens) := by
  let pre := segment.pre
  let post := segment.post
  let caseLabel := LabelSupply.label base (idx + 2)
  let testCode := Stmt.switchTest base idx probe
  let restTests := Stmt.switchTests base (idx + 1) rest
  let compiledBody := Block.compileFromCtx body ctx supply
  let compiledTail :=
    SwitchCases.compileFromCtx rest ctx endLabel base compiledBody.next
      (idx + 1)
  let compiledDefault :=
    SwitchDefault.compileFromCtx defaultBody ctx endLabel defaultLabel
      compiledTail.next
  let fullCode : Assembly.Program :=
    testCode ++ restTests ++ [Assembly.Instr.jump defaultLabel] ++
      casePrefix ++ [Assembly.Instr.label caseLabel, Assembly.Instr.prim .pop] ++
      compiledBody.code ++ [Assembly.Instr.jump endLabel] ++
      compiledTail.code ++ compiledDefault.code ++
      [Assembly.Instr.label endLabel]
  let preCase : Assembly.Program :=
    pre ++ testCode ++ restTests ++ [Assembly.Instr.jump defaultLabel] ++
      casePrefix
  have hLocalAsm : pre ++ fullCode ++ post = layout.asm := by
    simpa [pre, post, fullCode, caseLabel, testCode, restTests,
      compiledBody, compiledTail, compiledDefault] using segment.hAsm.symm
  have hFitsHead : AssemblyProgram.PCFitsFrom pre fullCode := by
    simpa [pre, fullCode, caseLabel, testCode, restTests, compiledBody,
      compiledTail, compiledDefault] using segment.hFits
  have hTestFitsAsm : AssemblyProgram.PCFitsFrom pre testCode :=
    AssemblyProgram.PCFitsFrom.left (pre := pre)
      (first := testCode)
      (second :=
        restTests ++ [Assembly.Instr.jump defaultLabel] ++
          casePrefix ++
          [Assembly.Instr.label caseLabel, Assembly.Instr.prim .pop] ++
          compiledBody.code ++ [Assembly.Instr.jump endLabel] ++
          compiledTail.code ++ compiledDefault.code ++
          [Assembly.Instr.label endLabel])
      (by simpa [fullCode, List.append_assoc] using hFitsHead)
  have hCondFitsAsm :
      AssemblyProgram.PCFitsFrom pre
        (Stmt.switchTestCode probe).toAssembly :=
    AssemblyProgram.PCFitsFrom.left (pre := pre)
      (first := (Stmt.switchTestCode probe).toAssembly)
      (second := [Assembly.Instr.jumpi caseLabel])
      (by simpa [Stmt.switchTest, caseLabel, testCode] using hTestFitsAsm)
  have hCondFits : Code.PCFitsFrom pre (Stmt.switchTestCode probe) :=
    Code.PCFitsFrom.of_assembly hCondFitsAsm
  have hExactLocal : ExactLabels (pre ++ fullCode ++ post) :=
    ExactLabels.cast_asm hLocalAsm.symm layout.exactLabels
  have hCaseLabel :
      Assembly.Program.labelPc
          (pre ++ (Stmt.switchTestCode probe).toAssembly ++
            [Assembly.Instr.jumpi caseLabel] ++
            (restTests ++ [Assembly.Instr.jump defaultLabel] ++
              casePrefix ++
              [Assembly.Instr.label caseLabel, Assembly.Instr.prim .pop] ++
              compiledBody.code ++ [Assembly.Instr.jump endLabel] ++
              compiledTail.code ++ compiledDefault.code ++
              [Assembly.Instr.label endLabel] ++ post))
          caseLabel =
        some (Assembly.Program.byteLength preCase) := by
    have hHere :=
      hExactLocal.labelPc_at preCase caseLabel
        ([Assembly.Instr.prim .pop] ++ compiledBody.code ++
          [Assembly.Instr.jump endLabel] ++ compiledTail.code ++
          compiledDefault.code ++ [Assembly.Instr.label endLabel] ++ post)
        (by
          simp [preCase, fullCode, testCode, Stmt.switchTest, caseLabel,
            List.append_assoc])
    simpa [preCase, fullCode, testCode, Stmt.switchTest, caseLabel,
      List.append_assoc] using hHere
  have hTestRun :=
    switchTest_true_result_ctx_withGasOracle_forProgramLayout
      (pre := pre)
      (post :=
        restTests ++ [Assembly.Instr.jump defaultLabel] ++
          casePrefix ++
          [Assembly.Instr.label caseLabel, Assembly.Instr.prim .pop] ++
          compiledBody.code ++ [Assembly.Instr.jump endLabel] ++
          compiledTail.code ++ compiledDefault.code ++
          [Assembly.Instr.label endLabel] ++ post)
      (label := caseLabel)
      (dest := Assembly.Program.byteLength preCase)
      (source := source) (target := target) (tokens := tokens)
      (stack := stack) (value := value) (probe := probe)
      (oracle := oracle) (cursor := cursor)
      hEq hCondFits (by simpa [pre, CodeSegment.startPc] using hPc)
      hRel (by simpa [List.append_assoc] using hCaseLabel) hPop
  have hTestToCaseLocal :
      ARunResultWithGasOracle (pre ++ fullCode ++ post) oracle cursor target
        (fun result targetCursorAtCase =>
          match result with
          | .running targetAtCase =>
              targetCursorAtCase = cursor ∧
                Frame.StateRel source targetAtCase tokens ∧
                  targetAtCase.pc = Assembly.Program.pcAfter preCase
          | .halted _ => False) := by
    exact ARunResultWithGasOracle.mono
      (by
        simpa [fullCode, testCode, restTests, caseLabel,
          List.append_assoc] using hTestRun)
      (by
        intro result targetCursorAtCase hResult
        cases result with
        | halted halt =>
            cases hResult
        | running targetAtCase =>
            rcases hResult with ⟨hCursorAtCase, hRelAtCase, hPcAtCase⟩
            exact
              ⟨hCursorAtCase, hRelAtCase,
                by simpa [Assembly.Program.pcAfter] using hPcAtCase⟩)
  have hTestToCase :
      ARunResultWithGasOracle layout.asm oracle cursor target
        (fun result targetCursorAtCase =>
          match result with
          | .running targetAtCase =>
              targetCursorAtCase = cursor ∧
                Frame.StateRel source targetAtCase tokens ∧
                  targetAtCase.pc = Assembly.Program.pcAfter preCase
          | .halted _ => False) :=
    ARunResultWithGasOracle.cast_program hLocalAsm hTestToCaseLocal
  refine
    ARunResultWithGasOracle.bind_running
      (program := layout.asm)
      (middle := fun targetAtCase targetCursorAtCase =>
        targetCursorAtCase = cursor ∧
          Frame.StateRel source targetAtCase tokens ∧
            targetAtCase.pc = Assembly.Program.pcAfter preCase)
      hTestToCase ?_
  intro targetAtCase targetCursorAtCase hAtCase
  rcases hAtCase with ⟨hCursorAtCase, hRelAtCase, hPcAtCase⟩
  subst targetCursorAtCase
  let tailCode : Assembly.Program :=
    [Assembly.Instr.label caseLabel, Assembly.Instr.prim .pop] ++
      compiledBody.code ++ [Assembly.Instr.jump endLabel] ++
      (compiledTail.code ++ compiledDefault.code) ++
      [Assembly.Instr.label endLabel]
  have hTailFits :
      AssemblyProgram.PCFitsFrom preCase tailCode := by
    have hRight :
        AssemblyProgram.PCFitsFrom preCase
          ([Assembly.Instr.label caseLabel, Assembly.Instr.prim .pop] ++
            compiledBody.code ++ [Assembly.Instr.jump endLabel] ++
            compiledTail.code ++ compiledDefault.code ++
            [Assembly.Instr.label endLabel]) := by
      simpa [preCase, fullCode, List.append_assoc] using
        AssemblyProgram.PCFitsFrom.right (pre := pre)
          (first :=
            testCode ++ restTests ++ [Assembly.Instr.jump defaultLabel] ++
              casePrefix)
          (second :=
            [Assembly.Instr.label caseLabel, Assembly.Instr.prim .pop] ++
              compiledBody.code ++ [Assembly.Instr.jump endLabel] ++
              compiledTail.code ++ compiledDefault.code ++
              [Assembly.Instr.label endLabel])
          (by simpa [fullCode, List.append_assoc] using hFitsHead)
    simpa [tailCode, List.append_assoc] using hRight
  let tailSeg : CodeSegment layout.asm tailCode :=
    { pre := preCase
      post := post
      hAsm := by
        simpa [pre, post, preCase, fullCode, tailCode, caseLabel, testCode,
          restTests, compiledBody, compiledTail, compiledDefault,
          List.append_assoc] using segment.hAsm
      hFits := hTailFits }
  have hTailRun :=
    labeled_body_tail_result_ctx_in_programLayout_withGasOracle
      (program := program) (layout := layout) (ctx := ctx)
      (bodySupply := supply) (body := body)
      (betweenEnd := compiledTail.code ++ compiledDefault.code)
      (caseLabel := caseLabel) (endLabel := endLabel)
      (source := source) (outcome := outcome) (target := targetAtCase)
      (tokens := tokens) (stack := stack) (value := value)
      (oracle := oracle) (cursor := cursor) (cursorFinal := cursorFinal)
      hBody tailSeg hProgramWF hCtxProcs hBodyCalls hResolve
      (by simpa [tailSeg, CodeSegment.startPc] using hPcAtCase)
      hRelAtCase hPop hBodyEval
  exact
    ARunResultWithGasOracle.mono hTailRun
      (by
        intro result targetCursorFinal hResult
        rcases hResult with ⟨hCursorFinal, hCompiled⟩
        exact
          ⟨hCursorFinal, by
            simpa [tailSeg, tailCode, fullCode, preCase,
              CodeSegment.fallthroughPc, caseLabel, testCode, restTests,
              compiledBody, compiledTail, compiledDefault, List.append_assoc]
              using hCompiled⟩)

theorem default_selected_tail_result_ctx_in_programLayout_withGasOracle
    {program : Program}
    {layout :
      _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.ProgramLayout
        program}
    {ctx : CompileContext} {bodySupply : LabelSupply} {body : Block}
    {between : Assembly.Program}
    {defaultLabel endLabel : Assembly.Label}
    {fuel : Nat} {source : RunState} {outcome : Outcome}
    {target : EVMState} {tokens : List Word}
    {stack : EvmYul.Stack Word} {value : Word}
    {oracle : GasOracle} {cursor cursorFinal : Nat}
    (hBody :
      BlockPreservesInProgramLayoutWithGasOracleAtFuel layout fuel ctx
        bodySupply body)
    (segment :
      CodeSegment layout.asm
        ([Assembly.Instr.jump defaultLabel] ++ between ++
          [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop] ++
          (Block.compileFromCtx body ctx bodySupply).code ++
          [Assembly.Instr.jump endLabel, Assembly.Instr.label endLabel]))
    (hProgramWF : program.WF)
    (hCtxProcs : ctx.procs = program.procs)
    (hBodyCalls :
      _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.CallsIncluded
        (Block.compileFromCtx body ctx bodySupply).calls layout.sites)
    (hResolve : ContextLabelsResolve layout.asm ctx)
    (hPc : target.pc = segment.startPc)
    (hRel : Frame.StateRel source target tokens)
    (hPop : source.evm.stack.pop = some (stack, value))
    (hBodyEval :
      Block.EvalWithGasOracle program oracle fuel body cursor
        (source.withEVM { source.evm with stack := stack }) outcome
        cursorFinal) :
    ARunResultWithGasOracle layout.asm oracle cursor target
      (fun result targetCursorFinal =>
        targetCursorFinal = cursorFinal ∧
          CompiledOutcomeRel layout.asm ctx segment.fallthroughPc outcome result
            tokens) := by
  let pre := segment.pre
  let post := segment.post
  let compiledBody := Block.compileFromCtx body ctx bodySupply
  let fullCode : Assembly.Program :=
    [Assembly.Instr.jump defaultLabel] ++ between ++
      [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop] ++
      compiledBody.code ++ [Assembly.Instr.jump endLabel,
        Assembly.Instr.label endLabel]
  let preDefault : Assembly.Program :=
    pre ++ [Assembly.Instr.jump defaultLabel] ++ between
  have hLocalAsm : pre ++ fullCode ++ post = layout.asm := by
    simpa [pre, post, fullCode, compiledBody] using segment.hAsm.symm
  have hFitsFull : AssemblyProgram.PCFitsFrom pre fullCode := by
    simpa [pre, fullCode, compiledBody] using segment.hFits
  have hFitJump : PCFits pre :=
    AssemblyProgram.PCFitsFrom.start hFitsFull
  have hTailFits :
      AssemblyProgram.PCFitsFrom preDefault
        ([Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop] ++
          compiledBody.code ++ [Assembly.Instr.jump endLabel] ++
          [Assembly.Instr.label endLabel]) := by
    simpa [preDefault, fullCode, compiledBody, List.append_assoc] using
      AssemblyProgram.PCFitsFrom.right (pre := pre)
        (first := [Assembly.Instr.jump defaultLabel] ++ between)
        (second :=
          [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop] ++
            compiledBody.code ++ [Assembly.Instr.jump endLabel] ++
            [Assembly.Instr.label endLabel])
        (by simpa [fullCode, compiledBody, List.append_assoc] using hFitsFull)
  have hExactLocal : ExactLabels (pre ++ fullCode ++ post) :=
    ExactLabels.cast_asm hLocalAsm.symm layout.exactLabels
  have hDefaultLabel :
      Assembly.Program.labelPc
          (pre ++ [Assembly.Instr.jump defaultLabel] ++
            (between ++
              [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop] ++
              compiledBody.code ++
              [Assembly.Instr.jump endLabel, Assembly.Instr.label endLabel] ++
              post))
          defaultLabel =
        some (Assembly.Program.byteLength preDefault) := by
    have hHere :=
      hExactLocal.labelPc_at preDefault defaultLabel
        ([Assembly.Instr.prim .pop] ++ compiledBody.code ++
          [Assembly.Instr.jump endLabel, Assembly.Instr.label endLabel] ++ post)
        (by simp [preDefault, fullCode, compiledBody, List.append_assoc])
    simpa [preDefault, fullCode, compiledBody, List.append_assoc] using hHere
  rcases FrameStateRel.jump_stepResult_at_withGasOracle
      (label := defaultLabel)
      (dest := Assembly.Program.byteLength preDefault)
      (pre := pre)
      (post :=
        between ++ [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop] ++
          compiledBody.code ++
          [Assembly.Instr.jump endLabel, Assembly.Instr.label endLabel] ++ post)
      (oracle := oracle) (cursor := cursor)
      hFitJump (by simpa [pre, CodeSegment.startPc] using hPc) hRel
      hDefaultLabel with
    ⟨targetAtDefault, hJumpStep, hRelAtDefault, hPcAtDefault⟩
  have hJumpRunLocal :
      ARunResultWithGasOracle (pre ++ fullCode ++ post) oracle cursor target
        (fun result targetCursorAtDefault =>
          match result with
          | .running targetAtDefault' =>
              targetCursorAtDefault = cursor ∧
                Frame.StateRel source targetAtDefault' tokens ∧
                  targetAtDefault'.pc = Assembly.Program.pcAfter preDefault
          | .halted _ => False) := by
    refine ⟨1, .running targetAtDefault, cursor, ?_, ?_⟩
    · unfold Assembly.GasParametric.sourceRunNResultWithGasOracle
      have hStep' :
          Assembly.GasParametric.sourceStepResultWithGasOracle
              (pre ++ [Assembly.Instr.jump defaultLabel] ++
                (between ++
                  [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop] ++
                  compiledBody.code ++
                  [Assembly.Instr.jump endLabel, Assembly.Instr.label endLabel] ++
                  post))
              oracle cursor target =
            .ok (.running targetAtDefault, cursor) := by
        simpa [fullCode, compiledBody, List.append_assoc] using hJumpStep
      rw [show
          pre ++ fullCode ++ post =
            pre ++ [Assembly.Instr.jump defaultLabel] ++
              (between ++
                [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop] ++
                compiledBody.code ++
                [Assembly.Instr.jump endLabel, Assembly.Instr.label endLabel] ++
                post) by
          simp [fullCode, compiledBody, List.append_assoc]]
      rw [hStep']
      rfl
    · exact
        ⟨rfl, hRelAtDefault,
          by simpa [preDefault, Assembly.Program.pcAfter] using hPcAtDefault⟩
  have hJumpRun :
      ARunResultWithGasOracle layout.asm oracle cursor target
        (fun result targetCursorAtDefault =>
          match result with
          | .running targetAtDefault' =>
              targetCursorAtDefault = cursor ∧
                Frame.StateRel source targetAtDefault' tokens ∧
                  targetAtDefault'.pc = Assembly.Program.pcAfter preDefault
          | .halted _ => False) :=
    ARunResultWithGasOracle.cast_program hLocalAsm hJumpRunLocal
  refine
    ARunResultWithGasOracle.bind_running
      (program := layout.asm)
      (middle := fun targetAtDefault targetCursorAtDefault =>
        targetCursorAtDefault = cursor ∧
          Frame.StateRel source targetAtDefault tokens ∧
            targetAtDefault.pc = Assembly.Program.pcAfter preDefault)
      hJumpRun ?_
  intro targetAtDefault' targetCursorAtDefault hAtDefault
  rcases hAtDefault with ⟨hCursorAtDefault, hRelAtDefault', hPcAtDefault'⟩
  subst targetCursorAtDefault
  let tailCode : Assembly.Program :=
    [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop] ++
      compiledBody.code ++ [Assembly.Instr.jump endLabel] ++
      ([] : Assembly.Program) ++
      [Assembly.Instr.label endLabel]
  let tailSeg : CodeSegment layout.asm tailCode :=
    { pre := preDefault
      post := post
      hAsm := by
        simpa [pre, post, preDefault, fullCode, tailCode, compiledBody,
          List.append_assoc] using segment.hAsm
      hFits := by
        simpa [tailCode, List.append_assoc] using hTailFits }
  have hTailRun :=
    labeled_body_tail_result_ctx_in_programLayout_withGasOracle
      (program := program) (layout := layout) (ctx := ctx)
      (bodySupply := bodySupply) (body := body)
      (betweenEnd := []) (caseLabel := defaultLabel) (endLabel := endLabel)
      (source := source) (outcome := outcome) (target := targetAtDefault')
      (tokens := tokens) (stack := stack) (value := value)
      (oracle := oracle) (cursor := cursor) (cursorFinal := cursorFinal)
      hBody tailSeg hProgramWF hCtxProcs hBodyCalls hResolve
      (by simpa [tailSeg, CodeSegment.startPc] using hPcAtDefault')
      hRelAtDefault' hPop hBodyEval
  exact
    ARunResultWithGasOracle.mono hTailRun
      (by
        intro result targetCursorFinal hResult
        rcases hResult with ⟨hCursorFinal, hCompiled⟩
        exact
          ⟨hCursorFinal, by
            simpa [tailSeg, tailCode, fullCode, preDefault,
              CodeSegment.fallthroughPc, compiledBody, List.append_assoc]
              using hCompiled⟩)

set_option maxHeartbeats 800000 in
theorem selected_cases_result_ctx_in_programLayout_withGasOracle
    {program : Program}
    {layout :
      _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.ProgramLayout
        program}
    {ctx : CompileContext} {base supply : LabelSupply} {idx : Nat}
    {cases : List (Word × Block)} {defaultBody : Option Block}
    {selected : Block}
    {casePrefix : Assembly.Program}
    {defaultLabel endLabel : Assembly.Label}
    {fuel : Nat} {source : RunState} {outcome : Outcome}
    {target : EVMState} {tokens : List Word}
    {stack : EvmYul.Stack Word} {value : Word}
    {oracle : GasOracle} {cursor cursorFinal : Nat}
    (hCases :
      SwitchCasesPreservesInProgramLayoutWithGasOracleAtFuel layout fuel ctx
        endLabel base supply idx cases)
    (hDefault :
      SwitchDefaultPreservesInProgramLayoutWithGasOracleAtFuel layout fuel ctx
        (SwitchCases.compileFromCtx cases ctx endLabel base supply idx).next
        defaultBody)
    (hCaseCalls :
      CallsIncluded
        (SwitchCases.compileFromCtx cases ctx endLabel base supply idx).calls
        layout.sites)
    (hDefaultCalls :
      CallsIncluded
        (SwitchDefault.compileFromCtx defaultBody ctx endLabel defaultLabel
          (SwitchCases.compileFromCtx cases ctx endLabel base supply idx).next).calls
        layout.sites)
    (segment :
      CodeSegment layout.asm
        (Stmt.switchTests base idx cases ++
          [Assembly.Instr.jump defaultLabel] ++
          casePrefix ++
          (SwitchCases.compileFromCtx cases ctx endLabel base supply idx).code ++
          (SwitchDefault.compileFromCtx defaultBody ctx endLabel defaultLabel
            (SwitchCases.compileFromCtx cases ctx endLabel base supply idx).next).code ++
          [Assembly.Instr.label endLabel]))
    (hProgramWF : program.WF)
    (hCtxProcs : ctx.procs = program.procs)
    (hResolve : ContextLabelsResolve layout.asm ctx)
    (hPc : target.pc = segment.startPc)
    (hRel : Frame.StateRel source target tokens)
    (hPop : source.evm.stack.pop = some (stack, value))
    (hSelect : Switch.select value cases defaultBody = some selected)
    (hBodyEval :
      Block.EvalWithGasOracle program oracle fuel selected cursor
        (source.withEVM { source.evm with stack := stack }) outcome
        cursorFinal) :
    ARunResultWithGasOracle layout.asm oracle cursor target
      (fun result targetCursorFinal =>
        targetCursorFinal = cursorFinal ∧
          CompiledOutcomeRel layout.asm ctx segment.fallthroughPc outcome result
            tokens) := by
  induction cases generalizing supply idx casePrefix target selected with
  | nil =>
      cases defaultBody with
      | none =>
          simp [Switch.select] at hSelect
      | some defaultBlock =>
          have hSelected : selected = defaultBlock := by
            simpa [Switch.select] using hSelect.symm
          subst selected
          have hDefaultBlock :
              BlockPreservesInProgramLayoutWithGasOracleAtFuel layout fuel ctx
                (SwitchCases.compileFromCtx ([] : List (Word × Block)) ctx
                  endLabel base supply idx).next defaultBlock := by
            change
              BlockPreservesInProgramLayoutWithGasOracleAtFuel layout fuel ctx
                (SwitchCases.compileFromCtx ([] : List (Word × Block)) ctx
                  endLabel base supply idx).next defaultBlock at hDefault
            exact hDefault
          have hDefaultBlockCalls :
              CallsIncluded
                (Block.compileFromCtx defaultBlock ctx
                  (SwitchCases.compileFromCtx ([] : List (Word × Block)) ctx
                    endLabel base supply idx).next).calls
                layout.sites := by
            simpa [SwitchCases.compileFromCtx, SwitchDefault.compileFromCtx]
              using hDefaultCalls
          let tailSeg :
              CodeSegment layout.asm
                ([Assembly.Instr.jump defaultLabel] ++ casePrefix ++
                  [ Assembly.Instr.label defaultLabel
                  , Assembly.Instr.prim .pop ] ++
                  (Block.compileFromCtx defaultBlock ctx
                    (SwitchCases.compileFromCtx ([] : List (Word × Block)) ctx
                      endLabel base supply idx).next).code ++
                  [Assembly.Instr.jump endLabel,
                    Assembly.Instr.label endLabel]) :=
            CodeSegment.cast_code
              (by
                simp [Stmt.switchTests, SwitchCases.compileFromCtx,
                  SwitchDefault.compileFromCtx, List.append_assoc])
              segment
          have hRun :=
            default_selected_tail_result_ctx_in_programLayout_withGasOracle
              (program := program) (layout := layout) (ctx := ctx)
              (bodySupply :=
                (SwitchCases.compileFromCtx ([] : List (Word × Block)) ctx
                  endLabel base supply idx).next)
              (body := defaultBlock)
              (between := casePrefix) (defaultLabel := defaultLabel)
              (endLabel := endLabel) (source := source) (outcome := outcome)
              (target := target) (tokens := tokens) (stack := stack)
              (value := value) (oracle := oracle) (cursor := cursor)
              (cursorFinal := cursorFinal)
              hDefaultBlock tailSeg hProgramWF hCtxProcs
              hDefaultBlockCalls hResolve
              (by simpa [tailSeg, CodeSegment.startPc] using hPc)
              hRel hPop hBodyEval
          exact
            ARunResultWithGasOracle.mono hRun
              (by
                intro result targetCursorFinal hResult
                rcases hResult with ⟨hCursorFinal, hCompiled⟩
                exact
                  ⟨hCursorFinal, by
                    simpa [tailSeg, CodeSegment.cast_code,
                      CodeSegment.fallthroughPc, Stmt.switchTests,
                      SwitchCases.compileFromCtx, SwitchDefault.compileFromCtx,
                      List.append_assoc] using hCompiled⟩)
  | cons head rest ih =>
      rcases head with ⟨probe, headBody⟩
      let caseLabel := LabelSupply.label base (idx + 2)
      let testCode := Stmt.switchTest base idx probe
      let restTests := Stmt.switchTests base (idx + 1) rest
      let compiledBody := Block.compileFromCtx headBody ctx supply
      let headCode : Assembly.Program :=
        [Assembly.Instr.label caseLabel, Assembly.Instr.prim .pop] ++
          compiledBody.code ++ [Assembly.Instr.jump endLabel]
      let compiledTail :=
        SwitchCases.compileFromCtx rest ctx endLabel base compiledBody.next
          (idx + 1)
      let compiledDefault :=
        SwitchDefault.compileFromCtx defaultBody ctx endLabel defaultLabel
          compiledTail.next
      have hHeadBodyPreserves :
          BlockPreservesInProgramLayoutWithGasOracleAtFuel layout fuel ctx
            supply headBody :=
        switchCasesPreservesInProgramLayoutWithGasOracleAtFuel_head hCases
      have hTailPreserves :
          SwitchCasesPreservesInProgramLayoutWithGasOracleAtFuel layout fuel ctx
            endLabel base compiledBody.next (idx + 1) rest := by
        simpa [compiledBody] using
          switchCasesPreservesInProgramLayoutWithGasOracleAtFuel_tail hCases
      have hDefaultTail :
          SwitchDefaultPreservesInProgramLayoutWithGasOracleAtFuel layout fuel ctx
            compiledTail.next defaultBody := by
        simpa [SwitchCases.compileFromCtx, CompileResult.append, caseLabel,
          compiledBody, compiledTail] using hDefault
      have hHeadCalls :
          CallsIncluded (Block.compileFromCtx headBody ctx supply).calls
            layout.sites :=
        _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.switchCases_calls_included_head
          hCaseCalls
      have hTailCalls :
          CallsIncluded
            (SwitchCases.compileFromCtx rest ctx endLabel base
              compiledBody.next (idx + 1)).calls layout.sites := by
        simpa [compiledBody] using
          _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.switchCases_calls_included_tail
            hCaseCalls
      have hDefaultTailCalls :
          CallsIncluded
            (SwitchDefault.compileFromCtx defaultBody ctx endLabel defaultLabel
              compiledTail.next).calls layout.sites := by
        simpa [SwitchCases.compileFromCtx, CompileResult.append, caseLabel,
          compiledBody, compiledTail] using hDefaultCalls
      by_cases hEq : probe = value
      · have hSelected : selected = headBody :=
          _root_.EvmCompiler.Structured.Preservation.SwitchPreservation.select_head_body_of_head_eq
            (value := value) (probe := probe) (headBody := headBody)
            (body := selected) (rest := rest) (defaultBody := defaultBody)
            hEq hSelect
        subst selected
        let headSeg :
            CodeSegment layout.asm
              (Stmt.switchTest base idx probe ++
                Stmt.switchTests base (idx + 1) rest ++
                [Assembly.Instr.jump defaultLabel] ++
                casePrefix ++
                [ Assembly.Instr.label (LabelSupply.label base (idx + 2))
                , Assembly.Instr.prim .pop ] ++
                (Block.compileFromCtx headBody ctx supply).code ++
                [Assembly.Instr.jump endLabel] ++
                (SwitchCases.compileFromCtx rest ctx endLabel base
                  (Block.compileFromCtx headBody ctx supply).next
                  (idx + 1)).code ++
                (SwitchDefault.compileFromCtx defaultBody ctx endLabel
                  defaultLabel
                  (SwitchCases.compileFromCtx rest ctx endLabel base
                    (Block.compileFromCtx headBody ctx supply).next
                    (idx + 1)).next).code ++
                [Assembly.Instr.label endLabel]) :=
          CodeSegment.cast_code
            (by
              simp [Stmt.switchTests, Stmt.switchTest,
                SwitchCases.compileFromCtx, CompileResult.append,
                List.append_assoc])
            segment
        have hRun :=
          head_case_from_tests_result_ctx_in_programLayout_withGasOracle
            (program := program) (layout := layout) (ctx := ctx)
            (base := base) (supply := supply) (idx := idx)
            (probe := probe) (body := headBody) (rest := rest)
            (defaultBody := defaultBody) (casePrefix := casePrefix)
            (defaultLabel := defaultLabel) (endLabel := endLabel)
            (source := source) (outcome := outcome) (target := target)
            (tokens := tokens) (stack := stack) (value := value)
            (oracle := oracle) (cursor := cursor)
            (cursorFinal := cursorFinal)
            hHeadBodyPreserves hEq headSeg hProgramWF hCtxProcs hHeadCalls
            hResolve (by simpa [headSeg, CodeSegment.startPc] using hPc)
            hRel hPop hBodyEval
        exact
          ARunResultWithGasOracle.mono hRun
            (by
              intro result targetCursorFinal hResult
              rcases hResult with ⟨hCursorFinal, hCompiled⟩
              exact
                ⟨hCursorFinal, by
                  simpa [headSeg, CodeSegment.cast_code,
                    CodeSegment.fallthroughPc, Stmt.switchTests,
                    Stmt.switchTest, SwitchCases.compileFromCtx,
                    CompileResult.append, caseLabel, testCode, restTests,
                    compiledBody, compiledTail, compiledDefault, headCode,
                    List.append_assoc] using hCompiled⟩)
      · have hTailSelect :
            Switch.select value rest defaultBody = some selected :=
          _root_.EvmCompiler.Structured.Preservation.SwitchPreservation.select_tail_of_head_ne
            (value := value) (probe := probe) (headBody := headBody)
            (body := selected) (rest := rest) (defaultBody := defaultBody)
            hEq hSelect
        let fullCode : Assembly.Program :=
          testCode ++ restTests ++ [Assembly.Instr.jump defaultLabel] ++
            casePrefix ++ headCode ++ compiledTail.code ++
            compiledDefault.code ++ [Assembly.Instr.label endLabel]
        let pre := segment.pre
        let post := segment.post
        have hLocalAsm : pre ++ fullCode ++ post = layout.asm := by
          simpa [pre, post, fullCode, Stmt.switchTests, Stmt.switchTest,
            SwitchCases.compileFromCtx, CompileResult.append, caseLabel,
            testCode, restTests, compiledBody, compiledTail, compiledDefault,
            headCode, List.append_assoc] using segment.hAsm.symm
        have hFitsCons : AssemblyProgram.PCFitsFrom pre fullCode := by
          simpa [pre, fullCode, Stmt.switchTests, Stmt.switchTest,
            SwitchCases.compileFromCtx, CompileResult.append, caseLabel,
            testCode, restTests, compiledBody, compiledTail, compiledDefault,
            headCode, List.append_assoc] using segment.hFits
        have hExactCons : ExactLabels (pre ++ fullCode ++ post) :=
          ExactLabels.cast_asm hLocalAsm.symm layout.exactLabels
        have hTestFitsAsm : AssemblyProgram.PCFitsFrom pre testCode :=
          AssemblyProgram.PCFitsFrom.left (pre := pre)
            (first := testCode)
            (second :=
              restTests ++ [Assembly.Instr.jump defaultLabel] ++
                casePrefix ++ headCode ++ compiledTail.code ++
                compiledDefault.code ++ [Assembly.Instr.label endLabel])
            (by simpa [fullCode, List.append_assoc] using hFitsCons)
        have hCondFitsAsm :
            AssemblyProgram.PCFitsFrom pre
              (Stmt.switchTestCode probe).toAssembly :=
          AssemblyProgram.PCFitsFrom.left (pre := pre)
            (first := (Stmt.switchTestCode probe).toAssembly)
            (second := [Assembly.Instr.jumpi caseLabel])
            (by simpa [Stmt.switchTest, caseLabel, testCode]
              using hTestFitsAsm)
        have hCondFits : Code.PCFitsFrom pre (Stmt.switchTestCode probe) :=
          Code.PCFitsFrom.of_assembly hCondFitsAsm
        let preCase : Assembly.Program :=
          pre ++ testCode ++ restTests ++
            [Assembly.Instr.jump defaultLabel] ++ casePrefix
        have hCaseLabel :
            Assembly.Program.labelPc
                (pre ++ (Stmt.switchTestCode probe).toAssembly ++
                  [Assembly.Instr.jumpi caseLabel] ++
                  (restTests ++ [Assembly.Instr.jump defaultLabel] ++
                    casePrefix ++ headCode ++ compiledTail.code ++
                    compiledDefault.code ++ [Assembly.Instr.label endLabel] ++
                    post))
                caseLabel =
              some (Assembly.Program.byteLength preCase) := by
          have hHere :=
            hExactCons.labelPc_at preCase caseLabel
              ([Assembly.Instr.prim .pop] ++ compiledBody.code ++
                [Assembly.Instr.jump endLabel] ++ compiledTail.code ++
                compiledDefault.code ++ [Assembly.Instr.label endLabel] ++ post)
              (by
                simp [preCase, fullCode, testCode, Stmt.switchTest, caseLabel,
                  headCode, List.append_assoc])
          simpa [preCase, fullCode, testCode, Stmt.switchTest, caseLabel,
            headCode, List.append_assoc] using hHere
        have hTestRun :=
          switchTest_false_result_ctx_withGasOracle_forProgramLayout
            (pre := pre)
            (post :=
              restTests ++ [Assembly.Instr.jump defaultLabel] ++
                casePrefix ++ headCode ++ compiledTail.code ++
                compiledDefault.code ++ [Assembly.Instr.label endLabel] ++ post)
            (label := caseLabel)
            (dest := Assembly.Program.byteLength preCase)
            (source := source) (target := target) (tokens := tokens)
            (stack := stack) (value := value) (probe := probe)
            (oracle := oracle) (cursor := cursor)
            hEq hCondFits
            (by simpa [pre, CodeSegment.startPc] using hPc)
            hRel (by simpa [List.append_assoc] using hCaseLabel) hPop
        have hTestFalseLocal :
            ARunResultWithGasOracle (pre ++ fullCode ++ post) oracle cursor target
              (fun result targetCursorAfterTest =>
                match result with
                | .running targetAfterTest =>
                    targetCursorAfterTest = cursor ∧
                      Frame.StateRel source targetAfterTest tokens ∧
                        targetAfterTest.pc =
                          Assembly.Program.pcAfter (pre ++ testCode)
                | .halted _ => False) := by
          exact ARunResultWithGasOracle.mono
            (by
              simpa [fullCode, testCode, caseLabel, List.append_assoc]
                using hTestRun)
            (by
              intro result targetCursorAfterTest hResult
              cases result with
              | halted halt =>
                  cases hResult
              | running targetAfterTest =>
                  simpa [testCode, Stmt.switchTest, caseLabel]
                    using hResult)
        have hTestFalse :
            ARunResultWithGasOracle layout.asm oracle cursor target
              (fun result targetCursorAfterTest =>
                match result with
                | .running targetAfterTest =>
                    targetCursorAfterTest = cursor ∧
                      Frame.StateRel source targetAfterTest tokens ∧
                        targetAfterTest.pc =
                          Assembly.Program.pcAfter (pre ++ testCode)
                | .halted _ => False) :=
          ARunResultWithGasOracle.cast_program hLocalAsm hTestFalseLocal
        refine
          ARunResultWithGasOracle.bind_running
            (program := layout.asm)
            (middle := fun targetAfterTest targetCursorAfterTest =>
              targetCursorAfterTest = cursor ∧
                Frame.StateRel source targetAfterTest tokens ∧
                  targetAfterTest.pc =
                    Assembly.Program.pcAfter (pre ++ testCode))
            hTestFalse ?_
        intro targetAfterTest targetCursorAfterTest hAfterTest
        rcases hAfterTest with
          ⟨hCursorAfterTest, hRelAfterTest, hPcAfterTest⟩
        subst targetCursorAfterTest
        let tailCode : Assembly.Program :=
          restTests ++ [Assembly.Instr.jump defaultLabel] ++
            (casePrefix ++ headCode) ++ compiledTail.code ++
            compiledDefault.code ++ [Assembly.Instr.label endLabel]
        let tailSeg : CodeSegment layout.asm tailCode :=
          { pre := pre ++ testCode
            post := post
            hAsm := by
              simpa [pre, post, fullCode, tailCode, Stmt.switchTests,
                Stmt.switchTest, SwitchCases.compileFromCtx,
                CompileResult.append, caseLabel, testCode, restTests,
                compiledBody, compiledTail, compiledDefault, headCode,
                List.append_assoc] using segment.hAsm
            hFits := by
              simpa [tailCode, fullCode, List.append_assoc] using
                AssemblyProgram.PCFitsFrom.right (pre := pre)
                  (first := testCode)
                  (second :=
                    restTests ++ [Assembly.Instr.jump defaultLabel] ++
                      casePrefix ++ headCode ++ compiledTail.code ++
                      compiledDefault.code ++ [Assembly.Instr.label endLabel])
                  (by simpa [fullCode, List.append_assoc] using hFitsCons) }
        have hRec :=
          ih (supply := compiledBody.next) (idx := idx + 1)
            (casePrefix := casePrefix ++ headCode)
            (target := targetAfterTest) (selected := selected)
            hTailPreserves hDefaultTail hTailCalls hDefaultTailCalls tailSeg
            (by simpa [tailSeg, CodeSegment.startPc] using hPcAfterTest)
            hRelAfterTest hTailSelect hBodyEval
        exact
          ARunResultWithGasOracle.mono hRec
            (by
              intro result targetCursorFinal hResult
              rcases hResult with ⟨hCursorFinal, hCompiled⟩
              exact
                ⟨hCursorFinal, by
                  simpa [tailSeg, tailCode, fullCode, pre, post,
                    CodeSegment.fallthroughPc, Stmt.switchTests,
                    Stmt.switchTest, SwitchCases.compileFromCtx,
                    CompileResult.append, caseLabel, testCode, restTests,
                    compiledBody, compiledTail, compiledDefault, headCode,
                    List.append_assoc] using hCompiled⟩)

theorem preserves_cons_in_programLayout_upTo_withGasOracle {program : Program}
    {layout :
      _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.ProgramLayout
        program}
    {maxFuel : Nat}
    {ctx : CompileContext} {supply : LabelSupply}
    {stmt : Stmt} {rest : List Stmt}
    (hStmt :
      StmtPreservesInProgramLayoutWithGasOracleUpTo layout maxFuel ctx supply
        stmt)
    (hRest :
      BlockPreservesInProgramLayoutWithGasOracleUpTo layout maxFuel ctx
        (Stmt.compileFromCtxCore stmt ctx supply).next { stmts := rest }) :
    BlockPreservesInProgramLayoutWithGasOracleUpTo layout maxFuel ctx supply
      { stmts := stmt :: rest } := by
  intro fuel source outcome target tokens oracle cursor cursorFinal hLt
    hProgramWF hCtxProcs hCalls hResolve segment hPc hRel hEval
  let compiledStmt := Stmt.compileFromCtxCore stmt ctx supply
  let compiledRest :=
    Block.compileFromCtx { stmts := rest } ctx compiledStmt.next
  have hCodeEq :
      (Block.compileFromCtx { stmts := stmt :: rest } ctx supply).code =
        compiledStmt.code ++ compiledRest.code := by
    simp [Block.compileFromCtx, CompileResult.append,
      compiledStmt, compiledRest]
  have hCallsEq :
      (Block.compileFromCtx { stmts := stmt :: rest } ctx supply).calls =
        compiledStmt.calls ++ compiledRest.calls := by
    simp [Block.compileFromCtx, CompileResult.append,
      compiledStmt, compiledRest]
  let appendSeg :
      CodeSegment layout.asm (compiledStmt.code ++ compiledRest.code) :=
    CodeSegment.cast_code hCodeEq segment
  let stmtSeg : CodeSegment layout.asm compiledStmt.code :=
    CodeSegment.left appendSeg
  let restSeg : CodeSegment layout.asm compiledRest.code :=
    CodeSegment.right appendSeg
  have hCallsAppend :
      CallsIncluded (compiledStmt.calls ++ compiledRest.calls) layout.sites := by
    simpa [hCallsEq] using hCalls
  have hStmtCalls : CallsIncluded compiledStmt.calls layout.sites :=
    _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.CallsIncluded.left
      hCallsAppend
  have hRestCalls : CallsIncluded compiledRest.calls layout.sites :=
    _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.CallsIncluded.right
      hCallsAppend
  have hStmtPc : target.pc = stmtSeg.startPc := by
    simpa [stmtSeg, appendSeg, CodeSegment.startPc, CodeSegment.left,
      CodeSegment.cast_code] using hPc
  have hRestFallthrough :
      restSeg.fallthroughPc = segment.fallthroughPc := by
    simp [restSeg, appendSeg, CodeSegment.fallthroughPc, CodeSegment.right,
      CodeSegment.cast_code, hCodeEq, List.append_assoc]
  cases hEval with
  | cons_regular hStmtEval hRestEval =>
      rename_i innerFuel cursorMid mid
      have hInnerLt : innerFuel < maxFuel := by omega
      have hStmtRun :=
        hStmt (fuel := innerFuel) (source := source)
          (outcome := Outcome.regular mid) (target := target)
          (tokens := tokens) (oracle := oracle) (cursor := cursor)
          (cursorFinal := cursorMid) hInnerLt hProgramWF hCtxProcs
          (by simpa [compiledStmt] using hStmtCalls)
          hResolve (by simpa [compiledStmt] using stmtSeg)
          hStmtPc hRel hStmtEval
      have hStmtRunRegular :
          ARunResultWithGasOracle layout.asm oracle cursor target
            (fun result targetCursorMid =>
              match result with
              | .running targetMid =>
                  targetCursorMid = cursorMid ∧
                    Preservation.Frame.StateRel mid targetMid tokens ∧
                    targetMid.pc = restSeg.startPc
              | .halted _ => False) := by
        exact
          ARunResultWithGasOracle.mono hStmtRun
            (by
              intro result targetCursorMid hResult
              rcases hResult with ⟨hCursorMid, hCompiled⟩
              cases result with
              | halted halt =>
                  cases hCompiled
              | running targetMid =>
                  exact ⟨hCursorMid, by
                    simpa [stmtSeg, restSeg, appendSeg,
                      CodeSegment.startPc, CodeSegment.fallthroughPc,
                      CodeSegment.left, CodeSegment.right,
                      CodeSegment.cast_code, CompiledOutcomeRel,
                      Outcome.regular, List.append_assoc] using hCompiled⟩)
      refine
        ARunResultWithGasOracle.bind_running
          (program := layout.asm) (oracle := oracle) (cursor := cursor)
          (state := target)
          (middle := fun targetMid targetCursorMid =>
            targetCursorMid = cursorMid ∧
              Preservation.Frame.StateRel mid targetMid tokens ∧
              targetMid.pc = restSeg.startPc)
          hStmtRunRegular ?_
      intro targetMid targetCursorMid hMid
      rcases hMid with ⟨hTargetCursorMid, hRelMid, hPcMid⟩
      subst targetCursorMid
      have hRestRun :=
        hRest (fuel := innerFuel) (source := mid) (outcome := outcome)
          (target := targetMid) (tokens := tokens) (oracle := oracle)
          (cursor := cursorMid) (cursorFinal := cursorFinal)
          hInnerLt hProgramWF hCtxProcs
          (by simpa [compiledRest] using hRestCalls)
          hResolve (by simpa [compiledRest] using restSeg)
          hPcMid hRelMid hRestEval
      exact
        ARunResultWithGasOracle.mono hRestRun
          (by
            intro result targetCursorFinal hResult
            simpa [hRestFallthrough] using hResult)
  | cons_brk hStmtEval =>
      rename_i innerFuel outState
      have hInnerLt : innerFuel < maxFuel := by omega
      have hStmtRun :=
        hStmt (fuel := innerFuel) (source := source)
          (outcome := Outcome.brk outState) (target := target)
          (tokens := tokens) (oracle := oracle) (cursor := cursor)
          (cursorFinal := cursorFinal) hInnerLt hProgramWF hCtxProcs
          (by simpa [compiledStmt] using hStmtCalls)
          hResolve (by simpa [compiledStmt] using stmtSeg)
          hStmtPc hRel hStmtEval
      exact
        ARunResultWithGasOracle.mono hStmtRun
          (by
            intro result targetCursorFinal hResult
            rcases hResult with ⟨hCursorFinal, hCompiled⟩
            cases result with
            | running target' =>
                exact ⟨hCursorFinal, by
                  simpa [CompiledOutcomeRel, Outcome.brk] using hCompiled⟩
            | halted halt =>
                cases hCompiled)
  | cons_cont hStmtEval =>
      rename_i innerFuel outState
      have hInnerLt : innerFuel < maxFuel := by omega
      have hStmtRun :=
        hStmt (fuel := innerFuel) (source := source)
          (outcome := Outcome.cont outState) (target := target)
          (tokens := tokens) (oracle := oracle) (cursor := cursor)
          (cursorFinal := cursorFinal) hInnerLt hProgramWF hCtxProcs
          (by simpa [compiledStmt] using hStmtCalls)
          hResolve (by simpa [compiledStmt] using stmtSeg)
          hStmtPc hRel hStmtEval
      exact
        ARunResultWithGasOracle.mono hStmtRun
          (by
            intro result targetCursorFinal hResult
            rcases hResult with ⟨hCursorFinal, hCompiled⟩
            cases result with
            | running target' =>
                exact ⟨hCursorFinal, by
                  simpa [CompiledOutcomeRel, Outcome.cont] using hCompiled⟩
            | halted halt =>
                cases hCompiled)
  | cons_leave hStmtEval =>
      rename_i innerFuel outState
      have hInnerLt : innerFuel < maxFuel := by omega
      have hStmtRun :=
        hStmt (fuel := innerFuel) (source := source)
          (outcome := Outcome.leave outState) (target := target)
          (tokens := tokens) (oracle := oracle) (cursor := cursor)
          (cursorFinal := cursorFinal) hInnerLt hProgramWF hCtxProcs
          (by simpa [compiledStmt] using hStmtCalls)
          hResolve (by simpa [compiledStmt] using stmtSeg)
          hStmtPc hRel hStmtEval
      exact
        ARunResultWithGasOracle.mono hStmtRun
          (by
            intro result targetCursorFinal hResult
            rcases hResult with ⟨hCursorFinal, hCompiled⟩
            cases result with
            | running target' =>
                exact ⟨hCursorFinal, by
                  simpa [CompiledOutcomeRel, Outcome.leave] using hCompiled⟩
            | halted halt =>
                cases hCompiled)
  | cons_halt hStmtEval =>
      rename_i innerFuel outState kind
      have hInnerLt : innerFuel < maxFuel := by omega
      have hStmtRun :=
        hStmt (fuel := innerFuel) (source := source)
          (outcome := Outcome.halt kind outState) (target := target)
          (tokens := tokens) (oracle := oracle) (cursor := cursor)
          (cursorFinal := cursorFinal) hInnerLt hProgramWF hCtxProcs
          (by simpa [compiledStmt] using hStmtCalls)
          hResolve (by simpa [compiledStmt] using stmtSeg)
          hStmtPc hRel hStmtEval
      exact
        ARunResultWithGasOracle.mono hStmtRun
          (by
            intro result targetCursorFinal hResult
            rcases hResult with ⟨hCursorFinal, hCompiled⟩
            cases result with
            | running target' =>
                cases hCompiled
            | halted halt =>
                exact ⟨hCursorFinal, by
                  simpa [CompiledOutcomeRel, Outcome.halt] using hCompiled⟩)

theorem callObligationUpTo_succ_of_procBodies_withGasOracle
    {program : Program}
    (layout :
      _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.ProgramLayout
        program)
    {maxFuel : Nat}
    (hProcBodies :
      ∀ {name : Name} {proc : Proc}
        (hLookup : ProcList.lookup? name program.procs = some proc),
        BlockPreservesInProgramLayoutWithGasOracleUpTo layout maxFuel
          (ProcedureCall.bodyCtx program proc)
          (layout.procLayout hLookup).bodySupply proc.body) :
    CallObligationUpToWithGasOracle layout (maxFuel + 1) := by
  constructor
  intro ctx supply name fuel source outcome target tokens oracle cursor
    cursorFinal hLt hProgramWF hCtxProcs hCalls _hResolve callSeg hPc hRel
    hEval
  cases hEval with
  | call_regular hLookup hSplit hBody hPop hAttach =>
      rename_i evalFuel evalProc args callerStack stack bodyState returned frame
      have hLookupCtx : ProcList.lookup? name ctx.procs = some evalProc := by
        simpa [hCtxProcs] using hLookup
      have hProcWF : Proc.WF evalProc :=
        Program.procWF_of_lookup? hProgramWF hLookup
      let procLayout := layout.procLayout hLookup
      let procSeg :
          CodeSegment layout.asm
            (ProcedureCall.procSegment program evalProc
              procLayout.bodySupply procLayout.dispatchSupply
              layout.sites) :=
        CodeSegment.cast_code
          (procSegment_eq_procedurePreservation
            (program := program) (proc := evalProc)
            (bodySupply := procLayout.bodySupply)
            (dispatchSupply := procLayout.dispatchSupply)
            (sites := layout.sites))
          procLayout.segment
      have hBodyCalls :
          CallsIncluded
            (Block.compileFromCtx evalProc.body
              (ProcedureCall.bodyCtx program evalProc)
              procLayout.bodySupply).calls
            layout.sites := by
        simpa [ProcedureCall.bodyCtx,
          _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.bodyCtx,
          procLayout] using procLayout.bodyCalls
      exact
        ProcedureCall.call_stmt_segments_withGasOracle
          (program := program) (ctx := ctx) (name := name)
          (proc := evalProc) (supply := supply)
          (bodySupply := procLayout.bodySupply)
          (dispatchSupply := procLayout.dispatchSupply)
          (sites := layout.sites)
          (site :=
            { procName := name
              token := Stmt.callToken supply
              returnLabel := LabelSupply.label supply 0 })
          (fuel := evalFuel + 1) (state := source)
          (outcome :=
            Outcome.regular
              (returned.withEVM { bodyState.evm with stack := stack }))
          (target := target) (tokens := tokens) (asm := layout.asm)
          (oracle := oracle) (cursor := cursor)
          (cursorFinal := cursorFinal)
          callSeg procSeg hCtxProcs hLookupCtx
          (fun {bodyFuel} hBodyFuelLt =>
            procBodyPreservesAtSegment_of_programLayout_withGasOracle
              (program := program) (layout := layout) (proc := evalProc)
              (bodySupply := procLayout.bodySupply)
              (dispatchSupply := procLayout.dispatchSupply)
              (fuel := bodyFuel) procSeg
              (blockPreservesInProgramLayoutWithGasOracleAtFuel_of_upTo
                (layout := layout) (maxFuel := maxFuel)
                (fuel := bodyFuel)
                (ctx := ProcedureCall.bodyCtx program evalProc)
                (supply := procLayout.bodySupply)
                (block := evalProc.body)
                (by omega)
                (hProcBodies hLookup))
              hProgramWF hBodyCalls)
          rfl
          (_root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.generated_callSite_mem_of_included
            (ctx := ctx) (supply := supply) (name := name)
            (proc := evalProc) (sites := layout.sites)
            hLookupCtx hCalls)
          layout.noDupTokens hProcWF.1 hProcWF.2.1 hPc hRel
          layout.exactLabels
          (Stmt.EvalWithGasOracle.call_regular hLookup hSplit hBody hPop
            hAttach)
  | call_leave hLookup hSplit hBody hPop hAttach =>
      rename_i evalFuel evalProc args callerStack stack bodyState returned frame
      have hLookupCtx : ProcList.lookup? name ctx.procs = some evalProc := by
        simpa [hCtxProcs] using hLookup
      have hProcWF : Proc.WF evalProc :=
        Program.procWF_of_lookup? hProgramWF hLookup
      let procLayout := layout.procLayout hLookup
      let procSeg :
          CodeSegment layout.asm
            (ProcedureCall.procSegment program evalProc
              procLayout.bodySupply procLayout.dispatchSupply
              layout.sites) :=
        CodeSegment.cast_code
          (procSegment_eq_procedurePreservation
            (program := program) (proc := evalProc)
            (bodySupply := procLayout.bodySupply)
            (dispatchSupply := procLayout.dispatchSupply)
            (sites := layout.sites))
          procLayout.segment
      have hBodyCalls :
          CallsIncluded
            (Block.compileFromCtx evalProc.body
              (ProcedureCall.bodyCtx program evalProc)
              procLayout.bodySupply).calls
            layout.sites := by
        simpa [ProcedureCall.bodyCtx,
          _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.bodyCtx,
          procLayout] using procLayout.bodyCalls
      exact
        ProcedureCall.call_stmt_segments_withGasOracle
          (program := program) (ctx := ctx) (name := name)
          (proc := evalProc) (supply := supply)
          (bodySupply := procLayout.bodySupply)
          (dispatchSupply := procLayout.dispatchSupply)
          (sites := layout.sites)
          (site :=
            { procName := name
              token := Stmt.callToken supply
              returnLabel := LabelSupply.label supply 0 })
          (fuel := evalFuel + 1) (state := source)
          (outcome :=
            Outcome.regular
              (returned.withEVM { bodyState.evm with stack := stack }))
          (target := target) (tokens := tokens) (asm := layout.asm)
          (oracle := oracle) (cursor := cursor)
          (cursorFinal := cursorFinal)
          callSeg procSeg hCtxProcs hLookupCtx
          (fun {bodyFuel} hBodyFuelLt =>
            procBodyPreservesAtSegment_of_programLayout_withGasOracle
              (program := program) (layout := layout) (proc := evalProc)
              (bodySupply := procLayout.bodySupply)
              (dispatchSupply := procLayout.dispatchSupply)
              (fuel := bodyFuel) procSeg
              (blockPreservesInProgramLayoutWithGasOracleAtFuel_of_upTo
                (layout := layout) (maxFuel := maxFuel)
                (fuel := bodyFuel)
                (ctx := ProcedureCall.bodyCtx program evalProc)
                (supply := procLayout.bodySupply)
                (block := evalProc.body)
                (by omega)
                (hProcBodies hLookup))
              hProgramWF hBodyCalls)
          rfl
          (_root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.generated_callSite_mem_of_included
            (ctx := ctx) (supply := supply) (name := name)
            (proc := evalProc) (sites := layout.sites)
            hLookupCtx hCalls)
          layout.noDupTokens hProcWF.1 hProcWF.2.1 hPc hRel
          layout.exactLabels
          (Stmt.EvalWithGasOracle.call_leave hLookup hSplit hBody hPop
            hAttach)
  | call_halt hLookup hSplit hBody =>
      rename_i evalFuel evalProc args callerStack bodyState kind
      have hLookupCtx : ProcList.lookup? name ctx.procs = some evalProc := by
        simpa [hCtxProcs] using hLookup
      have hProcWF : Proc.WF evalProc :=
        Program.procWF_of_lookup? hProgramWF hLookup
      let procLayout := layout.procLayout hLookup
      let procSeg :
          CodeSegment layout.asm
            (ProcedureCall.procSegment program evalProc
              procLayout.bodySupply procLayout.dispatchSupply
              layout.sites) :=
        CodeSegment.cast_code
          (procSegment_eq_procedurePreservation
            (program := program) (proc := evalProc)
            (bodySupply := procLayout.bodySupply)
            (dispatchSupply := procLayout.dispatchSupply)
            (sites := layout.sites))
          procLayout.segment
      have hBodyCalls :
          CallsIncluded
            (Block.compileFromCtx evalProc.body
              (ProcedureCall.bodyCtx program evalProc)
              procLayout.bodySupply).calls
            layout.sites := by
        simpa [ProcedureCall.bodyCtx,
          _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.bodyCtx,
          procLayout] using procLayout.bodyCalls
      exact
        ProcedureCall.call_stmt_segments_withGasOracle
          (program := program) (ctx := ctx) (name := name)
          (proc := evalProc) (supply := supply)
          (bodySupply := procLayout.bodySupply)
          (dispatchSupply := procLayout.dispatchSupply)
          (sites := layout.sites)
          (site :=
            { procName := name
              token := Stmt.callToken supply
              returnLabel := LabelSupply.label supply 0 })
          (fuel := evalFuel + 1) (state := source)
          (outcome := Outcome.halt kind bodyState)
          (target := target) (tokens := tokens) (asm := layout.asm)
          (oracle := oracle) (cursor := cursor)
          (cursorFinal := cursorFinal)
          callSeg procSeg hCtxProcs hLookupCtx
          (fun {bodyFuel} hBodyFuelLt =>
            procBodyPreservesAtSegment_of_programLayout_withGasOracle
              (program := program) (layout := layout) (proc := evalProc)
              (bodySupply := procLayout.bodySupply)
              (dispatchSupply := procLayout.dispatchSupply)
              (fuel := bodyFuel) procSeg
              (blockPreservesInProgramLayoutWithGasOracleAtFuel_of_upTo
                (layout := layout) (maxFuel := maxFuel)
                (fuel := bodyFuel)
                (ctx := ProcedureCall.bodyCtx program evalProc)
                (supply := procLayout.bodySupply)
                (block := evalProc.body)
                (by omega)
                (hProcBodies hLookup))
              hProgramWF hBodyCalls)
          rfl
          (_root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.generated_callSite_mem_of_included
            (ctx := ctx) (supply := supply) (name := name)
            (proc := evalProc) (sites := layout.sites)
            hLookupCtx hCalls)
          layout.noDupTokens hProcWF.1 hProcWF.2.1 hPc hRel
          layout.exactLabels
          (Stmt.EvalWithGasOracle.call_halt hLookup hSplit hBody)

end ProcedureLayoutPreservation

private theorem evalWithGasOracle_modeAllowed_at_fuel
    {program : Program} {oracle : GasOracle} :
    ∀ fuel,
      (∀ {cursor cursorFinal : Nat} {block : Block}
          {source : RunState} {outcome : Outcome}
          {canBreak canContinue canLeave : Bool},
        Block.WF canBreak canContinue canLeave block →
          Block.EvalWithGasOracle program oracle fuel block cursor source
            outcome cursorFinal →
          ProofOutcome.ModeAllowed canBreak canContinue canLeave outcome) ∧
      (∀ {cursor cursorFinal : Nat} {stmt : Stmt}
          {source : RunState} {outcome : Outcome}
          {canBreak canContinue canLeave : Bool},
        Stmt.WF canBreak canContinue canLeave stmt →
          Stmt.EvalWithGasOracle program oracle fuel stmt cursor source
            outcome cursorFinal →
          ProofOutcome.ModeAllowed canBreak canContinue canLeave outcome) ∧
      (∀ {cursor cursorFinal : Nat} {cond : Code} {post body : Block}
          {source : RunState} {outcome : Outcome}
          {canBreak canContinue canLeave : Bool},
        Block.WF false false canLeave post →
          Block.WF true true canLeave body →
          For.EvalWithGasOracle program oracle fuel cond post body cursor
            source outcome cursorFinal →
          ProofOutcome.ModeAllowed canBreak canContinue canLeave outcome)
  | 0 => by
      refine ⟨?_, ?_, ?_⟩
      · intro cursor cursorFinal block source outcome canBreak canContinue
          canLeave hWF hEval
        cases hEval
      · intro cursor cursorFinal stmt source outcome canBreak canContinue
          canLeave hWF hEval
        cases hEval with
        | code hCode =>
            simp [ProofOutcome.ModeAllowed, Outcome.regular]
        | brk =>
            cases hWF with
            | brk hAllowed =>
                simpa [ProofOutcome.ModeAllowed, Outcome.brk] using hAllowed
        | cont =>
            cases hWF with
            | cont hAllowed =>
                simpa [ProofOutcome.ModeAllowed, Outcome.cont] using hAllowed
        | leave hReturns =>
            cases hWF with
            | leave hAllowed =>
                simpa [ProofOutcome.ModeAllowed, Outcome.leave] using hAllowed
        | terminal hStep =>
            simp [ProofOutcome.ModeAllowed, Outcome.halt]
      · intro cursor cursorFinal cond post body source outcome canBreak
          canContinue canLeave hPostWF hBodyWF hEval
        cases hEval
  | fuel + 1 => by
      rcases evalWithGasOracle_modeAllowed_at_fuel
          (program := program) (oracle := oracle) fuel with
        ⟨hBlockIH, hStmtIH, hForIH⟩
      refine ⟨?_, ?_, ?_⟩
      · intro cursor cursorFinal block source outcome canBreak canContinue
          canLeave hWF hEval
        cases hEval with
        | nil =>
            simp [ProofOutcome.ModeAllowed, Outcome.regular]
        | cons_regular hStmt hRest =>
            cases hWF with
            | cons hStmtWF hRestWF =>
                exact hBlockIH hRestWF hRest
        | cons_brk hStmt =>
            cases hWF with
            | cons hStmtWF _hRestWF =>
                exact hStmtIH hStmtWF hStmt
        | cons_cont hStmt =>
            cases hWF with
            | cons hStmtWF _hRestWF =>
                exact hStmtIH hStmtWF hStmt
        | cons_leave hStmt =>
            cases hWF with
            | cons hStmtWF _hRestWF =>
                exact hStmtIH hStmtWF hStmt
        | cons_halt hStmt =>
            cases hWF with
            | cons hStmtWF _hRestWF =>
                exact hStmtIH hStmtWF hStmt
      · intro cursor cursorFinal stmt source outcome canBreak canContinue
          canLeave hWF hEval
        cases hEval with
        | code hCode =>
            simp [ProofOutcome.ModeAllowed, Outcome.regular]
        | if_false hCond =>
            simp [ProofOutcome.ModeAllowed, Outcome.regular]
        | if_true hCond hBody =>
            cases hWF with
            | if_ hBodyWF =>
                exact hBlockIH hBodyWF hBody
        | switch_none hScrutinee hPop hSelect =>
            simp [ProofOutcome.ModeAllowed, Outcome.regular]
        | switch_some hScrutinee hPop hStateAfterPop hSelect hBody =>
            cases hWF with
            | switch hCasesWF hDefaultWF =>
                exact
                  hBlockIH (Switch.wf_of_select hCasesWF hDefaultWF hSelect)
                    hBody
        | for_init_regular hInit hLoop =>
            cases hWF with
            | for_ hInitWF hPostWF hBodyWF =>
                exact
                  hForIH (canBreak := canBreak) (canContinue := canContinue)
                    hPostWF hBodyWF hLoop
        | for_init_leave hInit =>
            cases hWF with
            | for_ hInitWF _hPostWF _hBodyWF =>
                have hAllowed := hBlockIH hInitWF hInit
                simpa [ProofOutcome.ModeAllowed, Outcome.leave] using hAllowed
        | for_init_halt hInit =>
            cases hWF with
            | for_ hInitWF _hPostWF _hBodyWF =>
                simp [ProofOutcome.ModeAllowed, Outcome.halt]
        | brk =>
            cases hWF with
            | brk hAllowed =>
                simpa [ProofOutcome.ModeAllowed, Outcome.brk] using hAllowed
        | cont =>
            cases hWF with
            | cont hAllowed =>
                simpa [ProofOutcome.ModeAllowed, Outcome.cont] using hAllowed
        | leave hReturns =>
            cases hWF with
            | leave hAllowed =>
                simpa [ProofOutcome.ModeAllowed, Outcome.leave] using hAllowed
        | call_regular hLookup hSplit hBody hPop hAttach =>
            simp [ProofOutcome.ModeAllowed, Outcome.regular]
        | call_leave hLookup hSplit hBody hPop hAttach =>
            simp [ProofOutcome.ModeAllowed, Outcome.regular]
        | call_halt hLookup hSplit hBody =>
            simp [ProofOutcome.ModeAllowed, Outcome.halt]
        | terminal hStep =>
            simp [ProofOutcome.ModeAllowed, Outcome.halt]
      · intro cursor cursorFinal cond post body source outcome canBreak
          canContinue canLeave hPostWF hBodyWF hEval
        cases hEval with
        | false hCond =>
            simp [ProofOutcome.ModeAllowed, Outcome.regular]
        | body_brk hCond hBody =>
            simp [ProofOutcome.ModeAllowed, Outcome.regular]
        | body_leave hCond hBody =>
            have hAllowed := hBlockIH hBodyWF hBody
            simpa [ProofOutcome.ModeAllowed, Outcome.leave] using hAllowed
        | body_halt hCond hBody =>
            simp [ProofOutcome.ModeAllowed, Outcome.halt]
        | regular_post_regular hCond hBody hPost hLoop =>
            exact hForIH hPostWF hBodyWF hLoop
        | cont_post_regular hCond hBody hPost hLoop =>
            exact hForIH hPostWF hBodyWF hLoop
        | regular_post_leave hCond hBody hPost =>
            have hAllowed := hBlockIH hPostWF hPost
            simpa [ProofOutcome.ModeAllowed, Outcome.leave] using hAllowed
        | cont_post_leave hCond hBody hPost =>
            have hAllowed := hBlockIH hPostWF hPost
            simpa [ProofOutcome.ModeAllowed, Outcome.leave] using hAllowed
        | regular_post_halt hCond hBody hPost =>
            simp [ProofOutcome.ModeAllowed, Outcome.halt]
        | cont_post_halt hCond hBody hPost =>
            simp [ProofOutcome.ModeAllowed, Outcome.halt]

theorem Block.EvalWithGasOracle.modeAllowed {program : Program}
    {oracle : GasOracle} {fuel cursor cursorFinal : Nat}
    {block : Block} {source : RunState} {outcome : Outcome}
    {canBreak canContinue canLeave : Bool}
    (hWF : Block.WF canBreak canContinue canLeave block)
    (hEval :
      Block.EvalWithGasOracle program oracle fuel block cursor source outcome
        cursorFinal) :
    ProofOutcome.ModeAllowed canBreak canContinue canLeave outcome :=
  (evalWithGasOracle_modeAllowed_at_fuel
      (program := program) (oracle := oracle) fuel).1 hWF hEval

theorem Stmt.EvalWithGasOracle.modeAllowed {program : Program}
    {oracle : GasOracle} {fuel cursor cursorFinal : Nat}
    {stmt : Stmt} {source : RunState} {outcome : Outcome}
    {canBreak canContinue canLeave : Bool}
    (hWF : Stmt.WF canBreak canContinue canLeave stmt)
    (hEval :
      Stmt.EvalWithGasOracle program oracle fuel stmt cursor source outcome
        cursorFinal) :
    ProofOutcome.ModeAllowed canBreak canContinue canLeave outcome :=
  (evalWithGasOracle_modeAllowed_at_fuel
      (program := program) (oracle := oracle) fuel).2.1 hWF hEval

theorem For.EvalWithGasOracle.modeAllowed {program : Program}
    {oracle : GasOracle} {fuel cursor cursorFinal : Nat}
    {cond : Code} {post body : Block} {source : RunState}
    {outcome : Outcome} {canBreak canContinue canLeave : Bool}
    (hPostWF : Block.WF false false canLeave post)
    (hBodyWF : Block.WF true true canLeave body)
    (hEval :
      For.EvalWithGasOracle program oracle fuel cond post body cursor source
        outcome cursorFinal) :
    ProofOutcome.ModeAllowed canBreak canContinue canLeave outcome :=
  (evalWithGasOracle_modeAllowed_at_fuel
      (program := program) (oracle := oracle) fuel).2.2 hPostWF hBodyWF hEval

theorem Program.wholeProgramSourceOutcome_of_evalWithGasOracle {program : Program}
    {oracle : GasOracle} {fuel cursor cursorFinal : Nat} {initial : EVMState}
    {outcome : Outcome}
    (hWF : program.WF)
    (hEval :
      Block.EvalWithGasOracle program oracle fuel program.body cursor
        (Program.initialState initial) outcome cursorFinal) :
    WholeProgramSourceOutcome outcome := by
  exact
    ProofOutcome.whole_of_modeAllowed_false
      (Block.EvalWithGasOracle.modeAllowed hWF.2.2.2.2 hEval)

namespace SwitchPreservation

def CasesPreserves (program : Program) (ctx : CompileContext)
    (endLabel : Assembly.Label) (base : LabelSupply) :
    LabelSupply → Nat → List (Word × Block) → Prop
  | _supply, _idx, [] => True
  | supply, idx, (_value, body) :: rest =>
      let compiledBody := Block.compileFromCtx body ctx supply
      BlockPreservesWithGasOracle program ctx supply body ∧
        CasesPreserves program ctx endLabel base compiledBody.next (idx + 1)
          rest

def DefaultPreserves (program : Program) (ctx : CompileContext)
    (supply : LabelSupply) : Option Block → Prop
  | none => True
  | some body => BlockPreservesWithGasOracle program ctx supply body

theorem casesPreserves_head {program : Program} {ctx : CompileContext}
    {endLabel : Assembly.Label} {base supply : LabelSupply} {idx : Nat}
    {value : Word} {body : Block} {rest : List (Word × Block)}
    (hCases :
      CasesPreserves program ctx endLabel base supply idx
        ((value, body) :: rest)) :
    BlockPreservesWithGasOracle program ctx supply body := by
  exact hCases.1

theorem casesPreserves_tail {program : Program} {ctx : CompileContext}
    {endLabel : Assembly.Label} {base supply : LabelSupply} {idx : Nat}
    {value : Word} {body : Block} {rest : List (Word × Block)}
    (hCases :
      CasesPreserves program ctx endLabel base supply idx
        ((value, body) :: rest)) :
    CasesPreserves program ctx endLabel base
      (Block.compileFromCtx body ctx supply).next (idx + 1) rest := by
  exact hCases.2

theorem defaultPreserves_some {program : Program} {ctx : CompileContext}
    {supply : LabelSupply} {body : Block}
    (hDefault :
      DefaultPreserves program ctx supply (some body)) :
    BlockPreservesWithGasOracle program ctx supply body := by
  exact hDefault

theorem casesPreserves_of_all {program : Program} {ctx : CompileContext}
    {endLabel : Assembly.Label} {base supply : LabelSupply} {idx : Nat}
    {cases : List (Word × Block)}
    (hAll :
      ∀ {bodySupply : LabelSupply} {value : Word} {body : Block},
        (value, body) ∈ cases →
          BlockPreservesWithGasOracle program ctx bodySupply body) :
    CasesPreserves program ctx endLabel base supply idx cases := by
  induction cases generalizing supply idx with
  | nil =>
      trivial
  | cons head rest ih =>
      rcases head with ⟨value, body⟩
      exact
        ⟨ hAll (bodySupply := supply) (value := value) (body := body)
            (by simp)
        , ih (supply := (Block.compileFromCtx body ctx supply).next)
            (idx := idx + 1) (by
              intro bodySupply value' body' hMem
              exact
                hAll (bodySupply := bodySupply) (value := value')
                  (body := body') (by simp [hMem])) ⟩

set_option linter.unusedSimpArgs false in
theorem switchTestCode_runWithGasOracle_eq_run
    (probe : Word) (oracle : GasOracle) (cursor : Nat) (state : EVMState) :
    Code.runWithGasOracle (Stmt.switchTestCode probe) oracle cursor state =
      (do
        let final ← Code.run (Stmt.switchTestCode probe) state
        pure (final, cursor)) := by
  simp [Stmt.switchTestCode, Code.runWithGasOracle, Code.run,
    BasicInstr.stepWithGasOracle, BasicOp.stepWithGasOracle,
    BasicInstr.step, BasicOp.step, BasicOp.toPrimOp,
    Assembly.Target.stepInstr,
    Assembly.GasParametric.Target.stepInstrWithGasOracle,
    Assembly.GasParametric.PrimOp.stepWithGasOracle,
    Bind.bind, Except.bind]
  cases hDup : Assembly.PrimOp.step .dup1 state <;>
    simp [pure, Except.pure]
  rename_i afterDup
  cases hEq :
      Assembly.PrimOp.step .eq
        (EvmYul.EVM.State.replaceStackAndIncrPC afterDup
          (afterDup.stack.push probe) 33) <;>
    simp [hEq, Bind.bind, Except.bind, pure, Except.pure]

theorem switchTestCode_runConditionStateWithGasOracle_of_plain
    {probe : Word} {oracle : GasOracle} {cursor : Nat}
    {source final : RunState} {cond : Bool}
    (hRun :
      Code.runConditionState (Stmt.switchTestCode probe) source =
        .ok (final, cond)) :
    Code.runConditionStateWithGasOracle (Stmt.switchTestCode probe) oracle
        cursor source =
      .ok (final, cond, cursor) := by
  unfold Code.runConditionStateWithGasOracle
  unfold EvmCompiler.Structured.Code.runConditionState at hRun
  unfold Code.runConditionWithGasOracle
  unfold EvmCompiler.Structured.Code.runCondition at hRun
  rw [switchTestCode_runWithGasOracle_eq_run]
  cases hCode : Code.run (Stmt.switchTestCode probe) source.evm with
  | error err =>
      rw [hCode] at hRun
      simp [Bind.bind, Except.bind] at hRun
  | ok evmAfterCode =>
      rw [hCode] at hRun
      simp [Bind.bind, Except.bind]
      cases hPop : Code.popCondition evmAfterCode with
      | error err =>
          simp [hPop, Bind.bind, Except.bind] at hRun ⊢
      | ok popResult =>
          rcases popResult with ⟨evmAfterPop, condAfterPop⟩
          simp [hPop, Bind.bind, Except.bind] at hRun ⊢
          rcases hRun with ⟨hFinal, hCond⟩
          cases hFinal
          cases hCond
          simp [hPop, pure, Except.pure]

theorem test_runConditionState_withGasOracle {source : RunState}
    {stack : EvmYul.Stack Word} {value probe : Word}
    (oracle : GasOracle) (cursor : Nat)
    (hPop : source.evm.stack.pop = some (stack, value)) :
    ∃ final,
      Code.runConditionStateWithGasOracle (Stmt.switchTestCode probe) oracle
          cursor source =
        .ok (final, probe = value, cursor) ∧
      final.returns = source.returns ∧
      final.evm.stack = source.evm.stack ∧
      eraseControl final.evm = eraseControl source.evm := by
  rcases EvmCompiler.Structured.Preservation.SwitchPreservation.test_runConditionState
      (source := source) (stack := stack) (value := value) (probe := probe)
      hPop with
    ⟨final, hRun, hReturns, hStack, hErase⟩
  exact
    ⟨ final
    , switchTestCode_runConditionStateWithGasOracle_of_plain
        (oracle := oracle) (cursor := cursor) hRun
    , hReturns, hStack, hErase
    ⟩

theorem test_jumpi_result_ctx_withGasOracle {pre post : Assembly.Program}
    {label : Assembly.Label} {dest : Nat}
    {source : RunState} {target : EVMState} {tokens : List Word}
    {stack : EvmYul.Stack Word} {value probe : Word}
    {oracle : GasOracle} {cursor : Nat}
    (hFits : Code.PCFitsFrom pre (Stmt.switchTestCode probe))
    (hPc : target.pc = Assembly.Program.pcAfter pre)
    (hRel : Frame.StateRel source target tokens)
    (hLabel :
      Assembly.Program.labelPc
          (pre ++ (Stmt.switchTestCode probe).toAssembly ++
            [Assembly.Instr.jumpi label] ++ post) label = some dest)
    (hPop : source.evm.stack.pop = some (stack, value)) :
    ARunResultWithGasOracle
      (pre ++ (Stmt.switchTestCode probe).toAssembly ++
        [Assembly.Instr.jumpi label] ++ post)
      oracle cursor target
      (fun result cursorFinal =>
        match result with
        | .running target' =>
            cursorFinal = cursor ∧
              Frame.StateRel source target' tokens ∧
                target'.pc =
                  if probe = value then
                    EvmYul.UInt256.ofNat dest
                  else
                    Assembly.Program.pcAfter
                      (pre ++ (Stmt.switchTestCode probe).toAssembly ++
                        [Assembly.Instr.jumpi label])
        | .halted _ => False) := by
  rcases test_runConditionState_withGasOracle
      (source := source) (stack := stack) (value := value) (probe := probe)
      oracle cursor hPop with
    ⟨final, hRun, hReturns, hStack, hErase⟩
  have hRunJump :=
    FrameStateRel.runCondition_jumpi_result_ctx_withGasOracle
      (source := source) (final := final) (target := target)
      (tokens := tokens) (cond := Stmt.switchTestCode probe)
      (label := label) (dest := dest) (pre := pre) (post := post)
      (condTrue := probe = value) (oracle := oracle) (cursor := cursor)
      (cursor' := cursor)
      (Code.runnerSafeWithGasOracle_of_runnerSafe
        (EvmCompiler.Structured.Preservation.Code.switchTestCode_runnerSafe
          probe))
      (Code.switchTestCode_frameSafeWithGasOracle probe)
      hFits hPc hRel hLabel hRun
  exact ARunResultWithGasOracle.mono hRunJump (by
    intro result cursorFinal hResult
    cases result with
    | halted halt =>
        cases hResult
    | running target' =>
        rcases hResult with ⟨hCursor, hFinalRel, hTargetPc⟩
        refine ⟨hCursor, ?_, ?_⟩
        · refine ⟨?_, ?_⟩
          · rw [← hStack, ← hReturns]
            exact hFinalRel.stackRel
          · calc
              eraseControl target'
                  = eraseControl { final.evm with stack := target'.stack } :=
                      hFinalRel.dataRel
              _ = eraseControl { source.evm with stack := target'.stack } := by
                      exact eraseControl_with_stack_congr hErase
        · simpa [Bool.decide_eq_true] using hTargetPc)

theorem test_true_result_ctx_withGasOracle {pre post : Assembly.Program}
    {label : Assembly.Label} {dest : Nat}
    {source : RunState} {target : EVMState} {tokens : List Word}
    {stack : EvmYul.Stack Word} {value probe : Word}
    {oracle : GasOracle} {cursor : Nat}
    (hEq : probe = value)
    (hFits : Code.PCFitsFrom pre (Stmt.switchTestCode probe))
    (hPc : target.pc = Assembly.Program.pcAfter pre)
    (hRel : Frame.StateRel source target tokens)
    (hLabel :
      Assembly.Program.labelPc
          (pre ++ (Stmt.switchTestCode probe).toAssembly ++
            [Assembly.Instr.jumpi label] ++ post) label = some dest)
    (hPop : source.evm.stack.pop = some (stack, value)) :
    ARunResultWithGasOracle
      (pre ++ (Stmt.switchTestCode probe).toAssembly ++
        [Assembly.Instr.jumpi label] ++ post)
      oracle cursor target
      (fun result cursorFinal =>
        match result with
        | .running target' =>
            cursorFinal = cursor ∧
              Frame.StateRel source target' tokens ∧
                target'.pc = EvmYul.UInt256.ofNat dest
        | .halted _ => False) := by
  exact ARunResultWithGasOracle.mono
    (test_jumpi_result_ctx_withGasOracle (pre := pre) (post := post)
      (label := label) (dest := dest) (source := source) (target := target)
      (tokens := tokens) (stack := stack) (value := value) (probe := probe)
      (oracle := oracle) (cursor := cursor)
      hFits hPc hRel hLabel hPop)
    (by
      intro result cursorFinal hResult
      cases result with
      | halted halt =>
          cases hResult
      | running target' =>
          simpa [hEq] using hResult)

theorem test_false_result_ctx_withGasOracle {pre post : Assembly.Program}
    {label : Assembly.Label} {dest : Nat}
    {source : RunState} {target : EVMState} {tokens : List Word}
    {stack : EvmYul.Stack Word} {value probe : Word}
    {oracle : GasOracle} {cursor : Nat}
    (hNe : probe ≠ value)
    (hFits : Code.PCFitsFrom pre (Stmt.switchTestCode probe))
    (hPc : target.pc = Assembly.Program.pcAfter pre)
    (hRel : Frame.StateRel source target tokens)
    (hLabel :
      Assembly.Program.labelPc
          (pre ++ (Stmt.switchTestCode probe).toAssembly ++
            [Assembly.Instr.jumpi label] ++ post) label = some dest)
    (hPop : source.evm.stack.pop = some (stack, value)) :
    ARunResultWithGasOracle
      (pre ++ (Stmt.switchTestCode probe).toAssembly ++
        [Assembly.Instr.jumpi label] ++ post)
      oracle cursor target
      (fun result cursorFinal =>
        match result with
        | .running target' =>
            cursorFinal = cursor ∧
              Frame.StateRel source target' tokens ∧
                target'.pc =
                  Assembly.Program.pcAfter
                    (pre ++ (Stmt.switchTestCode probe).toAssembly ++
                      [Assembly.Instr.jumpi label])
        | .halted _ => False) := by
  exact ARunResultWithGasOracle.mono
    (test_jumpi_result_ctx_withGasOracle (pre := pre) (post := post)
      (label := label) (dest := dest) (source := source) (target := target)
      (tokens := tokens) (stack := stack) (value := value) (probe := probe)
      (oracle := oracle) (cursor := cursor)
      hFits hPc hRel hLabel hPop)
    (by
      intro result cursorFinal hResult
      cases result with
      | halted halt =>
          cases hResult
      | running target' =>
          simpa [hNe] using hResult)

theorem tests_fallthrough_result_ctx_withGasOracle
    {base : LabelSupply} {idx : Nat}
    {cases : List (Word × Block)} {pre post : Assembly.Program}
    {source : RunState} {target : EVMState} {tokens : List Word}
    {stack : EvmYul.Stack Word} {value : Word}
    {oracle : GasOracle} {cursor : Nat}
    (hFits : AssemblyProgram.PCFitsFrom pre (Stmt.switchTests base idx cases))
    (hResolve :
      EvmCompiler.Structured.Preservation.SwitchPreservation.TestsLabelsResolve
        (pre ++ Stmt.switchTests base idx cases ++ post)
        base idx cases)
    (hNoMatch : ∀ probe body, (probe, body) ∈ cases → probe ≠ value)
    (hPc : target.pc = Assembly.Program.pcAfter pre)
    (hRel : Frame.StateRel source target tokens)
    (hPop : source.evm.stack.pop = some (stack, value)) :
    ARunResultWithGasOracle (pre ++ Stmt.switchTests base idx cases ++ post)
      oracle cursor target
      (fun result cursorFinal =>
        match result with
        | .running target' =>
            cursorFinal = cursor ∧
              Frame.StateRel source target' tokens ∧
                target'.pc =
                  Assembly.Program.pcAfter
                    (pre ++ Stmt.switchTests base idx cases)
        | .halted _ => False) := by
  induction cases generalizing idx pre target cursor with
  | nil =>
      refine ARunResultWithGasOracle.pure ?_
      exact
        ⟨ rfl
        , by
            simpa [Stmt.switchTests] using And.intro hRel hPc
        ⟩
  | cons head rest ih =>
      rcases head with ⟨probe, body⟩
      let label := LabelSupply.label base (idx + 2)
      let testCode := Stmt.switchTest base idx probe
      let restCode := Stmt.switchTests base (idx + 1) rest
      have hFitsFull :
          AssemblyProgram.PCFitsFrom pre (testCode ++ restCode) := by
        simpa [Stmt.switchTests, Stmt.switchTest, label, testCode, restCode,
          List.append_assoc] using hFits
      have hTestFitsAsm : AssemblyProgram.PCFitsFrom pre testCode :=
        AssemblyProgram.PCFitsFrom.left (pre := pre) (first := testCode)
          (second := restCode) hFitsFull
      have hRestFits : AssemblyProgram.PCFitsFrom (pre ++ testCode) restCode :=
        AssemblyProgram.PCFitsFrom.right (pre := pre) (first := testCode)
          (second := restCode) hFitsFull
      have hCondFitsAsm :
          AssemblyProgram.PCFitsFrom pre
            (Stmt.switchTestCode probe).toAssembly :=
        AssemblyProgram.PCFitsFrom.left (pre := pre)
          (first := (Stmt.switchTestCode probe).toAssembly)
          (second := [Assembly.Instr.jumpi label])
          (by simpa [Stmt.switchTest, label, testCode] using hTestFitsAsm)
      have hCondFits : Code.PCFitsFrom pre (Stmt.switchTestCode probe) :=
        Code.PCFitsFrom.of_assembly hCondFitsAsm
      rcases hResolve with ⟨hHeadLabelExists, hTailResolve⟩
      rcases hHeadLabelExists with ⟨dest, hHeadLabel⟩
      have hHeadLabel' :
          Assembly.Program.labelPc
              (pre ++ (Stmt.switchTestCode probe).toAssembly ++
                [Assembly.Instr.jumpi label] ++ (restCode ++ post)) label =
            some dest := by
        simpa [Stmt.switchTests, Stmt.switchTest, label, testCode, restCode,
          List.append_assoc] using hHeadLabel
      have hProbeNe : probe ≠ value :=
        hNoMatch probe body (by simp)
      have hHeadRun :=
        test_false_result_ctx_withGasOracle
          (pre := pre) (post := restCode ++ post)
          (label := label) (dest := dest) (source := source)
          (target := target) (tokens := tokens) (stack := stack)
          (value := value) (probe := probe)
          (oracle := oracle) (cursor := cursor)
          hProbeNe hCondFits hPc hRel hHeadLabel' hPop
      refine
        ARunResultWithGasOracle.bind_running
          (program :=
            pre ++ Stmt.switchTests base idx ((probe, body) :: rest) ++ post)
          (middle := fun targetAfterHead cursorAfterHead =>
            cursorAfterHead = cursor ∧
              Frame.StateRel source targetAfterHead tokens ∧
                targetAfterHead.pc =
                  Assembly.Program.pcAfter (pre ++ testCode))
          ?_ ?_
      · simpa [Stmt.switchTests, Stmt.switchTest, label, testCode, restCode,
          List.append_assoc] using hHeadRun
      · intro targetAfterHead cursorAfterHead hAfterHead
        rcases hAfterHead with
          ⟨hCursorAfterHead, hRelAfterHead, hPcAfterHead⟩
        subst cursorAfterHead
        have hTailNoMatch :
            ∀ probe' body', (probe', body') ∈ rest → probe' ≠ value := by
          intro probe' body' hMem
          exact hNoMatch probe' body' (by simp [hMem])
        have hTailResolve' :
            EvmCompiler.Structured.Preservation.SwitchPreservation.TestsLabelsResolve
              ((pre ++ testCode) ++ restCode ++ post)
              base (idx + 1) rest := by
          simpa [Stmt.switchTests, Stmt.switchTest, label, testCode, restCode,
            List.append_assoc] using hTailResolve
        have hTailRun :=
          ih (idx := idx + 1) (pre := pre ++ testCode)
            (target := targetAfterHead) (cursor := cursor)
            hRestFits hTailResolve' hTailNoMatch hPcAfterHead
            hRelAfterHead
        exact ARunResultWithGasOracle.mono
          (by
            simpa [Stmt.switchTests, Stmt.switchTest, label, testCode,
              restCode, List.append_assoc] using hTailRun)
          (by
            intro result cursorFinal hResult
            cases result with
            | halted halt =>
                cases hResult
            | running target' =>
                simpa [Stmt.switchTests, Stmt.switchTest, label, testCode,
                  restCode, List.append_assoc] using hResult)

theorem default_none_tail_result_ctx_withGasOracle
    {pre between post : Assembly.Program}
    {defaultLabel endLabel : Assembly.Label}
    {source : RunState} {target : EVMState} {tokens : List Word}
    {stack : EvmYul.Stack Word} {value : Word}
    {oracle : GasOracle} {cursor : Nat}
    (hFitJumpDefault : PCFits pre)
    (hFitDefaultLabel :
      PCFits (pre ++ [Assembly.Instr.jump defaultLabel] ++ between))
    (hFitPop :
      PCFits (pre ++ [Assembly.Instr.jump defaultLabel] ++ between ++
        [Assembly.Instr.label defaultLabel]))
    (hFitJumpEnd :
      PCFits (pre ++ [Assembly.Instr.jump defaultLabel] ++ between ++
        [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop]))
    (hFitEndLabel :
      PCFits (pre ++ [Assembly.Instr.jump defaultLabel] ++ between ++
        [ Assembly.Instr.label defaultLabel
        , Assembly.Instr.prim .pop
        , Assembly.Instr.jump endLabel ]))
    (hPc : target.pc = Assembly.Program.pcAfter pre)
    (hRel : Frame.StateRel source target tokens)
    (hDefaultLabel :
      Assembly.Program.labelPc
          (pre ++ [Assembly.Instr.jump defaultLabel] ++ between ++
            [ Assembly.Instr.label defaultLabel
            , Assembly.Instr.prim .pop
            , Assembly.Instr.jump endLabel
            , Assembly.Instr.label endLabel ] ++ post)
          defaultLabel =
        some
          (Assembly.Program.byteLength
            (pre ++ [Assembly.Instr.jump defaultLabel] ++ between)))
    (hEndLabel :
      Assembly.Program.labelPc
          (pre ++ [Assembly.Instr.jump defaultLabel] ++ between ++
            [ Assembly.Instr.label defaultLabel
            , Assembly.Instr.prim .pop
            , Assembly.Instr.jump endLabel
            , Assembly.Instr.label endLabel ] ++ post)
          endLabel =
        some
          (Assembly.Program.byteLength
            (pre ++ [Assembly.Instr.jump defaultLabel] ++ between ++
              [ Assembly.Instr.label defaultLabel
              , Assembly.Instr.prim .pop
              , Assembly.Instr.jump endLabel ])))
    (hPop : source.evm.stack.pop = some (stack, value)) :
    ARunResultWithGasOracle
      (pre ++ [Assembly.Instr.jump defaultLabel] ++ between ++
        [ Assembly.Instr.label defaultLabel
        , Assembly.Instr.prim .pop
        , Assembly.Instr.jump endLabel
        , Assembly.Instr.label endLabel ] ++ post)
      oracle cursor target
      (fun result cursorFinal =>
        match result with
        | .running target' =>
            cursorFinal = cursor ∧
              Frame.StateRel
                (source.withEVM { source.evm with stack := stack })
                target' tokens ∧
              target'.pc =
                Assembly.Program.pcAfter
                  (pre ++ [Assembly.Instr.jump defaultLabel] ++ between ++
                    [ Assembly.Instr.label defaultLabel
                    , Assembly.Instr.prim .pop
                    , Assembly.Instr.jump endLabel
                    , Assembly.Instr.label endLabel ])
        | .halted _ => False) := by
  let preDefault : Assembly.Program :=
    pre ++ [Assembly.Instr.jump defaultLabel] ++ between ++
      [Assembly.Instr.label defaultLabel]
  let preAfterPop : Assembly.Program :=
    preDefault ++ [Assembly.Instr.prim .pop]
  have hDefaultRun :=
    FrameStateRel.jump_then_label_runResult_at_withGasOracle
      (label := defaultLabel) (pre := pre) (between := between)
      (post :=
        [ Assembly.Instr.prim .pop
        , Assembly.Instr.jump endLabel
        , Assembly.Instr.label endLabel ] ++ post)
      (oracle := oracle) (cursor := cursor)
      hFitJumpDefault
      (by simpa [List.append_assoc] using hFitDefaultLabel)
      hPc hRel
      (by simpa [List.append_assoc] using hDefaultLabel)
  refine
    ARunResultWithGasOracle.bind_running
      (program :=
        pre ++ [Assembly.Instr.jump defaultLabel] ++ between ++
          [ Assembly.Instr.label defaultLabel
          , Assembly.Instr.prim .pop
          , Assembly.Instr.jump endLabel
          , Assembly.Instr.label endLabel ] ++ post)
      (middle := fun targetAtDefault cursorAtDefault =>
        cursorAtDefault = cursor ∧
          Frame.StateRel source targetAtDefault tokens ∧
            targetAtDefault.pc = Assembly.Program.pcAfter preDefault)
      ?_ ?_
  · simpa [preDefault, List.append_assoc] using hDefaultRun
  · intro targetAtDefault cursorAtDefault hAtDefault
    rcases hAtDefault with ⟨hCursorAtDefault, hRelAtDefault, hPcAtDefault⟩
    subst cursorAtDefault
    rcases FrameStateRel.pop_stepResult_at_withGasOracle
        (pre := preDefault)
        (post :=
          [Assembly.Instr.jump endLabel, Assembly.Instr.label endLabel] ++ post)
        (source := source) (target := targetAtDefault) (tokens := tokens)
        (stack := stack) (value := value)
        (oracle := oracle) (cursor := cursor)
        (by simpa [preDefault, List.append_assoc] using hFitPop)
        hPcAtDefault hRelAtDefault hPop with
      ⟨targetAfterPop, hPopStep, hRelAfterPop, hPcAfterPop⟩
    have hPopRun :
        ARunResultWithGasOracle
          (preDefault ++ [Assembly.Instr.prim .pop] ++
            ([Assembly.Instr.jump endLabel, Assembly.Instr.label endLabel] ++
              post))
          oracle cursor targetAtDefault
          (fun result cursorAfterPop =>
            match result with
            | .running targetAfterPop' =>
                cursorAfterPop = cursor ∧
                  Frame.StateRel
                    (source.withEVM { source.evm with stack := stack })
                    targetAfterPop' tokens ∧
                    targetAfterPop'.pc =
                      Assembly.Program.pcAfter preAfterPop
            | .halted _ => False) := by
      refine ⟨1, .running targetAfterPop, cursor, ?_, ?_⟩
      · unfold Assembly.GasParametric.sourceRunNResultWithGasOracle
        rw [hPopStep]
        rfl
      · exact
          ⟨rfl, hRelAfterPop,
            by simpa [preAfterPop, List.append_assoc] using hPcAfterPop⟩
    refine
      ARunResultWithGasOracle.bind_running
        (program :=
          pre ++ [Assembly.Instr.jump defaultLabel] ++ between ++
            [ Assembly.Instr.label defaultLabel
            , Assembly.Instr.prim .pop
            , Assembly.Instr.jump endLabel
            , Assembly.Instr.label endLabel ] ++ post)
        (middle := fun targetAfterPop cursorAfterPop =>
          cursorAfterPop = cursor ∧
            Frame.StateRel
              (source.withEVM { source.evm with stack := stack })
              targetAfterPop tokens ∧
              targetAfterPop.pc = Assembly.Program.pcAfter preAfterPop)
        ?_ ?_
    · simpa [preDefault, preAfterPop, List.append_assoc] using hPopRun
    · intro targetAfterPop cursorAfterPop hAfterPop
      rcases hAfterPop with ⟨hCursorAfterPop, hRelAfterPop', hPcAfterPop'⟩
      subst cursorAfterPop
      have hEndRun :=
        FrameStateRel.jump_then_label_runResult_at_withGasOracle
          (label := endLabel) (pre := preAfterPop) (between := [])
          (post := post) (oracle := oracle) (cursor := cursor)
          (by
            simpa [preAfterPop, preDefault, List.append_assoc]
              using hFitJumpEnd)
          (by
            simpa [preAfterPop, preDefault, List.append_assoc]
              using hFitEndLabel)
          hPcAfterPop' hRelAfterPop'
          (by
            simpa [preAfterPop, preDefault, List.append_assoc]
              using hEndLabel)
      exact ARunResultWithGasOracle.mono
        (by
          simpa [preDefault, preAfterPop, List.append_assoc] using hEndRun)
        (by
          intro result cursorFinal hResult
          cases result with
          | halted halt =>
              cases hResult
          | running target' =>
              simpa [preDefault, preAfterPop, List.append_assoc] using hResult)

theorem default_some_tail_result_ctx_withGasOracle {program : Program}
    {ctx : CompileContext} {bodySupply : LabelSupply} {body : Block}
    {pre between post : Assembly.Program}
    {defaultLabel endLabel : Assembly.Label}
    {fuel : Nat} {source : RunState} {outcome : Outcome}
    {target : EVMState} {tokens : List Word}
    {stack : EvmYul.Stack Word} {value : Word}
    {oracle : GasOracle} {cursor cursorFinal : Nat}
    (hBody : BlockPreservesWithGasOracle program ctx bodySupply body)
    (hFitJumpDefault : PCFits pre)
    (hFitDefaultLabel :
      PCFits (pre ++ [Assembly.Instr.jump defaultLabel] ++ between))
    (hFitPop :
      PCFits (pre ++ [Assembly.Instr.jump defaultLabel] ++ between ++
        [Assembly.Instr.label defaultLabel]))
    (hBodyFits :
      AssemblyProgram.PCFitsFrom
        (pre ++ [Assembly.Instr.jump defaultLabel] ++ between ++
          [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop])
        (Block.compileFromCtx body ctx bodySupply).code)
    (hFitJumpEnd :
      PCFits
        (pre ++ [Assembly.Instr.jump defaultLabel] ++ between ++
          [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop] ++
          (Block.compileFromCtx body ctx bodySupply).code))
    (hFitEndLabel :
      PCFits
        (pre ++ [Assembly.Instr.jump defaultLabel] ++ between ++
          [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop] ++
          (Block.compileFromCtx body ctx bodySupply).code ++
          [Assembly.Instr.jump endLabel]))
    (hBodyResolve :
      ContextLabelsResolve
        (pre ++ [Assembly.Instr.jump defaultLabel] ++ between ++
          [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop] ++
          (Block.compileFromCtx body ctx bodySupply).code ++
          ([Assembly.Instr.jump endLabel, Assembly.Instr.label endLabel] ++
            post))
        ctx)
    (hBodyExact :
      ExactLabels
        (pre ++ [Assembly.Instr.jump defaultLabel] ++ between ++
          [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop] ++
          (Block.compileFromCtx body ctx bodySupply).code ++
          ([Assembly.Instr.jump endLabel, Assembly.Instr.label endLabel] ++
            post)))
    (hDefaultLabel :
      Assembly.Program.labelPc
          (pre ++ [Assembly.Instr.jump defaultLabel] ++ between ++
            [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop] ++
            (Block.compileFromCtx body ctx bodySupply).code ++
            [Assembly.Instr.jump endLabel, Assembly.Instr.label endLabel] ++
            post)
          defaultLabel =
        some
          (Assembly.Program.byteLength
            (pre ++ [Assembly.Instr.jump defaultLabel] ++ between)))
    (hEndLabel :
      Assembly.Program.labelPc
          (pre ++ [Assembly.Instr.jump defaultLabel] ++ between ++
            [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop] ++
            (Block.compileFromCtx body ctx bodySupply).code ++
            [Assembly.Instr.jump endLabel, Assembly.Instr.label endLabel] ++
            post)
          endLabel =
        some
          (Assembly.Program.byteLength
            (pre ++ [Assembly.Instr.jump defaultLabel] ++ between ++
              [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop] ++
              (Block.compileFromCtx body ctx bodySupply).code ++
              [Assembly.Instr.jump endLabel])))
    (hPc : target.pc = Assembly.Program.pcAfter pre)
    (hRel : Frame.StateRel source target tokens)
    (hPop : source.evm.stack.pop = some (stack, value))
    (hBodyEval :
      Block.EvalWithGasOracle program oracle fuel body cursor
        (source.withEVM { source.evm with stack := stack }) outcome
        cursorFinal) :
    ARunResultWithGasOracle
      (pre ++ [Assembly.Instr.jump defaultLabel] ++ between ++
        [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop] ++
        (Block.compileFromCtx body ctx bodySupply).code ++
        [Assembly.Instr.jump endLabel, Assembly.Instr.label endLabel] ++ post)
      oracle cursor target
      (fun result targetCursorFinal =>
        targetCursorFinal = cursorFinal ∧
          CompiledOutcomeRel
            (pre ++ [Assembly.Instr.jump defaultLabel] ++ between ++
              [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop] ++
              (Block.compileFromCtx body ctx bodySupply).code ++
              [Assembly.Instr.jump endLabel, Assembly.Instr.label endLabel] ++
              post)
            ctx
            (Assembly.Program.pcAfter
              (pre ++ [Assembly.Instr.jump defaultLabel] ++ between ++
                [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop] ++
                (Block.compileFromCtx body ctx bodySupply).code ++
                [Assembly.Instr.jump endLabel, Assembly.Instr.label endLabel]))
            outcome result tokens) := by
  let preDefault : Assembly.Program :=
    pre ++ [Assembly.Instr.jump defaultLabel] ++ between ++
      [Assembly.Instr.label defaultLabel]
  let preBody : Assembly.Program :=
    preDefault ++ [Assembly.Instr.prim .pop]
  let compiledBody := Block.compileFromCtx body ctx bodySupply
  let preAfterBody : Assembly.Program := preBody ++ compiledBody.code
  have hDefaultRun :=
    FrameStateRel.jump_then_label_runResult_at_withGasOracle
      (label := defaultLabel) (pre := pre) (between := between)
      (post :=
        [Assembly.Instr.prim .pop] ++ compiledBody.code ++
          [Assembly.Instr.jump endLabel, Assembly.Instr.label endLabel] ++ post)
      (oracle := oracle) (cursor := cursor)
      hFitJumpDefault
      (by simpa [List.append_assoc] using hFitDefaultLabel)
      hPc hRel
      (by
        simpa [compiledBody, List.append_assoc] using hDefaultLabel)
  refine
    ARunResultWithGasOracle.bind_running
      (program :=
        pre ++ [Assembly.Instr.jump defaultLabel] ++ between ++
          [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop] ++
          compiledBody.code ++
          [Assembly.Instr.jump endLabel, Assembly.Instr.label endLabel] ++ post)
      (middle := fun targetAtDefault cursorAtDefault =>
        cursorAtDefault = cursor ∧
          Frame.StateRel source targetAtDefault tokens ∧
            targetAtDefault.pc = Assembly.Program.pcAfter preDefault)
      ?_ ?_
  · exact ARunResultWithGasOracle.mono
      (by simpa [preDefault, compiledBody, List.append_assoc] using hDefaultRun)
      (by
        intro result cursorAtDefault hResult
        cases result with
        | halted halt =>
            cases hResult
        | running targetAtDefault =>
            simpa [preDefault] using hResult)
  · intro targetAtDefault cursorAtDefault hAtDefault
    rcases hAtDefault with ⟨hCursorAtDefault, hRelAtDefault, hPcAtDefault⟩
    subst cursorAtDefault
    rcases FrameStateRel.pop_stepResult_at_withGasOracle
        (pre := preDefault)
        (post :=
          compiledBody.code ++
            [Assembly.Instr.jump endLabel, Assembly.Instr.label endLabel] ++ post)
        (source := source) (target := targetAtDefault) (tokens := tokens)
        (stack := stack) (value := value)
        (oracle := oracle) (cursor := cursor)
        (by simpa [preDefault, List.append_assoc] using hFitPop)
        hPcAtDefault hRelAtDefault hPop with
      ⟨targetAfterPop, hPopStep, hRelAfterPop, hPcAfterPop⟩
    have hPopRun :
        ARunResultWithGasOracle
          (preDefault ++ [Assembly.Instr.prim .pop] ++
            (compiledBody.code ++
              [Assembly.Instr.jump endLabel, Assembly.Instr.label endLabel] ++
                post))
          oracle cursor targetAtDefault
          (fun result cursorAfterPop =>
            match result with
            | .running targetAfterPop' =>
                cursorAfterPop = cursor ∧
                  Frame.StateRel
                    (source.withEVM { source.evm with stack := stack })
                    targetAfterPop' tokens ∧
                    targetAfterPop'.pc = Assembly.Program.pcAfter preBody
            | .halted _ => False) := by
      refine ⟨1, .running targetAfterPop, cursor, ?_, ?_⟩
      · unfold Assembly.GasParametric.sourceRunNResultWithGasOracle
        rw [hPopStep]
        rfl
      · exact
          ⟨rfl, hRelAfterPop,
            by simpa [preBody, List.append_assoc] using hPcAfterPop⟩
    refine
      ARunResultWithGasOracle.bind_running
        (program :=
          pre ++ [Assembly.Instr.jump defaultLabel] ++ between ++
            [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop] ++
            compiledBody.code ++
            [Assembly.Instr.jump endLabel, Assembly.Instr.label endLabel] ++
              post)
        (middle := fun targetAfterPop cursorAfterPop =>
          cursorAfterPop = cursor ∧
            Frame.StateRel
              (source.withEVM { source.evm with stack := stack })
              targetAfterPop tokens ∧
              targetAfterPop.pc = Assembly.Program.pcAfter preBody)
        ?_ ?_
    · simpa [preDefault, preBody, compiledBody, List.append_assoc]
        using hPopRun
    · intro targetAfterPop cursorAfterPop hAfterPop
      rcases hAfterPop with ⟨hCursorAfterPop, hRelAfterPop', hPcAfterPop'⟩
      subst cursorAfterPop
      have hBodyRun :=
        hBody (pre := preBody)
          (post := [Assembly.Instr.jump endLabel,
            Assembly.Instr.label endLabel] ++ post)
          (fuel := fuel)
          (source := source.withEVM { source.evm with stack := stack })
          (outcome := outcome)
          (target := targetAfterPop) (tokens := tokens)
          (oracle := oracle) (cursor := cursor) (cursorFinal := cursorFinal)
          (by
            simpa [preDefault, preBody, compiledBody, List.append_assoc]
              using hBodyFits)
          (by
            simpa [preDefault, preBody, compiledBody, List.append_assoc]
              using hBodyResolve)
          (by
            simpa [preDefault, preBody, compiledBody, List.append_assoc]
              using hBodyExact)
          hPcAfterPop' hRelAfterPop' hBodyEval
      cases outcome with
      | mk outState outMode =>
          cases outMode with
          | regular =>
              have hBodyRegular :
                  ARunResultWithGasOracle
                    (preBody ++ compiledBody.code ++
                      ([Assembly.Instr.jump endLabel,
                        Assembly.Instr.label endLabel] ++ post))
                    oracle cursor targetAfterPop
                    (fun result targetCursorBeforeEnd =>
                      match result with
                      | .running targetBeforeEnd =>
                          targetCursorBeforeEnd = cursorFinal ∧
                            Frame.StateRel outState targetBeforeEnd tokens ∧
                              targetBeforeEnd.pc =
                                Assembly.Program.pcAfter preAfterBody
                      | .halted _ => False) := by
                exact ARunResultWithGasOracle.mono hBodyRun (by
                  intro result targetCursorBeforeEnd hResult
                  cases result with
                  | halted halt =>
                      cases hResult.2
                  | running targetBeforeEnd =>
                      rcases hResult with ⟨hCursorBeforeEnd, hCompiled⟩
                      exact
                        ⟨hCursorBeforeEnd, by
                          simpa [CompiledOutcomeRel, Outcome.regular,
                            preAfterBody, List.append_assoc] using hCompiled⟩)
              refine
                ARunResultWithGasOracle.bind_running
                  (program :=
                    pre ++ [Assembly.Instr.jump defaultLabel] ++ between ++
                      [ Assembly.Instr.label defaultLabel
                      , Assembly.Instr.prim .pop ] ++
                      compiledBody.code ++
                      [ Assembly.Instr.jump endLabel
                      , Assembly.Instr.label endLabel ] ++ post)
                  (middle := fun targetBeforeEnd targetCursorBeforeEnd =>
                    targetCursorBeforeEnd = cursorFinal ∧
                      Frame.StateRel outState targetBeforeEnd tokens ∧
                        targetBeforeEnd.pc =
                          Assembly.Program.pcAfter preAfterBody)
                  ?_ ?_
              · simpa [preDefault, preBody, preAfterBody, compiledBody,
                  List.append_assoc] using hBodyRegular
              · intro targetBeforeEnd targetCursorBeforeEnd hBeforeEnd
                rcases hBeforeEnd with
                  ⟨hCursorBeforeEnd, hRelBeforeEnd, hPcBeforeEnd⟩
                subst targetCursorBeforeEnd
                have hEndRun :=
                  FrameStateRel.jump_then_label_runResult_at_withGasOracle
                    (label := endLabel) (pre := preAfterBody)
                    (between := []) (post := post)
                    (oracle := oracle) (cursor := cursorFinal)
                    (by
                      simpa [preAfterBody, preBody, preDefault,
                        compiledBody, List.append_assoc] using hFitJumpEnd)
                    (by
                      simpa [preAfterBody, preBody, preDefault,
                        compiledBody, List.append_assoc] using hFitEndLabel)
                    hPcBeforeEnd hRelBeforeEnd
                    (by
                      simpa [preAfterBody, preBody, preDefault,
                        compiledBody, List.append_assoc] using hEndLabel)
                exact ARunResultWithGasOracle.mono
                  (by
                    simpa [preAfterBody, preBody, preDefault, compiledBody,
                      List.append_assoc] using hEndRun)
                  (by
                    intro result targetCursorFinal hResult
                    cases result with
                    | halted halt =>
                        cases hResult
                    | running targetFinal =>
                        rcases hResult with
                          ⟨hCursorEnd, hTargetRel, hTargetPc⟩
                        exact
                          ⟨hCursorEnd, by
                            simpa [preAfterBody, preBody, preDefault,
                              compiledBody, CompiledOutcomeRel,
                              Outcome.regular, List.append_assoc]
                              using And.intro hTargetRel hTargetPc⟩)
          | brk =>
              exact ARunResultWithGasOracle.mono
                (by
                  simpa [preDefault, preBody, compiledBody, List.append_assoc]
                    using hBodyRun)
                (by
                  intro result targetCursor hResult
                  rcases hResult with ⟨hCursor, hCompiled⟩
                  cases result with
                  | running target' =>
                      exact
                        ⟨hCursor, by
                          simpa [preDefault, preBody, compiledBody,
                            CompiledOutcomeRel, Outcome.brk, List.append_assoc]
                            using hCompiled⟩
                  | halted halt =>
                      cases hCompiled)
          | cont =>
              exact ARunResultWithGasOracle.mono
                (by
                  simpa [preDefault, preBody, compiledBody, List.append_assoc]
                    using hBodyRun)
                (by
                  intro result targetCursor hResult
                  rcases hResult with ⟨hCursor, hCompiled⟩
                  cases result with
                  | running target' =>
                      exact
                        ⟨hCursor, by
                          simpa [preDefault, preBody, compiledBody,
                            CompiledOutcomeRel, Outcome.cont, List.append_assoc]
                            using hCompiled⟩
                  | halted halt =>
                      cases hCompiled)
          | leave =>
              exact ARunResultWithGasOracle.mono
                (by
                  simpa [preDefault, preBody, compiledBody, List.append_assoc]
                    using hBodyRun)
                (by
                  intro result targetCursor hResult
                  rcases hResult with ⟨hCursor, hCompiled⟩
                  cases result with
                  | running target' =>
                      exact
                        ⟨hCursor, by
                          simpa [preDefault, preBody, compiledBody,
                            CompiledOutcomeRel, Outcome.leave, List.append_assoc]
                            using hCompiled⟩
                  | halted halt =>
                      cases hCompiled)
          | halt kind =>
              exact ARunResultWithGasOracle.mono
                (by
                  simpa [preDefault, preBody, compiledBody, List.append_assoc]
                    using hBodyRun)
                (by
                  intro result targetCursor hResult
                  rcases hResult with ⟨hCursor, hCompiled⟩
                  cases result with
                  | running target' =>
                      cases hCompiled
                  | halted halt =>
                      exact
                        ⟨hCursor, by
                          simpa [preDefault, preBody, compiledBody,
                            CompiledOutcomeRel, Outcome.halt, List.append_assoc]
                            using hCompiled⟩)

theorem default_selected_tail_result_ctx_withGasOracle {program : Program}
    {ctx : CompileContext} {bodySupply : LabelSupply} {body : Block}
    {pre between post : Assembly.Program}
    {defaultLabel endLabel : Assembly.Label}
    {fuel : Nat} {source : RunState} {outcome : Outcome}
    {target : EVMState} {tokens : List Word}
    {stack : EvmYul.Stack Word} {value : Word}
    {oracle : GasOracle} {cursor cursorFinal : Nat}
    (hBody : BlockPreservesWithGasOracle program ctx bodySupply body)
    (hFits :
      AssemblyProgram.PCFitsFrom pre
        ([Assembly.Instr.jump defaultLabel] ++ between ++
          [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop] ++
          (Block.compileFromCtx body ctx bodySupply).code ++
          [Assembly.Instr.jump endLabel, Assembly.Instr.label endLabel]))
    (hResolve :
      ContextLabelsResolve
        (pre ++
          ([Assembly.Instr.jump defaultLabel] ++ between ++
            [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop] ++
            (Block.compileFromCtx body ctx bodySupply).code ++
            [Assembly.Instr.jump endLabel, Assembly.Instr.label endLabel]) ++
          post)
        ctx)
    (hExact :
      ExactLabels
        (pre ++
          ([Assembly.Instr.jump defaultLabel] ++ between ++
            [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop] ++
            (Block.compileFromCtx body ctx bodySupply).code ++
            [Assembly.Instr.jump endLabel, Assembly.Instr.label endLabel]) ++
          post))
    (hPc : target.pc = Assembly.Program.pcAfter pre)
    (hRel : Frame.StateRel source target tokens)
    (hPop : source.evm.stack.pop = some (stack, value))
    (hBodyEval :
      Block.EvalWithGasOracle program oracle fuel body cursor
        (source.withEVM { source.evm with stack := stack }) outcome
        cursorFinal) :
    ARunResultWithGasOracle
      (pre ++
        ([Assembly.Instr.jump defaultLabel] ++ between ++
          [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop] ++
          (Block.compileFromCtx body ctx bodySupply).code ++
          [Assembly.Instr.jump endLabel, Assembly.Instr.label endLabel]) ++
        post)
      oracle cursor target
      (fun result targetCursorFinal =>
        targetCursorFinal = cursorFinal ∧
          CompiledOutcomeRel
            (pre ++
              ([Assembly.Instr.jump defaultLabel] ++ between ++
                [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop] ++
                (Block.compileFromCtx body ctx bodySupply).code ++
                [Assembly.Instr.jump endLabel, Assembly.Instr.label endLabel]) ++
              post)
            ctx
            (Assembly.Program.pcAfter
              (pre ++
                ([Assembly.Instr.jump defaultLabel] ++ between ++
                  [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop] ++
                  (Block.compileFromCtx body ctx bodySupply).code ++
                  [Assembly.Instr.jump endLabel, Assembly.Instr.label endLabel])))
            outcome result tokens) := by
  let compiledBody := Block.compileFromCtx body ctx bodySupply
  have hFitJumpDefault : PCFits pre :=
    AssemblyProgram.PCFitsFrom.start hFits
  have hFitDefaultLabel :
      PCFits (pre ++ [Assembly.Instr.jump defaultLabel] ++ between) := by
    have hPrefix :
        AssemblyProgram.PCFitsFrom pre
          ([Assembly.Instr.jump defaultLabel] ++ between) :=
      AssemblyProgram.PCFitsFrom.left (pre := pre)
        (first := [Assembly.Instr.jump defaultLabel] ++ between)
        (second :=
          [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop] ++
            compiledBody.code ++
            [Assembly.Instr.jump endLabel, Assembly.Instr.label endLabel])
        (by simpa [compiledBody, List.append_assoc] using hFits)
    simpa [List.append_assoc] using AssemblyProgram.PCFitsFrom.end hPrefix
  have hFitPop :
      PCFits (pre ++ [Assembly.Instr.jump defaultLabel] ++ between ++
        [Assembly.Instr.label defaultLabel]) := by
    have hPrefix :
        AssemblyProgram.PCFitsFrom pre
          ([Assembly.Instr.jump defaultLabel] ++ between ++
            [Assembly.Instr.label defaultLabel]) :=
      AssemblyProgram.PCFitsFrom.left (pre := pre)
        (first :=
          [Assembly.Instr.jump defaultLabel] ++ between ++
            [Assembly.Instr.label defaultLabel])
        (second :=
          [Assembly.Instr.prim .pop] ++ compiledBody.code ++
            [Assembly.Instr.jump endLabel, Assembly.Instr.label endLabel])
        (by simpa [compiledBody, List.append_assoc] using hFits)
    simpa [List.append_assoc] using AssemblyProgram.PCFitsFrom.end hPrefix
  have hBodyFits :
      AssemblyProgram.PCFitsFrom
        (pre ++ [Assembly.Instr.jump defaultLabel] ++ between ++
          [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop])
        compiledBody.code := by
    have hAfterPop :
        AssemblyProgram.PCFitsFrom
          (pre ++ [Assembly.Instr.jump defaultLabel] ++ between ++
            [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop])
          (compiledBody.code ++
            [Assembly.Instr.jump endLabel, Assembly.Instr.label endLabel]) := by
      simpa [compiledBody, List.append_assoc] using
        AssemblyProgram.PCFitsFrom.right (pre := pre)
          (first :=
            [Assembly.Instr.jump defaultLabel] ++ between ++
              [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop])
          (second :=
            compiledBody.code ++
              [Assembly.Instr.jump endLabel, Assembly.Instr.label endLabel])
          (by simpa [compiledBody, List.append_assoc] using hFits)
    exact
      AssemblyProgram.PCFitsFrom.left
        (pre :=
          pre ++ [Assembly.Instr.jump defaultLabel] ++ between ++
            [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop])
        (first := compiledBody.code)
        (second := [Assembly.Instr.jump endLabel, Assembly.Instr.label endLabel])
        hAfterPop
  have hFitJumpEnd :
      PCFits (pre ++ [Assembly.Instr.jump defaultLabel] ++ between ++
        [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop] ++
        compiledBody.code) := by
    simpa [List.append_assoc] using
      AssemblyProgram.PCFitsFrom.end hBodyFits
  have hFitEndLabel :
      PCFits (pre ++ [Assembly.Instr.jump defaultLabel] ++ between ++
        [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop] ++
        compiledBody.code ++ [Assembly.Instr.jump endLabel]) := by
    have hPrefix :
        AssemblyProgram.PCFitsFrom pre
          ([Assembly.Instr.jump defaultLabel] ++ between ++
            [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop] ++
            compiledBody.code ++ [Assembly.Instr.jump endLabel]) :=
      AssemblyProgram.PCFitsFrom.left (pre := pre)
        (first :=
          [Assembly.Instr.jump defaultLabel] ++ between ++
            [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop] ++
            compiledBody.code ++ [Assembly.Instr.jump endLabel])
        (second := [Assembly.Instr.label endLabel])
        (by simpa [compiledBody, List.append_assoc] using hFits)
    simpa [List.append_assoc] using AssemblyProgram.PCFitsFrom.end hPrefix
  have hDefaultLabel :
      Assembly.Program.labelPc
          (pre ++ [Assembly.Instr.jump defaultLabel] ++ between ++
            [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop] ++
            compiledBody.code ++
            [Assembly.Instr.jump endLabel, Assembly.Instr.label endLabel] ++
            post)
          defaultLabel =
        some
          (Assembly.Program.byteLength
            (pre ++ [Assembly.Instr.jump defaultLabel] ++ between)) := by
    have hHere :=
      hExact.labelPc_at
        (pre ++ [Assembly.Instr.jump defaultLabel] ++ between)
        defaultLabel
        ([Assembly.Instr.prim .pop] ++ compiledBody.code ++
          [Assembly.Instr.jump endLabel, Assembly.Instr.label endLabel] ++ post)
        (by simp [compiledBody, List.append_assoc])
    simpa [compiledBody, List.append_assoc] using hHere
  have hEndLabel :
      Assembly.Program.labelPc
          (pre ++ [Assembly.Instr.jump defaultLabel] ++ between ++
            [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop] ++
            compiledBody.code ++
            [Assembly.Instr.jump endLabel, Assembly.Instr.label endLabel] ++
            post)
          endLabel =
        some
          (Assembly.Program.byteLength
            (pre ++ [Assembly.Instr.jump defaultLabel] ++ between ++
              [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop] ++
              compiledBody.code ++ [Assembly.Instr.jump endLabel])) := by
    have hHere :=
      hExact.labelPc_at
        (pre ++ [Assembly.Instr.jump defaultLabel] ++ between ++
          [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop] ++
          compiledBody.code ++ [Assembly.Instr.jump endLabel])
        endLabel post
        (by simp [compiledBody, List.append_assoc])
    simpa [compiledBody, List.append_assoc] using hHere
  have hBodyResolve :
      ContextLabelsResolve
        (pre ++ [Assembly.Instr.jump defaultLabel] ++ between ++
          [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop] ++
          compiledBody.code ++
          ([Assembly.Instr.jump endLabel, Assembly.Instr.label endLabel] ++
            post))
        ctx := by
    simpa [compiledBody, List.append_assoc] using hResolve
  have hBodyExact :
      ExactLabels
        (pre ++ [Assembly.Instr.jump defaultLabel] ++ between ++
          [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop] ++
          compiledBody.code ++
          ([Assembly.Instr.jump endLabel, Assembly.Instr.label endLabel] ++
            post)) := by
    simpa [compiledBody, List.append_assoc] using hExact
  have hTail :=
    default_some_tail_result_ctx_withGasOracle
      (program := program) (ctx := ctx) (bodySupply := bodySupply)
      (body := body) (pre := pre) (between := between) (post := post)
      (defaultLabel := defaultLabel) (endLabel := endLabel)
      (fuel := fuel) (source := source) (outcome := outcome)
      (target := target) (tokens := tokens) (stack := stack) (value := value)
      (oracle := oracle) (cursor := cursor) (cursorFinal := cursorFinal)
      hBody hFitJumpDefault hFitDefaultLabel hFitPop
      (by simpa [compiledBody] using hBodyFits)
      (by simpa [compiledBody] using hFitJumpEnd)
      (by simpa [compiledBody] using hFitEndLabel)
      (by simpa [compiledBody, List.append_assoc] using hBodyResolve)
      (by simpa [compiledBody, List.append_assoc] using hBodyExact)
      (by simpa [compiledBody, List.append_assoc] using hDefaultLabel)
      (by simpa [compiledBody, List.append_assoc] using hEndLabel)
      hPc hRel hPop hBodyEval
  simpa [compiledBody, List.append_assoc] using hTail

theorem labeled_body_tail_result_ctx_withGasOracle {program : Program}
    {ctx : CompileContext} {bodySupply : LabelSupply} {body : Block}
    {pre betweenEnd post : Assembly.Program}
    {caseLabel endLabel : Assembly.Label}
    {fuel : Nat} {source : RunState} {outcome : Outcome}
    {target : EVMState} {tokens : List Word}
    {stack : EvmYul.Stack Word} {value : Word}
    {oracle : GasOracle} {cursor cursorFinal : Nat}
    (hBody : BlockPreservesWithGasOracle program ctx bodySupply body)
    (hFitLabel : PCFits pre)
    (hFitPop : PCFits (pre ++ [Assembly.Instr.label caseLabel]))
    (hBodyFits :
      AssemblyProgram.PCFitsFrom
        (pre ++ [Assembly.Instr.label caseLabel, Assembly.Instr.prim .pop])
        (Block.compileFromCtx body ctx bodySupply).code)
    (hFitJumpEnd :
      PCFits
        (pre ++ [Assembly.Instr.label caseLabel, Assembly.Instr.prim .pop] ++
          (Block.compileFromCtx body ctx bodySupply).code))
    (hFitEndLabel :
      PCFits
        (pre ++ [Assembly.Instr.label caseLabel, Assembly.Instr.prim .pop] ++
          (Block.compileFromCtx body ctx bodySupply).code ++
          [Assembly.Instr.jump endLabel] ++ betweenEnd))
    (hBodyResolve :
      ContextLabelsResolve
        (pre ++ [Assembly.Instr.label caseLabel, Assembly.Instr.prim .pop] ++
          (Block.compileFromCtx body ctx bodySupply).code ++
          ([Assembly.Instr.jump endLabel] ++ betweenEnd ++
            [Assembly.Instr.label endLabel] ++ post))
        ctx)
    (hBodyExact :
      ExactLabels
        (pre ++ [Assembly.Instr.label caseLabel, Assembly.Instr.prim .pop] ++
          (Block.compileFromCtx body ctx bodySupply).code ++
          ([Assembly.Instr.jump endLabel] ++ betweenEnd ++
            [Assembly.Instr.label endLabel] ++ post)))
    (hEndLabel :
      Assembly.Program.labelPc
          (pre ++ [Assembly.Instr.label caseLabel, Assembly.Instr.prim .pop] ++
            (Block.compileFromCtx body ctx bodySupply).code ++
            [Assembly.Instr.jump endLabel] ++ betweenEnd ++
            [Assembly.Instr.label endLabel] ++ post)
          endLabel =
        some
          (Assembly.Program.byteLength
            (pre ++ [Assembly.Instr.label caseLabel, Assembly.Instr.prim .pop] ++
              (Block.compileFromCtx body ctx bodySupply).code ++
              [Assembly.Instr.jump endLabel] ++ betweenEnd)))
    (hPc : target.pc = Assembly.Program.pcAfter pre)
    (hRel : Frame.StateRel source target tokens)
    (hPop : source.evm.stack.pop = some (stack, value))
    (hBodyEval :
      Block.EvalWithGasOracle program oracle fuel body cursor
        (source.withEVM { source.evm with stack := stack }) outcome
        cursorFinal) :
    ARunResultWithGasOracle
      (pre ++ [Assembly.Instr.label caseLabel, Assembly.Instr.prim .pop] ++
        (Block.compileFromCtx body ctx bodySupply).code ++
        [Assembly.Instr.jump endLabel] ++ betweenEnd ++
        [Assembly.Instr.label endLabel] ++ post)
      oracle cursor target
      (fun result targetCursorFinal =>
        targetCursorFinal = cursorFinal ∧
          CompiledOutcomeRel
            (pre ++ [Assembly.Instr.label caseLabel, Assembly.Instr.prim .pop] ++
              (Block.compileFromCtx body ctx bodySupply).code ++
              [Assembly.Instr.jump endLabel] ++ betweenEnd ++
              [Assembly.Instr.label endLabel] ++ post)
            ctx
            (Assembly.Program.pcAfter
              (pre ++ [Assembly.Instr.label caseLabel, Assembly.Instr.prim .pop] ++
                (Block.compileFromCtx body ctx bodySupply).code ++
                [Assembly.Instr.jump endLabel] ++ betweenEnd ++
                [Assembly.Instr.label endLabel]))
            outcome result tokens) := by
  let preAfterLabel : Assembly.Program :=
    pre ++ [Assembly.Instr.label caseLabel]
  let preBody : Assembly.Program := preAfterLabel ++ [Assembly.Instr.prim .pop]
  let compiledBody := Block.compileFromCtx body ctx bodySupply
  let preAfterBody : Assembly.Program := preBody ++ compiledBody.code
  have hLabelRun :=
    FrameStateRel.label_runResult_at_withGasOracle
      (label := caseLabel) (pre := pre)
      (post :=
        [Assembly.Instr.prim .pop] ++ compiledBody.code ++
          [Assembly.Instr.jump endLabel] ++ betweenEnd ++
          [Assembly.Instr.label endLabel] ++ post)
      (oracle := oracle) (cursor := cursor)
      hFitLabel hPc hRel
  refine
    ARunResultWithGasOracle.bind_running
      (program :=
        pre ++ [Assembly.Instr.label caseLabel, Assembly.Instr.prim .pop] ++
          compiledBody.code ++ [Assembly.Instr.jump endLabel] ++ betweenEnd ++
          [Assembly.Instr.label endLabel] ++ post)
      (middle := fun targetAfterLabel cursorAfterLabel =>
        cursorAfterLabel = cursor ∧
          Frame.StateRel source targetAfterLabel tokens ∧
            targetAfterLabel.pc = Assembly.Program.pcAfter preAfterLabel)
      ?_ ?_
  · exact ARunResultWithGasOracle.mono
      (by simpa [preAfterLabel, compiledBody, List.append_assoc] using hLabelRun)
      (by
        intro result cursorAfterLabel hResult
        cases result with
        | halted halt =>
            cases hResult
        | running targetAfterLabel =>
            simpa [preAfterLabel] using hResult)
  · intro targetAfterLabel cursorAfterLabel hAfterLabel
    rcases hAfterLabel with ⟨hCursorAfterLabel, hRelAfterLabel, hPcAfterLabel⟩
    subst cursorAfterLabel
    rcases FrameStateRel.pop_stepResult_at_withGasOracle
        (pre := preAfterLabel)
        (post :=
          compiledBody.code ++ [Assembly.Instr.jump endLabel] ++ betweenEnd ++
            [Assembly.Instr.label endLabel] ++ post)
        (source := source) (target := targetAfterLabel) (tokens := tokens)
        (stack := stack) (value := value)
        (oracle := oracle) (cursor := cursor)
        (by simpa [preAfterLabel, List.append_assoc] using hFitPop)
        hPcAfterLabel hRelAfterLabel hPop with
      ⟨targetAfterPop, hPopStep, hRelAfterPop, hPcAfterPop⟩
    have hPopRun :
        ARunResultWithGasOracle
          (preAfterLabel ++ [Assembly.Instr.prim .pop] ++
            (compiledBody.code ++ [Assembly.Instr.jump endLabel] ++
              betweenEnd ++ [Assembly.Instr.label endLabel] ++ post))
          oracle cursor targetAfterLabel
          (fun result cursorAfterPop =>
            match result with
            | .running targetAfterPop' =>
                cursorAfterPop = cursor ∧
                  Frame.StateRel
                    (source.withEVM { source.evm with stack := stack })
                    targetAfterPop' tokens ∧
                    targetAfterPop'.pc = Assembly.Program.pcAfter preBody
            | .halted _ => False) := by
      refine ⟨1, .running targetAfterPop, cursor, ?_, ?_⟩
      · unfold Assembly.GasParametric.sourceRunNResultWithGasOracle
        rw [hPopStep]
        rfl
      · exact
          ⟨rfl, hRelAfterPop,
            by simpa [preBody, List.append_assoc] using hPcAfterPop⟩
    refine
      ARunResultWithGasOracle.bind_running
        (program :=
          pre ++ [Assembly.Instr.label caseLabel, Assembly.Instr.prim .pop] ++
            compiledBody.code ++ [Assembly.Instr.jump endLabel] ++
            betweenEnd ++ [Assembly.Instr.label endLabel] ++ post)
        (middle := fun targetAfterPop cursorAfterPop =>
          cursorAfterPop = cursor ∧
            Frame.StateRel
              (source.withEVM { source.evm with stack := stack })
              targetAfterPop tokens ∧
              targetAfterPop.pc = Assembly.Program.pcAfter preBody)
        ?_ ?_
    · simpa [preAfterLabel, preBody, compiledBody, List.append_assoc] using hPopRun
    · intro targetAfterPop cursorAfterPop hAfterPop
      rcases hAfterPop with ⟨hCursorAfterPop, hRelAfterPop', hPcAfterPop'⟩
      subst cursorAfterPop
      have hBodyRun :=
        hBody (pre := preBody)
          (post :=
            [Assembly.Instr.jump endLabel] ++ betweenEnd ++
              [Assembly.Instr.label endLabel] ++ post)
          (fuel := fuel)
          (source := source.withEVM { source.evm with stack := stack })
          (outcome := outcome)
          (target := targetAfterPop) (tokens := tokens)
          (oracle := oracle) (cursor := cursor) (cursorFinal := cursorFinal)
          (by
            simpa [preAfterLabel, preBody, compiledBody, List.append_assoc]
              using hBodyFits)
          (by
            simpa [preAfterLabel, preBody, compiledBody, List.append_assoc]
              using hBodyResolve)
          (by
            simpa [preAfterLabel, preBody, compiledBody, List.append_assoc]
              using hBodyExact)
          hPcAfterPop' hRelAfterPop' hBodyEval
      cases outcome with
      | mk outState outMode =>
          cases outMode with
          | regular =>
              have hBodyRegular :
                  ARunResultWithGasOracle
                    (preBody ++ compiledBody.code ++
                      ([Assembly.Instr.jump endLabel] ++ betweenEnd ++
                        [Assembly.Instr.label endLabel] ++ post))
                    oracle cursor targetAfterPop
                    (fun result targetCursorBeforeEnd =>
                      match result with
                      | .running targetBeforeEnd =>
                          targetCursorBeforeEnd = cursorFinal ∧
                            Frame.StateRel outState targetBeforeEnd tokens ∧
                              targetBeforeEnd.pc =
                                Assembly.Program.pcAfter preAfterBody
                      | .halted _ => False) := by
                exact ARunResultWithGasOracle.mono hBodyRun (by
                  intro result targetCursorBeforeEnd hResult
                  cases result with
                  | halted halt =>
                      cases hResult.2
                  | running targetBeforeEnd =>
                      rcases hResult with ⟨hCursorBeforeEnd, hCompiled⟩
                      exact
                        ⟨hCursorBeforeEnd, by
                          simpa [CompiledOutcomeRel, Outcome.regular,
                            preAfterBody, List.append_assoc] using hCompiled⟩)
              refine
                ARunResultWithGasOracle.bind_running
                  (program :=
                    pre ++
                      [Assembly.Instr.label caseLabel,
                        Assembly.Instr.prim .pop] ++
                      compiledBody.code ++ [Assembly.Instr.jump endLabel] ++
                      betweenEnd ++ [Assembly.Instr.label endLabel] ++ post)
                  (middle := fun targetBeforeEnd targetCursorBeforeEnd =>
                    targetCursorBeforeEnd = cursorFinal ∧
                      Frame.StateRel outState targetBeforeEnd tokens ∧
                        targetBeforeEnd.pc =
                          Assembly.Program.pcAfter preAfterBody)
                  ?_ ?_
              · simpa [preAfterLabel, preBody, preAfterBody, compiledBody,
                  List.append_assoc] using hBodyRegular
              · intro targetBeforeEnd targetCursorBeforeEnd hBeforeEnd
                rcases hBeforeEnd with
                  ⟨hCursorBeforeEnd, hRelBeforeEnd, hPcBeforeEnd⟩
                subst targetCursorBeforeEnd
                have hEndRun :=
                  FrameStateRel.jump_then_label_runResult_at_withGasOracle
                    (label := endLabel) (pre := preAfterBody)
                    (between := betweenEnd) (post := post)
                    (oracle := oracle) (cursor := cursorFinal)
                    (by
                      simpa [preAfterBody, preBody, preAfterLabel,
                        compiledBody, List.append_assoc] using hFitJumpEnd)
                    (by
                      simpa [preAfterBody, preBody, preAfterLabel,
                        compiledBody, List.append_assoc] using hFitEndLabel)
                    hPcBeforeEnd hRelBeforeEnd
                    (by
                      simpa [preAfterBody, preBody, preAfterLabel,
                        compiledBody, List.append_assoc] using hEndLabel)
                exact ARunResultWithGasOracle.mono
                  (by
                    simpa [preAfterBody, preBody, preAfterLabel, compiledBody,
                      List.append_assoc] using hEndRun)
                  (by
                    intro result targetCursorFinal hResult
                    cases result with
                    | halted halt =>
                        cases hResult
                    | running targetFinal =>
                        rcases hResult with
                          ⟨hCursorEnd, hTargetRel, hTargetPc⟩
                        exact
                          ⟨hCursorEnd, by
                            simpa [preAfterBody, preBody, preAfterLabel,
                              compiledBody, CompiledOutcomeRel,
                              Outcome.regular, List.append_assoc]
                              using And.intro hTargetRel hTargetPc⟩)
          | brk =>
              exact ARunResultWithGasOracle.mono
                (by
                  simpa [preAfterLabel, preBody, compiledBody, List.append_assoc]
                    using hBodyRun)
                (by
                  intro result targetCursor hResult
                  rcases hResult with ⟨hCursor, hCompiled⟩
                  cases result with
                  | running target' =>
                      exact
                        ⟨hCursor, by
                          simpa [preAfterLabel, preBody, compiledBody,
                            CompiledOutcomeRel, Outcome.brk, List.append_assoc]
                            using hCompiled⟩
                  | halted halt =>
                      cases hCompiled)
          | cont =>
              exact ARunResultWithGasOracle.mono
                (by
                  simpa [preAfterLabel, preBody, compiledBody, List.append_assoc]
                    using hBodyRun)
                (by
                  intro result targetCursor hResult
                  rcases hResult with ⟨hCursor, hCompiled⟩
                  cases result with
                  | running target' =>
                      exact
                        ⟨hCursor, by
                          simpa [preAfterLabel, preBody, compiledBody,
                            CompiledOutcomeRel, Outcome.cont, List.append_assoc]
                            using hCompiled⟩
                  | halted halt =>
                      cases hCompiled)
          | leave =>
              exact ARunResultWithGasOracle.mono
                (by
                  simpa [preAfterLabel, preBody, compiledBody, List.append_assoc]
                    using hBodyRun)
                (by
                  intro result targetCursor hResult
                  rcases hResult with ⟨hCursor, hCompiled⟩
                  cases result with
                  | running target' =>
                      exact
                        ⟨hCursor, by
                          simpa [preAfterLabel, preBody, compiledBody,
                            CompiledOutcomeRel, Outcome.leave, List.append_assoc]
                            using hCompiled⟩
                  | halted halt =>
                      cases hCompiled)
          | halt kind =>
              exact ARunResultWithGasOracle.mono
                (by
                  simpa [preAfterLabel, preBody, compiledBody, List.append_assoc]
                    using hBodyRun)
                (by
                  intro result targetCursor hResult
                  rcases hResult with ⟨hCursor, hCompiled⟩
                  cases result with
                  | running target' =>
                      cases hCompiled
                  | halted halt =>
                      exact
                        ⟨hCursor, by
                          simpa [preAfterLabel, preBody, compiledBody,
                            CompiledOutcomeRel, Outcome.halt, List.append_assoc]
                            using hCompiled⟩)

theorem head_case_from_tests_result_ctx_withGasOracle {program : Program}
    {ctx : CompileContext} {base supply : LabelSupply} {idx : Nat}
    {probe : Word} {body : Block} {rest : List (Word × Block)}
    {defaultBody : Option Block}
    {pre casePrefix post : Assembly.Program}
    {defaultLabel endLabel : Assembly.Label}
    {fuel : Nat} {source : RunState} {outcome : Outcome}
    {target : EVMState} {tokens : List Word}
    {stack : EvmYul.Stack Word} {value : Word}
    {oracle : GasOracle} {cursor cursorFinal : Nat}
    (hBody : BlockPreservesWithGasOracle program ctx supply body)
    (hEq : probe = value)
    (hFits :
      AssemblyProgram.PCFitsFrom pre
        (Stmt.switchTest base idx probe ++
          Stmt.switchTests base (idx + 1) rest ++
          [Assembly.Instr.jump defaultLabel] ++
          casePrefix ++
          [ Assembly.Instr.label (LabelSupply.label base (idx + 2))
          , Assembly.Instr.prim .pop ] ++
          (Block.compileFromCtx body ctx supply).code ++
          [Assembly.Instr.jump endLabel] ++
          (SwitchCases.compileFromCtx rest ctx endLabel base
            (Block.compileFromCtx body ctx supply).next (idx + 1)).code ++
          (SwitchDefault.compileFromCtx defaultBody ctx endLabel defaultLabel
            (SwitchCases.compileFromCtx rest ctx endLabel base
              (Block.compileFromCtx body ctx supply).next (idx + 1)).next).code ++
          [Assembly.Instr.label endLabel]))
    (hResolve :
      ContextLabelsResolve
        (pre ++
          (Stmt.switchTest base idx probe ++
            Stmt.switchTests base (idx + 1) rest ++
            [Assembly.Instr.jump defaultLabel] ++
            casePrefix ++
            [ Assembly.Instr.label (LabelSupply.label base (idx + 2))
            , Assembly.Instr.prim .pop ] ++
            (Block.compileFromCtx body ctx supply).code ++
            [Assembly.Instr.jump endLabel] ++
            (SwitchCases.compileFromCtx rest ctx endLabel base
              (Block.compileFromCtx body ctx supply).next (idx + 1)).code ++
            (SwitchDefault.compileFromCtx defaultBody ctx endLabel defaultLabel
              (SwitchCases.compileFromCtx rest ctx endLabel base
                (Block.compileFromCtx body ctx supply).next (idx + 1)).next).code ++
            [Assembly.Instr.label endLabel]) ++ post)
        ctx)
    (hExact :
      ExactLabels
        (pre ++
          (Stmt.switchTest base idx probe ++
            Stmt.switchTests base (idx + 1) rest ++
            [Assembly.Instr.jump defaultLabel] ++
            casePrefix ++
            [ Assembly.Instr.label (LabelSupply.label base (idx + 2))
            , Assembly.Instr.prim .pop ] ++
            (Block.compileFromCtx body ctx supply).code ++
            [Assembly.Instr.jump endLabel] ++
            (SwitchCases.compileFromCtx rest ctx endLabel base
              (Block.compileFromCtx body ctx supply).next (idx + 1)).code ++
            (SwitchDefault.compileFromCtx defaultBody ctx endLabel defaultLabel
              (SwitchCases.compileFromCtx rest ctx endLabel base
                (Block.compileFromCtx body ctx supply).next (idx + 1)).next).code ++
            [Assembly.Instr.label endLabel]) ++ post))
    (hPc : target.pc = Assembly.Program.pcAfter pre)
    (hRel : Frame.StateRel source target tokens)
    (hPop : source.evm.stack.pop = some (stack, value))
    (hBodyEval :
      Block.EvalWithGasOracle program oracle fuel body cursor
        (source.withEVM { source.evm with stack := stack }) outcome
        cursorFinal) :
    ARunResultWithGasOracle
      (pre ++
        (Stmt.switchTest base idx probe ++
          Stmt.switchTests base (idx + 1) rest ++
          [Assembly.Instr.jump defaultLabel] ++
          casePrefix ++
          [ Assembly.Instr.label (LabelSupply.label base (idx + 2))
          , Assembly.Instr.prim .pop ] ++
          (Block.compileFromCtx body ctx supply).code ++
          [Assembly.Instr.jump endLabel] ++
          (SwitchCases.compileFromCtx rest ctx endLabel base
            (Block.compileFromCtx body ctx supply).next (idx + 1)).code ++
          (SwitchDefault.compileFromCtx defaultBody ctx endLabel defaultLabel
            (SwitchCases.compileFromCtx rest ctx endLabel base
              (Block.compileFromCtx body ctx supply).next (idx + 1)).next).code ++
          [Assembly.Instr.label endLabel]) ++ post)
      oracle cursor target
      (fun result targetCursorFinal =>
        targetCursorFinal = cursorFinal ∧
          CompiledOutcomeRel
            (pre ++
              (Stmt.switchTest base idx probe ++
                Stmt.switchTests base (idx + 1) rest ++
                [Assembly.Instr.jump defaultLabel] ++
                casePrefix ++
                [ Assembly.Instr.label (LabelSupply.label base (idx + 2))
                , Assembly.Instr.prim .pop ] ++
                (Block.compileFromCtx body ctx supply).code ++
                [Assembly.Instr.jump endLabel] ++
                (SwitchCases.compileFromCtx rest ctx endLabel base
                  (Block.compileFromCtx body ctx supply).next (idx + 1)).code ++
                (SwitchDefault.compileFromCtx defaultBody ctx endLabel defaultLabel
                  (SwitchCases.compileFromCtx rest ctx endLabel base
                    (Block.compileFromCtx body ctx supply).next (idx + 1)).next).code ++
                [Assembly.Instr.label endLabel]) ++ post)
            ctx
            (Assembly.Program.pcAfter
              (pre ++
                (Stmt.switchTest base idx probe ++
                  Stmt.switchTests base (idx + 1) rest ++
                  [Assembly.Instr.jump defaultLabel] ++
                  casePrefix ++
                  [ Assembly.Instr.label (LabelSupply.label base (idx + 2))
                  , Assembly.Instr.prim .pop ] ++
                  (Block.compileFromCtx body ctx supply).code ++
                  [Assembly.Instr.jump endLabel] ++
                  (SwitchCases.compileFromCtx rest ctx endLabel base
                    (Block.compileFromCtx body ctx supply).next (idx + 1)).code ++
                  (SwitchDefault.compileFromCtx defaultBody ctx endLabel defaultLabel
                    (SwitchCases.compileFromCtx rest ctx endLabel base
                      (Block.compileFromCtx body ctx supply).next
                        (idx + 1)).next).code ++
                  [Assembly.Instr.label endLabel])))
            outcome result tokens) := by
  let caseLabel := LabelSupply.label base (idx + 2)
  let testCode := Stmt.switchTest base idx probe
  let restTests := Stmt.switchTests base (idx + 1) rest
  let compiledBody := Block.compileFromCtx body ctx supply
  let compiledTail :=
    SwitchCases.compileFromCtx rest ctx endLabel base compiledBody.next
      (idx + 1)
  let compiledDefault :=
    SwitchDefault.compileFromCtx defaultBody ctx endLabel defaultLabel
      compiledTail.next
  let preCase : Assembly.Program :=
    pre ++ testCode ++ restTests ++ [Assembly.Instr.jump defaultLabel] ++
      casePrefix
  have hFitsHead :
      AssemblyProgram.PCFitsFrom pre
        (testCode ++ restTests ++ [Assembly.Instr.jump defaultLabel] ++
          casePrefix ++
          [Assembly.Instr.label caseLabel, Assembly.Instr.prim .pop] ++
          compiledBody.code ++
          [Assembly.Instr.jump endLabel] ++
          compiledTail.code ++ compiledDefault.code ++
          [Assembly.Instr.label endLabel]) := by
    simpa [caseLabel, testCode, restTests, compiledBody, compiledTail,
      compiledDefault, List.append_assoc] using hFits
  have hExactHead :
      ExactLabels
        (pre ++
          (testCode ++ restTests ++ [Assembly.Instr.jump defaultLabel] ++
            casePrefix ++
            [Assembly.Instr.label caseLabel, Assembly.Instr.prim .pop] ++
            compiledBody.code ++
            [Assembly.Instr.jump endLabel] ++
            compiledTail.code ++ compiledDefault.code ++
            [Assembly.Instr.label endLabel]) ++ post) := by
    simpa [caseLabel, testCode, restTests, compiledBody, compiledTail,
      compiledDefault, List.append_assoc] using hExact
  have hResolveHead :
      ContextLabelsResolve
        (pre ++
          (testCode ++ restTests ++ [Assembly.Instr.jump defaultLabel] ++
            casePrefix ++
            [Assembly.Instr.label caseLabel, Assembly.Instr.prim .pop] ++
            compiledBody.code ++
            [Assembly.Instr.jump endLabel] ++
            compiledTail.code ++ compiledDefault.code ++
            [Assembly.Instr.label endLabel]) ++ post)
        ctx := by
    simpa [caseLabel, testCode, restTests, compiledBody, compiledTail,
      compiledDefault, List.append_assoc] using hResolve
  have hTestFitsAsm : AssemblyProgram.PCFitsFrom pre testCode :=
    AssemblyProgram.PCFitsFrom.left (pre := pre)
      (first := testCode)
      (second :=
        restTests ++ [Assembly.Instr.jump defaultLabel] ++
          casePrefix ++
          [Assembly.Instr.label caseLabel, Assembly.Instr.prim .pop] ++
          compiledBody.code ++
          [Assembly.Instr.jump endLabel] ++ compiledTail.code ++
          compiledDefault.code ++ [Assembly.Instr.label endLabel])
      (by simpa [List.append_assoc] using hFitsHead)
  have hCondFitsAsm :
      AssemblyProgram.PCFitsFrom pre
        (Stmt.switchTestCode probe).toAssembly :=
    AssemblyProgram.PCFitsFrom.left (pre := pre)
      (first := (Stmt.switchTestCode probe).toAssembly)
      (second := [Assembly.Instr.jumpi caseLabel])
      (by simpa [Stmt.switchTest, caseLabel, testCode] using hTestFitsAsm)
  have hCondFits : Code.PCFitsFrom pre (Stmt.switchTestCode probe) :=
    Code.PCFitsFrom.of_assembly hCondFitsAsm
  have hFitCaseLabel : PCFits preCase := by
    have hPrefix :
        AssemblyProgram.PCFitsFrom pre
          (testCode ++ restTests ++ [Assembly.Instr.jump defaultLabel] ++
            casePrefix) :=
      AssemblyProgram.PCFitsFrom.left (pre := pre)
        (first :=
          testCode ++ restTests ++ [Assembly.Instr.jump defaultLabel] ++
            casePrefix)
        (second :=
          [Assembly.Instr.label caseLabel, Assembly.Instr.prim .pop] ++
            compiledBody.code ++ [Assembly.Instr.jump endLabel] ++
            compiledTail.code ++ compiledDefault.code ++
            [Assembly.Instr.label endLabel])
        (by simpa [List.append_assoc] using hFitsHead)
    simpa [preCase, List.append_assoc] using
      AssemblyProgram.PCFitsFrom.end hPrefix
  have hFitPop :
      PCFits (preCase ++ [Assembly.Instr.label caseLabel]) := by
    have hPrefix :
        AssemblyProgram.PCFitsFrom pre
          (testCode ++ restTests ++ [Assembly.Instr.jump defaultLabel] ++
            casePrefix ++ [Assembly.Instr.label caseLabel]) :=
      AssemblyProgram.PCFitsFrom.left (pre := pre)
        (first :=
          testCode ++ restTests ++ [Assembly.Instr.jump defaultLabel] ++
            casePrefix ++ [Assembly.Instr.label caseLabel])
        (second :=
          [Assembly.Instr.prim .pop] ++ compiledBody.code ++
            [Assembly.Instr.jump endLabel] ++ compiledTail.code ++
            compiledDefault.code ++ [Assembly.Instr.label endLabel])
        (by simpa [List.append_assoc] using hFitsHead)
    simpa [preCase, List.append_assoc] using
      AssemblyProgram.PCFitsFrom.end hPrefix
  have hBodyFits :
      AssemblyProgram.PCFitsFrom
        (preCase ++
          [Assembly.Instr.label caseLabel, Assembly.Instr.prim .pop])
        compiledBody.code := by
    have hAfterPop :
        AssemblyProgram.PCFitsFrom
          (preCase ++
            [Assembly.Instr.label caseLabel, Assembly.Instr.prim .pop])
          (compiledBody.code ++ [Assembly.Instr.jump endLabel] ++
            compiledTail.code ++ compiledDefault.code ++
            [Assembly.Instr.label endLabel]) := by
      simpa [preCase, List.append_assoc] using
        AssemblyProgram.PCFitsFrom.right (pre := pre)
          (first :=
            testCode ++ restTests ++ [Assembly.Instr.jump defaultLabel] ++
              casePrefix ++
              [Assembly.Instr.label caseLabel, Assembly.Instr.prim .pop])
          (second :=
            compiledBody.code ++ [Assembly.Instr.jump endLabel] ++
              compiledTail.code ++ compiledDefault.code ++
              [Assembly.Instr.label endLabel])
          (by simpa [List.append_assoc] using hFitsHead)
    exact
      AssemblyProgram.PCFitsFrom.left
        (pre := preCase ++
          [Assembly.Instr.label caseLabel, Assembly.Instr.prim .pop])
        (first := compiledBody.code)
        (second :=
          [Assembly.Instr.jump endLabel] ++ compiledTail.code ++
            compiledDefault.code ++ [Assembly.Instr.label endLabel])
        (by simpa [List.append_assoc] using hAfterPop)
  have hFitJumpEnd :
      PCFits
        (preCase ++
          [Assembly.Instr.label caseLabel, Assembly.Instr.prim .pop] ++
          compiledBody.code) := by
    simpa [List.append_assoc] using
      AssemblyProgram.PCFitsFrom.end hBodyFits
  have hFitEndLabel :
      PCFits
        (preCase ++
          [Assembly.Instr.label caseLabel, Assembly.Instr.prim .pop] ++
          compiledBody.code ++ [Assembly.Instr.jump endLabel] ++
          (compiledTail.code ++ compiledDefault.code)) := by
    have hPrefix :
        AssemblyProgram.PCFitsFrom pre
          (testCode ++ restTests ++ [Assembly.Instr.jump defaultLabel] ++
            casePrefix ++
            [Assembly.Instr.label caseLabel, Assembly.Instr.prim .pop] ++
            compiledBody.code ++ [Assembly.Instr.jump endLabel] ++
            compiledTail.code ++ compiledDefault.code) :=
      AssemblyProgram.PCFitsFrom.left (pre := pre)
        (first :=
          testCode ++ restTests ++ [Assembly.Instr.jump defaultLabel] ++
            casePrefix ++
            [Assembly.Instr.label caseLabel, Assembly.Instr.prim .pop] ++
            compiledBody.code ++ [Assembly.Instr.jump endLabel] ++
            compiledTail.code ++ compiledDefault.code)
        (second := [Assembly.Instr.label endLabel])
        (by simpa [List.append_assoc] using hFitsHead)
    simpa [preCase, List.append_assoc] using
      AssemblyProgram.PCFitsFrom.end hPrefix
  have hCaseLabel :
      Assembly.Program.labelPc
          (pre ++ (Stmt.switchTestCode probe).toAssembly ++
            [Assembly.Instr.jumpi caseLabel] ++
            (restTests ++ [Assembly.Instr.jump defaultLabel] ++
              casePrefix ++
              [Assembly.Instr.label caseLabel, Assembly.Instr.prim .pop] ++
              compiledBody.code ++ [Assembly.Instr.jump endLabel] ++
              compiledTail.code ++ compiledDefault.code ++
              [Assembly.Instr.label endLabel] ++ post))
          caseLabel =
        some (Assembly.Program.byteLength preCase) := by
    have hHere :=
      hExactHead.labelPc_at preCase caseLabel
        ([Assembly.Instr.prim .pop] ++ compiledBody.code ++
          [Assembly.Instr.jump endLabel] ++ compiledTail.code ++
          compiledDefault.code ++ [Assembly.Instr.label endLabel] ++ post)
        (by simp [preCase, testCode, Stmt.switchTest, caseLabel,
          List.append_assoc])
    simpa [preCase, testCode, Stmt.switchTest, caseLabel, List.append_assoc]
      using hHere
  have hEndLabel :
      Assembly.Program.labelPc
          (preCase ++
            [Assembly.Instr.label caseLabel, Assembly.Instr.prim .pop] ++
            compiledBody.code ++ [Assembly.Instr.jump endLabel] ++
            compiledTail.code ++ compiledDefault.code ++
            [Assembly.Instr.label endLabel] ++ post)
          endLabel =
        some
          (Assembly.Program.byteLength
            (preCase ++
              [Assembly.Instr.label caseLabel, Assembly.Instr.prim .pop] ++
              compiledBody.code ++ [Assembly.Instr.jump endLabel] ++
              compiledTail.code ++ compiledDefault.code)) := by
    have hHere :=
      hExactHead.labelPc_at
        (preCase ++
          [Assembly.Instr.label caseLabel, Assembly.Instr.prim .pop] ++
          compiledBody.code ++ [Assembly.Instr.jump endLabel] ++
          compiledTail.code ++ compiledDefault.code)
        endLabel post
        (by simp [preCase, List.append_assoc])
    simpa [preCase, List.append_assoc] using hHere
  have hBodyResolve :
      ContextLabelsResolve
        (preCase ++
          [Assembly.Instr.label caseLabel, Assembly.Instr.prim .pop] ++
          compiledBody.code ++
          ([Assembly.Instr.jump endLabel] ++
            (compiledTail.code ++ compiledDefault.code) ++
            [Assembly.Instr.label endLabel] ++ post))
        ctx := by
    simpa [preCase, List.append_assoc] using hResolveHead
  have hBodyExact :
      ExactLabels
        (preCase ++
          [Assembly.Instr.label caseLabel, Assembly.Instr.prim .pop] ++
          compiledBody.code ++
          ([Assembly.Instr.jump endLabel] ++
            (compiledTail.code ++ compiledDefault.code) ++
            [Assembly.Instr.label endLabel] ++ post)) := by
    simpa [preCase, List.append_assoc] using hExactHead
  have hTestRun :=
    test_true_result_ctx_withGasOracle
      (pre := pre)
      (post :=
        restTests ++ [Assembly.Instr.jump defaultLabel] ++
          casePrefix ++
          [Assembly.Instr.label caseLabel, Assembly.Instr.prim .pop] ++
          compiledBody.code ++ [Assembly.Instr.jump endLabel] ++
          compiledTail.code ++ compiledDefault.code ++
          [Assembly.Instr.label endLabel] ++ post)
      (label := caseLabel)
      (dest := Assembly.Program.byteLength preCase)
      (source := source) (target := target) (tokens := tokens)
      (stack := stack) (value := value) (probe := probe)
      (oracle := oracle) (cursor := cursor)
      hEq hCondFits hPc hRel
      (by simpa [List.append_assoc] using hCaseLabel) hPop
  have hTestToCase :
      ARunResultWithGasOracle
        (pre ++
          (Stmt.switchTest base idx probe ++
            Stmt.switchTests base (idx + 1) rest ++
            [Assembly.Instr.jump defaultLabel] ++
            casePrefix ++
            [Assembly.Instr.label caseLabel, Assembly.Instr.prim .pop] ++
            compiledBody.code ++
            [Assembly.Instr.jump endLabel] ++ compiledTail.code ++
            compiledDefault.code ++ [Assembly.Instr.label endLabel]) ++ post)
        oracle cursor target
        (fun result targetCursorAtCase =>
          match result with
          | .running targetAtCase =>
              targetCursorAtCase = cursor ∧
                Frame.StateRel source targetAtCase tokens ∧
                  targetAtCase.pc = Assembly.Program.pcAfter preCase
          | .halted _ => False) := by
    exact ARunResultWithGasOracle.mono
      (by
        simpa [testCode, restTests, caseLabel, List.append_assoc]
          using hTestRun)
      (by
        intro result targetCursorAtCase hResult
        cases result with
        | halted halt =>
            cases hResult
        | running targetAtCase =>
            rcases hResult with ⟨hCursorAtCase, hRelAtCase, hPcAtCase⟩
            exact
              ⟨hCursorAtCase, hRelAtCase,
                by simpa [Assembly.Program.pcAfter] using hPcAtCase⟩)
  refine
    ARunResultWithGasOracle.bind_running
      (program :=
        pre ++
          (Stmt.switchTest base idx probe ++
            Stmt.switchTests base (idx + 1) rest ++
            [Assembly.Instr.jump defaultLabel] ++
            casePrefix ++
            [Assembly.Instr.label caseLabel, Assembly.Instr.prim .pop] ++
            compiledBody.code ++
            [Assembly.Instr.jump endLabel] ++ compiledTail.code ++
            compiledDefault.code ++ [Assembly.Instr.label endLabel]) ++ post)
      (middle := fun targetAtCase targetCursorAtCase =>
        targetCursorAtCase = cursor ∧
          Frame.StateRel source targetAtCase tokens ∧
            targetAtCase.pc = Assembly.Program.pcAfter preCase)
      hTestToCase ?_
  intro targetAtCase targetCursorAtCase hAtCase
  rcases hAtCase with ⟨hCursorAtCase, hRelAtCase, hPcAtCase⟩
  subst targetCursorAtCase
  have hTail :=
    labeled_body_tail_result_ctx_withGasOracle
      (program := program) (ctx := ctx) (bodySupply := supply)
      (body := body) (pre := preCase)
      (betweenEnd := compiledTail.code ++ compiledDefault.code)
      (post := post) (caseLabel := caseLabel) (endLabel := endLabel)
      (fuel := fuel) (source := source) (outcome := outcome)
      (target := targetAtCase) (tokens := tokens) (stack := stack)
      (value := value) (oracle := oracle) (cursor := cursor)
      (cursorFinal := cursorFinal)
      hBody hFitCaseLabel hFitPop hBodyFits hFitJumpEnd hFitEndLabel
      (by simpa [compiledBody, List.append_assoc] using hBodyResolve)
      (by simpa [compiledBody, List.append_assoc] using hBodyExact)
      (by simpa [compiledBody, List.append_assoc] using hEndLabel)
      hPcAtCase hRelAtCase hPop hBodyEval
  simpa [caseLabel, testCode, restTests, compiledBody, compiledTail,
    compiledDefault, preCase, List.append_assoc] using hTail

theorem selected_cases_result_ctx_withGasOracle {program : Program}
    {ctx : CompileContext} {base supply : LabelSupply} {idx : Nat}
    {cases : List (Word × Block)} {defaultBody : Option Block}
    {selected : Block}
    {pre casePrefix post : Assembly.Program}
    {defaultLabel endLabel : Assembly.Label}
    {fuel : Nat} {source : RunState} {outcome : Outcome}
    {target : EVMState} {tokens : List Word}
    {stack : EvmYul.Stack Word} {value : Word}
    {oracle : GasOracle} {cursor cursorFinal : Nat}
    (hCases :
      CasesPreserves program ctx endLabel base supply idx cases)
    (hDefault :
      DefaultPreserves program ctx
        (SwitchCases.compileFromCtx cases ctx endLabel base supply idx).next
        defaultBody)
    (hFits :
      AssemblyProgram.PCFitsFrom pre
        (Stmt.switchTests base idx cases ++
          [Assembly.Instr.jump defaultLabel] ++
          casePrefix ++
          (SwitchCases.compileFromCtx cases ctx endLabel base supply idx).code ++
          (SwitchDefault.compileFromCtx defaultBody ctx endLabel defaultLabel
            (SwitchCases.compileFromCtx cases ctx endLabel base supply idx).next).code ++
          [Assembly.Instr.label endLabel]))
    (hResolve :
      ContextLabelsResolve
        (pre ++
          (Stmt.switchTests base idx cases ++
            [Assembly.Instr.jump defaultLabel] ++
            casePrefix ++
            (SwitchCases.compileFromCtx cases ctx endLabel base supply idx).code ++
            (SwitchDefault.compileFromCtx defaultBody ctx endLabel defaultLabel
              (SwitchCases.compileFromCtx cases ctx endLabel base supply idx).next).code ++
            [Assembly.Instr.label endLabel]) ++ post)
        ctx)
    (hExact :
      ExactLabels
        (pre ++
          (Stmt.switchTests base idx cases ++
            [Assembly.Instr.jump defaultLabel] ++
            casePrefix ++
            (SwitchCases.compileFromCtx cases ctx endLabel base supply idx).code ++
            (SwitchDefault.compileFromCtx defaultBody ctx endLabel defaultLabel
              (SwitchCases.compileFromCtx cases ctx endLabel base supply idx).next).code ++
            [Assembly.Instr.label endLabel]) ++ post))
    (hPc : target.pc = Assembly.Program.pcAfter pre)
    (hRel : Frame.StateRel source target tokens)
    (hPop : source.evm.stack.pop = some (stack, value))
    (hSelect : Switch.select value cases defaultBody = some selected)
    (hBodyEval :
      Block.EvalWithGasOracle program oracle fuel selected cursor
        (source.withEVM { source.evm with stack := stack }) outcome
        cursorFinal) :
    ARunResultWithGasOracle
      (pre ++
        (Stmt.switchTests base idx cases ++
          [Assembly.Instr.jump defaultLabel] ++
          casePrefix ++
          (SwitchCases.compileFromCtx cases ctx endLabel base supply idx).code ++
          (SwitchDefault.compileFromCtx defaultBody ctx endLabel defaultLabel
            (SwitchCases.compileFromCtx cases ctx endLabel base supply idx).next).code ++
          [Assembly.Instr.label endLabel]) ++ post)
      oracle cursor target
      (fun result targetCursorFinal =>
        targetCursorFinal = cursorFinal ∧
          CompiledOutcomeRel
            (pre ++
              (Stmt.switchTests base idx cases ++
                [Assembly.Instr.jump defaultLabel] ++
                casePrefix ++
                (SwitchCases.compileFromCtx cases ctx endLabel base supply idx).code ++
                (SwitchDefault.compileFromCtx defaultBody ctx endLabel defaultLabel
                  (SwitchCases.compileFromCtx cases ctx endLabel base supply idx).next).code ++
                [Assembly.Instr.label endLabel]) ++ post)
            ctx
            (Assembly.Program.pcAfter
              (pre ++
                (Stmt.switchTests base idx cases ++
                  [Assembly.Instr.jump defaultLabel] ++
                  casePrefix ++
                  (SwitchCases.compileFromCtx cases ctx endLabel base supply idx).code ++
                  (SwitchDefault.compileFromCtx defaultBody ctx endLabel
                    defaultLabel
                    (SwitchCases.compileFromCtx cases ctx endLabel base supply
                      idx).next).code ++
                  [Assembly.Instr.label endLabel])))
            outcome result tokens) := by
  induction cases generalizing pre supply idx casePrefix target selected cursor with
  | nil =>
      cases defaultBody with
      | none =>
          simp [Switch.select] at hSelect
      | some defaultBlock =>
          have hSelected : selected = defaultBlock := by
            simpa [Switch.select] using hSelect.symm
          subst selected
          have hDefaultBlock :
              BlockPreservesWithGasOracle program ctx supply defaultBlock := by
            have hNext :
                (SwitchCases.compileFromCtx ([] : List (Word × Block)) ctx
                  endLabel base supply idx).next = supply := by
              simp [SwitchCases.compileFromCtx]
            rw [hNext] at hDefault
            intro pre' post' fuel' source' outcome' target' tokens' oracle'
              cursor' cursorFinal' hFits' hResolve' hExact' hPc' hRel' hEval'
            have hRun :=
              hDefault (pre := pre') (post := post') (fuel := fuel')
                (source := source') (outcome := outcome') (target := target')
                (tokens := tokens') (oracle := oracle') (cursor := cursor')
                (cursorFinal := cursorFinal')
                hFits'
                (by simpa [List.append_assoc] using hResolve')
                (by simpa [List.append_assoc] using hExact')
                hPc' hRel' hEval'
            exact ARunResultWithGasOracle.mono
              (by simpa [DefaultPreserves, List.append_assoc] using hRun)
              (by
                intro result targetCursorFinal hResult
                simpa [DefaultPreserves, List.append_assoc] using hResult)
          have hRun :=
            default_selected_tail_result_ctx_withGasOracle
              (program := program) (ctx := ctx) (bodySupply := supply)
              (body := defaultBlock) (pre := pre) (between := casePrefix)
              (post := post) (defaultLabel := defaultLabel)
              (endLabel := endLabel) (fuel := fuel) (source := source)
              (outcome := outcome) (target := target) (tokens := tokens)
              (stack := stack) (value := value)
              (oracle := oracle) (cursor := cursor)
              (cursorFinal := cursorFinal)
              hDefaultBlock
              (by
                simpa [Stmt.switchTests, SwitchCases.compileFromCtx,
                  SwitchDefault.compileFromCtx, List.append_assoc] using hFits)
              (by
                simpa [Stmt.switchTests, SwitchCases.compileFromCtx,
                  SwitchDefault.compileFromCtx, List.append_assoc]
                  using hResolve)
              (by
                simpa [Stmt.switchTests, SwitchCases.compileFromCtx,
                  SwitchDefault.compileFromCtx, List.append_assoc]
                  using hExact)
              hPc hRel hPop hBodyEval
          simpa [Stmt.switchTests, SwitchCases.compileFromCtx,
            SwitchDefault.compileFromCtx, List.append_assoc] using hRun
  | cons head rest ih =>
      rcases head with ⟨probe, headBody⟩
      let caseLabel := LabelSupply.label base (idx + 2)
      let testCode := Stmt.switchTest base idx probe
      let restTests := Stmt.switchTests base (idx + 1) rest
      let compiledBody := Block.compileFromCtx headBody ctx supply
      let headCode : Assembly.Program :=
        [Assembly.Instr.label caseLabel, Assembly.Instr.prim .pop] ++
          compiledBody.code ++ [Assembly.Instr.jump endLabel]
      let compiledTail :=
        SwitchCases.compileFromCtx rest ctx endLabel base compiledBody.next
          (idx + 1)
      let compiledDefault :=
        SwitchDefault.compileFromCtx defaultBody ctx endLabel defaultLabel
          compiledTail.next
      have hHeadBodyPreserves :
          BlockPreservesWithGasOracle program ctx supply headBody :=
        casesPreserves_head hCases
      have hTailPreserves :
          CasesPreserves program ctx endLabel base
            compiledBody.next (idx + 1) rest := by
        simpa [compiledBody] using casesPreserves_tail hCases
      have hDefaultTail :
          DefaultPreserves program ctx compiledTail.next defaultBody := by
        simpa [SwitchCases.compileFromCtx, CompileResult.append, caseLabel,
          compiledBody, compiledTail] using hDefault
      by_cases hEq : probe = value
      · have hSelected : selected = headBody :=
          EvmCompiler.Structured.Preservation.SwitchPreservation.select_head_body_of_head_eq
            (value := value) (probe := probe)
            (headBody := headBody) (body := selected) (rest := rest)
            (defaultBody := defaultBody) hEq hSelect
        subst selected
        have hRun :=
          head_case_from_tests_result_ctx_withGasOracle
            (program := program) (ctx := ctx) (base := base)
            (supply := supply) (idx := idx) (probe := probe)
            (body := headBody) (rest := rest) (defaultBody := defaultBody)
            (pre := pre) (casePrefix := casePrefix) (post := post)
            (defaultLabel := defaultLabel) (endLabel := endLabel)
            (fuel := fuel) (source := source) (outcome := outcome)
            (target := target) (tokens := tokens) (stack := stack)
            (value := value) (oracle := oracle) (cursor := cursor)
            (cursorFinal := cursorFinal)
            hHeadBodyPreserves hEq
            (by
              simpa [Stmt.switchTests, Stmt.switchTest,
                SwitchCases.compileFromCtx, CompileResult.append, caseLabel,
                testCode, restTests, compiledBody, compiledTail,
                compiledDefault, headCode, List.append_assoc] using hFits)
            (by
              simpa [Stmt.switchTests, Stmt.switchTest,
                SwitchCases.compileFromCtx, CompileResult.append, caseLabel,
                testCode, restTests, compiledBody, compiledTail,
                compiledDefault, headCode, List.append_assoc] using hResolve)
            (by
              simpa [Stmt.switchTests, Stmt.switchTest,
                SwitchCases.compileFromCtx, CompileResult.append, caseLabel,
                testCode, restTests, compiledBody, compiledTail,
                compiledDefault, headCode, List.append_assoc] using hExact)
            hPc hRel hPop hBodyEval
        simpa [Stmt.switchTests, Stmt.switchTest, SwitchCases.compileFromCtx,
          CompileResult.append, caseLabel, testCode, restTests, compiledBody,
          compiledTail, compiledDefault, headCode, List.append_assoc] using hRun
      · have hTailSelect :
            Switch.select value rest defaultBody = some selected :=
          EvmCompiler.Structured.Preservation.SwitchPreservation.select_tail_of_head_ne
            (value := value) (probe := probe)
            (headBody := headBody) (body := selected) (rest := rest)
            (defaultBody := defaultBody) hEq hSelect
        have hFitsCons :
            AssemblyProgram.PCFitsFrom pre
              (testCode ++ restTests ++ [Assembly.Instr.jump defaultLabel] ++
                casePrefix ++ headCode ++ compiledTail.code ++
                compiledDefault.code ++ [Assembly.Instr.label endLabel]) := by
          simpa [Stmt.switchTests, Stmt.switchTest,
            SwitchCases.compileFromCtx, CompileResult.append, caseLabel,
            testCode, restTests, compiledBody, compiledTail, compiledDefault,
            headCode, List.append_assoc] using hFits
        have hExactCons :
            ExactLabels
              (pre ++
                (testCode ++ restTests ++ [Assembly.Instr.jump defaultLabel] ++
                  casePrefix ++ headCode ++ compiledTail.code ++
                  compiledDefault.code ++ [Assembly.Instr.label endLabel]) ++
                post) := by
          simpa [Stmt.switchTests, Stmt.switchTest,
            SwitchCases.compileFromCtx, CompileResult.append, caseLabel,
            testCode, restTests, compiledBody, compiledTail, compiledDefault,
            headCode, List.append_assoc] using hExact
        have hResolveCons :
            ContextLabelsResolve
              (pre ++
                (testCode ++ restTests ++ [Assembly.Instr.jump defaultLabel] ++
                  casePrefix ++ headCode ++ compiledTail.code ++
                  compiledDefault.code ++ [Assembly.Instr.label endLabel]) ++
                post)
              ctx := by
          simpa [Stmt.switchTests, Stmt.switchTest,
            SwitchCases.compileFromCtx, CompileResult.append, caseLabel,
            testCode, restTests, compiledBody, compiledTail, compiledDefault,
            headCode, List.append_assoc] using hResolve
        have hTestFitsAsm : AssemblyProgram.PCFitsFrom pre testCode :=
          AssemblyProgram.PCFitsFrom.left (pre := pre)
            (first := testCode)
            (second :=
              restTests ++ [Assembly.Instr.jump defaultLabel] ++
                casePrefix ++ headCode ++ compiledTail.code ++
                compiledDefault.code ++ [Assembly.Instr.label endLabel])
            (by simpa [List.append_assoc] using hFitsCons)
        have hCondFitsAsm :
            AssemblyProgram.PCFitsFrom pre
              (Stmt.switchTestCode probe).toAssembly :=
          AssemblyProgram.PCFitsFrom.left (pre := pre)
            (first := (Stmt.switchTestCode probe).toAssembly)
            (second := [Assembly.Instr.jumpi caseLabel])
            (by simpa [Stmt.switchTest, caseLabel, testCode]
              using hTestFitsAsm)
        have hCondFits : Code.PCFitsFrom pre (Stmt.switchTestCode probe) :=
          Code.PCFitsFrom.of_assembly hCondFitsAsm
        let preCase : Assembly.Program :=
          pre ++ testCode ++ restTests ++
            [Assembly.Instr.jump defaultLabel] ++ casePrefix
        have hCaseLabel :
            Assembly.Program.labelPc
                (pre ++ (Stmt.switchTestCode probe).toAssembly ++
                  [Assembly.Instr.jumpi caseLabel] ++
                  (restTests ++ [Assembly.Instr.jump defaultLabel] ++
                    casePrefix ++ headCode ++ compiledTail.code ++
                    compiledDefault.code ++ [Assembly.Instr.label endLabel] ++
                    post))
                caseLabel =
              some (Assembly.Program.byteLength preCase) := by
          have hHere :=
            hExactCons.labelPc_at preCase caseLabel
              ([Assembly.Instr.prim .pop] ++ compiledBody.code ++
                [Assembly.Instr.jump endLabel] ++ compiledTail.code ++
                compiledDefault.code ++ [Assembly.Instr.label endLabel] ++ post)
              (by
                simp [preCase, testCode, Stmt.switchTest, caseLabel,
                  headCode, List.append_assoc])
          simpa [preCase, testCode, Stmt.switchTest, caseLabel, headCode,
            List.append_assoc] using hHere
        have hTestRun :=
          test_false_result_ctx_withGasOracle
            (pre := pre)
            (post :=
              restTests ++ [Assembly.Instr.jump defaultLabel] ++
                casePrefix ++ headCode ++ compiledTail.code ++
                compiledDefault.code ++ [Assembly.Instr.label endLabel] ++ post)
            (label := caseLabel)
            (dest := Assembly.Program.byteLength preCase)
            (source := source) (target := target) (tokens := tokens)
            (stack := stack) (value := value) (probe := probe)
            (oracle := oracle) (cursor := cursor)
            hEq hCondFits hPc hRel
            (by simpa [List.append_assoc] using hCaseLabel) hPop
        have hTestFalse :
            ARunResultWithGasOracle
              (pre ++
                (testCode ++ restTests ++ [Assembly.Instr.jump defaultLabel] ++
                  casePrefix ++ headCode ++ compiledTail.code ++
                  compiledDefault.code ++ [Assembly.Instr.label endLabel]) ++
                post)
              oracle cursor target
              (fun result targetCursorAfterTest =>
                match result with
                | .running targetAfterTest =>
                    targetCursorAfterTest = cursor ∧
                      Frame.StateRel source targetAfterTest tokens ∧
                        targetAfterTest.pc =
                          Assembly.Program.pcAfter (pre ++ testCode)
                | .halted _ => False) := by
          simpa [testCode, caseLabel, List.append_assoc] using hTestRun
        refine
          ARunResultWithGasOracle.bind_running
            (program :=
              pre ++
                (Stmt.switchTests base idx ((probe, headBody) :: rest) ++
                  [Assembly.Instr.jump defaultLabel] ++ casePrefix ++
                  (SwitchCases.compileFromCtx ((probe, headBody) :: rest) ctx
                    endLabel base supply idx).code ++
                  (SwitchDefault.compileFromCtx defaultBody ctx endLabel
                    defaultLabel
                    (SwitchCases.compileFromCtx ((probe, headBody) :: rest)
                      ctx endLabel base supply idx).next).code ++
                  [Assembly.Instr.label endLabel]) ++ post)
            (middle := fun targetAfterTest targetCursorAfterTest =>
              targetCursorAfterTest = cursor ∧
                Frame.StateRel source targetAfterTest tokens ∧
                  targetAfterTest.pc = Assembly.Program.pcAfter (pre ++ testCode))
            ?_ ?_
        · simpa [Stmt.switchTests, Stmt.switchTest,
            SwitchCases.compileFromCtx, CompileResult.append, caseLabel,
            testCode, restTests, compiledBody, compiledTail, compiledDefault,
            headCode, List.append_assoc] using hTestFalse
        · intro targetAfterTest targetCursorAfterTest hAfterTest
          rcases hAfterTest with
            ⟨hCursorAfterTest, hRelAfterTest, hPcAfterTest⟩
          subst targetCursorAfterTest
          have hRec :=
            ih (supply := compiledBody.next) (idx := idx + 1)
              (pre := pre ++ testCode)
              (casePrefix := casePrefix ++ headCode)
              (target := targetAfterTest)
              (selected := selected) (cursor := cursor)
              hTailPreserves hDefaultTail
              (by
                simpa [testCode, restTests, compiledBody, compiledTail,
                  compiledDefault, headCode, List.append_assoc] using
                  (AssemblyProgram.PCFitsFrom.right (pre := pre)
                    (first := testCode)
                    (second :=
                      restTests ++ [Assembly.Instr.jump defaultLabel] ++
                        casePrefix ++ headCode ++ compiledTail.code ++
                        compiledDefault.code ++ [Assembly.Instr.label endLabel])
                    hFitsCons))
              (by
                simpa [testCode, restTests, compiledBody, compiledTail,
                  compiledDefault, headCode, List.append_assoc]
                  using hResolveCons)
              (by
                simpa [testCode, restTests, compiledBody, compiledTail,
                  compiledDefault, headCode, List.append_assoc]
                  using hExactCons)
              hPcAfterTest hRelAfterTest hTailSelect hBodyEval
          simpa [Stmt.switchTests, Stmt.switchTest,
            SwitchCases.compileFromCtx, CompileResult.append, caseLabel,
            testCode, restTests, compiledBody, compiledTail, compiledDefault,
            headCode, List.append_assoc] using hRec

theorem switch_none_result_ctx_withGasOracle {ctx : CompileContext}
    {supply : LabelSupply} {scrutinee : Code}
    {cases : List (Word × Block)} {defaultBody : Option Block}
    {source stateAfterScrutinee : RunState}
    {target : EVMState} {tokens : List Word}
    {stack : EvmYul.Stack Word} {value : Word}
    {pre post : Assembly.Program}
    {oracle : GasOracle} {cursor cursorAfterScrutinee : Nat}
    (hScrutineeSafe : Code.RunnerSafeWithGasOracle scrutinee)
    (hScrutineeFrame : Code.FrameSafeWithGasOracle scrutinee)
    (hFits :
      AssemblyProgram.PCFitsFrom pre
        (Stmt.compileFromCtxCore
          (.switch scrutinee cases defaultBody) ctx supply).code)
    (hExact :
      ExactLabels
        (pre ++
          (Stmt.compileFromCtxCore
            (.switch scrutinee cases defaultBody) ctx supply).code ++ post))
    (hPc : target.pc = Assembly.Program.pcAfter pre)
    (hRel : Frame.StateRel source target tokens)
    (hScrutinee :
      Code.runStateWithGasOracle scrutinee oracle cursor source =
        .ok (stateAfterScrutinee, cursorAfterScrutinee))
    (hPop : stateAfterScrutinee.evm.stack.pop = some (stack, value))
    (hSelect : Switch.select value cases defaultBody = none) :
    ARunResultWithGasOracle
      (pre ++
        (Stmt.compileFromCtxCore
          (.switch scrutinee cases defaultBody) ctx supply).code ++ post)
      oracle cursor target
      (fun result targetCursorFinal =>
        targetCursorFinal = cursorAfterScrutinee ∧
          CompiledOutcomeRel
            (pre ++
              (Stmt.compileFromCtxCore
                (.switch scrutinee cases defaultBody) ctx supply).code ++ post)
            ctx
            (Assembly.Program.pcAfter
              (pre ++
                (Stmt.compileFromCtxCore
                  (.switch scrutinee cases defaultBody) ctx supply).code))
            (Outcome.regular
              (stateAfterScrutinee.withEVM
                { stateAfterScrutinee.evm with stack := stack }))
            result tokens) := by
  let endLabel := LabelSupply.label supply 0
  let defaultLabel := LabelSupply.label supply 1
  let compiledCases :=
    SwitchCases.compileFromCtx cases ctx endLabel supply
      (LabelSupply.next supply) 0
  let compiledDefault :=
    SwitchDefault.compileFromCtx defaultBody ctx endLabel defaultLabel
      compiledCases.next
  let preTests : Assembly.Program := pre ++ scrutinee.toAssembly
  let preTail : Assembly.Program :=
    preTests ++ Stmt.switchTests supply 0 cases
  have hDefaultNone : defaultBody = none :=
    EvmCompiler.Structured.Preservation.SwitchPreservation.default_none_of_select_none
      hSelect
  have hFitsSwitch :
      AssemblyProgram.PCFitsFrom pre
        (scrutinee.toAssembly ++
          Stmt.switchTests supply 0 cases ++
          [Assembly.Instr.jump defaultLabel] ++
          compiledCases.code ++
          [ Assembly.Instr.label defaultLabel
          , Assembly.Instr.prim .pop
          , Assembly.Instr.jump endLabel
          , Assembly.Instr.label endLabel ]) := by
    simpa [Stmt.compileFromCtxCore, endLabel, defaultLabel, compiledCases,
      compiledDefault, hDefaultNone, SwitchDefault.compileFromCtx,
      List.append_assoc] using hFits
  have hScrutineeFitsAsm :
      AssemblyProgram.PCFitsFrom pre scrutinee.toAssembly :=
    AssemblyProgram.PCFitsFrom.left (pre := pre)
      (first := scrutinee.toAssembly)
      (second :=
        Stmt.switchTests supply 0 cases ++
          [Assembly.Instr.jump defaultLabel] ++
          compiledCases.code ++
          [ Assembly.Instr.label defaultLabel
          , Assembly.Instr.prim .pop
          , Assembly.Instr.jump endLabel
          , Assembly.Instr.label endLabel ])
      (by simpa [List.append_assoc] using hFitsSwitch)
  have hScrutineeFits : Code.PCFitsFrom pre scrutinee :=
    Code.PCFitsFrom.of_assembly hScrutineeFitsAsm
  have hAfterScrutineeFits :
      AssemblyProgram.PCFitsFrom preTests
        (Stmt.switchTests supply 0 cases ++
          [Assembly.Instr.jump defaultLabel] ++
          compiledCases.code ++
          [ Assembly.Instr.label defaultLabel
          , Assembly.Instr.prim .pop
          , Assembly.Instr.jump endLabel
          , Assembly.Instr.label endLabel ]) := by
    simpa [preTests, List.append_assoc] using
      AssemblyProgram.PCFitsFrom.right (pre := pre)
        (first := scrutinee.toAssembly)
        (second :=
          Stmt.switchTests supply 0 cases ++
            [Assembly.Instr.jump defaultLabel] ++
            compiledCases.code ++
            [ Assembly.Instr.label defaultLabel
            , Assembly.Instr.prim .pop
            , Assembly.Instr.jump endLabel
            , Assembly.Instr.label endLabel ])
        (by simpa [List.append_assoc] using hFitsSwitch)
  have hTestsFits :
      AssemblyProgram.PCFitsFrom preTests
        (Stmt.switchTests supply 0 cases) :=
    AssemblyProgram.PCFitsFrom.left (pre := preTests)
      (first := Stmt.switchTests supply 0 cases)
      (second :=
        [Assembly.Instr.jump defaultLabel] ++ compiledCases.code ++
          [ Assembly.Instr.label defaultLabel
          , Assembly.Instr.prim .pop
          , Assembly.Instr.jump endLabel
          , Assembly.Instr.label endLabel ])
      (by simpa [List.append_assoc] using hAfterScrutineeFits)
  have hFitJumpDefault : PCFits preTail := by
    simpa [preTail, List.append_assoc] using
      AssemblyProgram.PCFitsFrom.end hTestsFits
  have hFitDefaultLabel :
      PCFits (preTail ++ [Assembly.Instr.jump defaultLabel] ++
        compiledCases.code) := by
    have hPrefix :
        AssemblyProgram.PCFitsFrom pre
          (scrutinee.toAssembly ++
            Stmt.switchTests supply 0 cases ++
            [Assembly.Instr.jump defaultLabel] ++
            compiledCases.code) :=
      AssemblyProgram.PCFitsFrom.left (pre := pre)
        (first :=
          scrutinee.toAssembly ++
            Stmt.switchTests supply 0 cases ++
            [Assembly.Instr.jump defaultLabel] ++
            compiledCases.code)
        (second :=
          [ Assembly.Instr.label defaultLabel
          , Assembly.Instr.prim .pop
          , Assembly.Instr.jump endLabel
          , Assembly.Instr.label endLabel ])
        (by simpa [List.append_assoc] using hFitsSwitch)
    simpa [preTests, preTail, List.append_assoc] using
      AssemblyProgram.PCFitsFrom.end hPrefix
  have hFitPop :
      PCFits (preTail ++ [Assembly.Instr.jump defaultLabel] ++
        compiledCases.code ++ [Assembly.Instr.label defaultLabel]) := by
    have hPrefix :
        AssemblyProgram.PCFitsFrom pre
          (scrutinee.toAssembly ++
            Stmt.switchTests supply 0 cases ++
            [Assembly.Instr.jump defaultLabel] ++
            compiledCases.code ++ [Assembly.Instr.label defaultLabel]) :=
      AssemblyProgram.PCFitsFrom.left (pre := pre)
        (first :=
          scrutinee.toAssembly ++
            Stmt.switchTests supply 0 cases ++
            [Assembly.Instr.jump defaultLabel] ++
            compiledCases.code ++ [Assembly.Instr.label defaultLabel])
        (second :=
          [ Assembly.Instr.prim .pop
          , Assembly.Instr.jump endLabel
          , Assembly.Instr.label endLabel ])
        (by simpa [List.append_assoc] using hFitsSwitch)
    simpa [preTests, preTail, List.append_assoc] using
      AssemblyProgram.PCFitsFrom.end hPrefix
  have hFitJumpEnd :
      PCFits (preTail ++ [Assembly.Instr.jump defaultLabel] ++
        compiledCases.code ++
        [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop]) := by
    have hPrefix :
        AssemblyProgram.PCFitsFrom pre
          (scrutinee.toAssembly ++
            Stmt.switchTests supply 0 cases ++
            [Assembly.Instr.jump defaultLabel] ++
            compiledCases.code ++
            [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop]) :=
      AssemblyProgram.PCFitsFrom.left (pre := pre)
        (first :=
          scrutinee.toAssembly ++
            Stmt.switchTests supply 0 cases ++
            [Assembly.Instr.jump defaultLabel] ++
            compiledCases.code ++
            [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop])
        (second :=
          [Assembly.Instr.jump endLabel, Assembly.Instr.label endLabel])
        (by simpa [List.append_assoc] using hFitsSwitch)
    simpa [preTests, preTail, List.append_assoc] using
      AssemblyProgram.PCFitsFrom.end hPrefix
  have hFitEndLabel :
      PCFits (preTail ++ [Assembly.Instr.jump defaultLabel] ++
        compiledCases.code ++
        [ Assembly.Instr.label defaultLabel
        , Assembly.Instr.prim .pop
        , Assembly.Instr.jump endLabel ]) := by
    have hPrefix :
        AssemblyProgram.PCFitsFrom pre
          (scrutinee.toAssembly ++
            Stmt.switchTests supply 0 cases ++
            [Assembly.Instr.jump defaultLabel] ++
            compiledCases.code ++
            [ Assembly.Instr.label defaultLabel
            , Assembly.Instr.prim .pop
            , Assembly.Instr.jump endLabel ]) :=
      AssemblyProgram.PCFitsFrom.left (pre := pre)
        (first :=
          scrutinee.toAssembly ++
            Stmt.switchTests supply 0 cases ++
            [Assembly.Instr.jump defaultLabel] ++
            compiledCases.code ++
            [ Assembly.Instr.label defaultLabel
            , Assembly.Instr.prim .pop
            , Assembly.Instr.jump endLabel ])
        (second := [Assembly.Instr.label endLabel])
        (by simpa [List.append_assoc] using hFitsSwitch)
    simpa [preTests, preTail, List.append_assoc] using
      AssemblyProgram.PCFitsFrom.end hPrefix
  have hExactSwitch :
      ExactLabels
        (pre ++
          (scrutinee.toAssembly ++
            Stmt.switchTests supply 0 cases ++
            [Assembly.Instr.jump defaultLabel] ++
            compiledCases.code ++
            [ Assembly.Instr.label defaultLabel
            , Assembly.Instr.prim .pop
            , Assembly.Instr.jump endLabel
            , Assembly.Instr.label endLabel ]) ++ post) := by
    simpa [Stmt.compileFromCtxCore, endLabel, defaultLabel, compiledCases,
      compiledDefault, hDefaultNone, SwitchDefault.compileFromCtx,
      List.append_assoc] using hExact
  have hTestsResolve :
      EvmCompiler.Structured.Preservation.SwitchPreservation.TestsLabelsResolve
        (preTests ++ Stmt.switchTests supply 0 cases ++
          ([Assembly.Instr.jump defaultLabel] ++
            compiledCases.code ++
            [ Assembly.Instr.label defaultLabel
            , Assembly.Instr.prim .pop
            , Assembly.Instr.jump endLabel
            , Assembly.Instr.label endLabel ] ++ post))
        supply 0 cases := by
    have hCasesExact :
        ExactLabels
          ((preTests ++ Stmt.switchTests supply 0 cases ++
              [Assembly.Instr.jump defaultLabel]) ++
            compiledCases.code ++
            ([ Assembly.Instr.label defaultLabel
            , Assembly.Instr.prim .pop
            , Assembly.Instr.jump endLabel
            , Assembly.Instr.label endLabel ] ++ post)) := by
      simpa [preTests, compiledCases, List.append_assoc] using hExactSwitch
    have hResolve :=
      EvmCompiler.Structured.Preservation.SwitchPreservation.testsLabelsResolve_of_exact
        (cases := cases) (ctx := ctx)
        (endLabel := endLabel) (base := supply)
        (supply := LabelSupply.next supply) (idx := 0)
        (pre := preTests ++ Stmt.switchTests supply 0 cases ++
          [Assembly.Instr.jump defaultLabel])
        (suffix :=
          [ Assembly.Instr.label defaultLabel
          , Assembly.Instr.prim .pop
          , Assembly.Instr.jump endLabel
          , Assembly.Instr.label endLabel ] ++ post)
        hCasesExact
    simpa [compiledCases, List.append_assoc] using hResolve
  have hDefaultLabel :
      Assembly.Program.labelPc
          (preTail ++ [Assembly.Instr.jump defaultLabel] ++
            compiledCases.code ++
            [ Assembly.Instr.label defaultLabel
            , Assembly.Instr.prim .pop
            , Assembly.Instr.jump endLabel
            , Assembly.Instr.label endLabel ] ++ post)
          defaultLabel =
        some
          (Assembly.Program.byteLength
            (preTail ++ [Assembly.Instr.jump defaultLabel] ++
              compiledCases.code)) := by
    have hHere :=
      hExactSwitch.labelPc_at
        (preTail ++ [Assembly.Instr.jump defaultLabel] ++ compiledCases.code)
        defaultLabel
        ([ Assembly.Instr.prim .pop
        , Assembly.Instr.jump endLabel
        , Assembly.Instr.label endLabel ] ++ post)
        (by simp [preTests, preTail, List.append_assoc])
    simpa [preTests, preTail, List.append_assoc] using hHere
  have hEndLabel :
      Assembly.Program.labelPc
          (preTail ++ [Assembly.Instr.jump defaultLabel] ++
            compiledCases.code ++
            [ Assembly.Instr.label defaultLabel
            , Assembly.Instr.prim .pop
            , Assembly.Instr.jump endLabel
            , Assembly.Instr.label endLabel ] ++ post)
          endLabel =
        some
          (Assembly.Program.byteLength
            (preTail ++ [Assembly.Instr.jump defaultLabel] ++
              compiledCases.code ++
              [ Assembly.Instr.label defaultLabel
              , Assembly.Instr.prim .pop
              , Assembly.Instr.jump endLabel ])) := by
    have hHere :=
      hExactSwitch.labelPc_at
        (preTail ++ [Assembly.Instr.jump defaultLabel] ++
          compiledCases.code ++
          [ Assembly.Instr.label defaultLabel
          , Assembly.Instr.prim .pop
          , Assembly.Instr.jump endLabel ])
        endLabel post
        (by simp [preTests, preTail, List.append_assoc])
    simpa [preTests, preTail, List.append_assoc] using hHere
  have hScrutineeRun :
      ARunResultWithGasOracle
        (pre ++
          (Stmt.compileFromCtxCore
            (.switch scrutinee cases defaultBody) ctx supply).code ++ post)
        oracle cursor target
        (fun result targetCursorAfterScrutinee =>
          match result with
          | .running targetAfterScrutinee =>
              targetCursorAfterScrutinee = cursorAfterScrutinee ∧
                Frame.StateRel stateAfterScrutinee targetAfterScrutinee tokens ∧
                  targetAfterScrutinee.pc =
                    Assembly.Program.pcAfter preTests
          | .halted _ => False) := by
    have hRun :=
      FrameStateRel.source_run_code_ctx_result_withGasOracle
        (source := source) (final := stateAfterScrutinee)
        (target := target) (tokens := tokens) (code := scrutinee)
        (pre := pre)
        (post :=
          Stmt.switchTests supply 0 cases ++
            [Assembly.Instr.jump defaultLabel] ++
            compiledCases.code ++
            [ Assembly.Instr.label defaultLabel
            , Assembly.Instr.prim .pop
            , Assembly.Instr.jump endLabel
            , Assembly.Instr.label endLabel ] ++ post)
        hScrutineeSafe hScrutineeFrame hScrutineeFits hPc hRel hScrutinee
    simpa [Stmt.compileFromCtxCore, endLabel, defaultLabel, compiledCases,
      compiledDefault, hDefaultNone, SwitchDefault.compileFromCtx,
      preTests, List.append_assoc] using hRun
  refine
    ARunResultWithGasOracle.bind_running
      (program :=
        pre ++
          (Stmt.compileFromCtxCore
            (.switch scrutinee cases defaultBody) ctx supply).code ++ post)
      (middle := fun targetAfterScrutinee targetCursorAfterScrutinee =>
        targetCursorAfterScrutinee = cursorAfterScrutinee ∧
          Frame.StateRel stateAfterScrutinee targetAfterScrutinee tokens ∧
            targetAfterScrutinee.pc = Assembly.Program.pcAfter preTests)
      hScrutineeRun ?_
  intro targetAfterScrutinee targetCursorAfterScrutinee hAfterScrutinee
  rcases hAfterScrutinee with
    ⟨hTargetCursorAfterScrutinee, hRelAfterScrutinee, hPcAfterScrutinee⟩
  subst targetCursorAfterScrutinee
  have hTestsRun :
      ARunResultWithGasOracle
        (pre ++
          (Stmt.compileFromCtxCore
            (.switch scrutinee cases defaultBody) ctx supply).code ++ post)
        oracle cursorAfterScrutinee targetAfterScrutinee
        (fun result targetCursorAfterTests =>
          match result with
          | .running targetAfterTests =>
              targetCursorAfterTests = cursorAfterScrutinee ∧
                Frame.StateRel stateAfterScrutinee targetAfterTests tokens ∧
                  targetAfterTests.pc = Assembly.Program.pcAfter preTail
          | .halted _ => False) := by
    have hRun :=
      tests_fallthrough_result_ctx_withGasOracle
        (base := supply) (idx := 0) (cases := cases)
        (pre := preTests)
        (post :=
          [Assembly.Instr.jump defaultLabel] ++
            compiledCases.code ++
            [ Assembly.Instr.label defaultLabel
            , Assembly.Instr.prim .pop
            , Assembly.Instr.jump endLabel
            , Assembly.Instr.label endLabel ] ++ post)
        (source := stateAfterScrutinee)
        (target := targetAfterScrutinee) (tokens := tokens)
        (stack := stack) (value := value)
        (oracle := oracle) (cursor := cursorAfterScrutinee)
        hTestsFits
        (by simpa [List.append_assoc] using hTestsResolve)
        (EvmCompiler.Structured.Preservation.SwitchPreservation.no_match_of_select_none
          hSelect)
        hPcAfterScrutinee hRelAfterScrutinee hPop
    simpa [Stmt.compileFromCtxCore, endLabel, defaultLabel, compiledCases,
      compiledDefault, hDefaultNone, SwitchDefault.compileFromCtx,
      preTests, preTail, List.append_assoc] using hRun
  refine
    ARunResultWithGasOracle.bind_running
      (program :=
        pre ++
          (Stmt.compileFromCtxCore
            (.switch scrutinee cases defaultBody) ctx supply).code ++ post)
      (middle := fun targetAfterTests targetCursorAfterTests =>
        targetCursorAfterTests = cursorAfterScrutinee ∧
          Frame.StateRel stateAfterScrutinee targetAfterTests tokens ∧
            targetAfterTests.pc = Assembly.Program.pcAfter preTail)
      hTestsRun ?_
  intro targetAfterTests targetCursorAfterTests hAfterTests
  rcases hAfterTests with
    ⟨hTargetCursorAfterTests, hRelAfterTests, hPcAfterTests⟩
  subst targetCursorAfterTests
  have hTailRun :=
    default_none_tail_result_ctx_withGasOracle
      (pre := preTail) (between := compiledCases.code) (post := post)
      (defaultLabel := defaultLabel) (endLabel := endLabel)
      (source := stateAfterScrutinee) (target := targetAfterTests)
      (tokens := tokens) (stack := stack) (value := value)
      (oracle := oracle) (cursor := cursorAfterScrutinee)
      hFitJumpDefault hFitDefaultLabel hFitPop hFitJumpEnd hFitEndLabel
      hPcAfterTests hRelAfterTests
      (by simpa [List.append_assoc] using hDefaultLabel)
      (by simpa [List.append_assoc] using hEndLabel)
      hPop
  exact ARunResultWithGasOracle.mono
    (by
      simpa [Stmt.compileFromCtxCore, endLabel, defaultLabel, compiledCases,
        compiledDefault, hDefaultNone, SwitchDefault.compileFromCtx,
        preTests, preTail, List.append_assoc] using hTailRun)
    (by
      intro result targetCursorFinal hResult
      cases result with
      | halted halt =>
          cases hResult
      | running targetFinal =>
          rcases hResult with ⟨hCursorFinal, hRelFinal, hPcFinal⟩
          exact
            ⟨ hCursorFinal
            , CompiledOutcomeRel.regular hRelFinal
                (by
                  simpa [Stmt.compileFromCtxCore, endLabel, defaultLabel,
                    compiledCases, compiledDefault, hDefaultNone,
                    SwitchDefault.compileFromCtx, preTests, preTail,
                    List.append_assoc] using hPcFinal)
            ⟩)

theorem switch_default_some_result_ctx_withGasOracle {program : Program}
    {ctx : CompileContext} {supply : LabelSupply} {scrutinee : Code}
    {cases : List (Word × Block)} {defaultBody : Option Block}
    {body : Block} {fuel : Nat}
    {source stateAfterScrutinee : RunState} {outcome : Outcome}
    {target : EVMState} {tokens : List Word}
    {stack : EvmYul.Stack Word} {value : Word}
    {pre post : Assembly.Program}
    {oracle : GasOracle} {cursor cursorAfterScrutinee cursorFinal : Nat}
    (hScrutineeSafe : Code.RunnerSafeWithGasOracle scrutinee)
    (hScrutineeFrame : Code.FrameSafeWithGasOracle scrutinee)
    (hBody :
      BlockPreservesWithGasOracle program ctx
        (SwitchCases.compileFromCtx cases ctx (LabelSupply.label supply 0)
          supply (LabelSupply.next supply) 0).next
        body)
    (hFits :
      AssemblyProgram.PCFitsFrom pre
        (Stmt.compileFromCtxCore
          (.switch scrutinee cases defaultBody) ctx supply).code)
    (hResolve :
      ContextLabelsResolve
        (pre ++
          (Stmt.compileFromCtxCore
            (.switch scrutinee cases defaultBody) ctx supply).code ++ post)
        ctx)
    (hExact :
      ExactLabels
        (pre ++
          (Stmt.compileFromCtxCore
            (.switch scrutinee cases defaultBody) ctx supply).code ++ post))
    (hPc : target.pc = Assembly.Program.pcAfter pre)
    (hRel : Frame.StateRel source target tokens)
    (hScrutinee :
      Code.runStateWithGasOracle scrutinee oracle cursor source =
        .ok (stateAfterScrutinee, cursorAfterScrutinee))
    (hPop : stateAfterScrutinee.evm.stack.pop = some (stack, value))
    (hNoMatch : ∀ probe body', (probe, body') ∈ cases → probe ≠ value)
    (hDefaultBody : defaultBody = some body)
    (hBodyEval :
      Block.EvalWithGasOracle program oracle fuel body cursorAfterScrutinee
        (stateAfterScrutinee.withEVM
          { stateAfterScrutinee.evm with stack := stack })
        outcome cursorFinal) :
    ARunResultWithGasOracle
      (pre ++
        (Stmt.compileFromCtxCore
          (.switch scrutinee cases defaultBody) ctx supply).code ++ post)
      oracle cursor target
      (fun result targetCursorFinal =>
        targetCursorFinal = cursorFinal ∧
          CompiledOutcomeRel
            (pre ++
              (Stmt.compileFromCtxCore
                (.switch scrutinee cases defaultBody) ctx supply).code ++ post)
            ctx
            (Assembly.Program.pcAfter
              (pre ++
                (Stmt.compileFromCtxCore
                  (.switch scrutinee cases defaultBody) ctx supply).code))
            outcome result tokens) := by
  let endLabel := LabelSupply.label supply 0
  let defaultLabel := LabelSupply.label supply 1
  let compiledCases :=
    SwitchCases.compileFromCtx cases ctx endLabel supply
      (LabelSupply.next supply) 0
  let compiledBody := Block.compileFromCtx body ctx compiledCases.next
  let preTests : Assembly.Program := pre ++ scrutinee.toAssembly
  let preTail : Assembly.Program :=
    preTests ++ Stmt.switchTests supply 0 cases
  have hBodyPreserves :
      BlockPreservesWithGasOracle program ctx compiledCases.next body := by
    change BlockPreservesWithGasOracle program ctx compiledCases.next body at hBody
    exact hBody
  have hFitsSwitch :
      AssemblyProgram.PCFitsFrom pre
        (scrutinee.toAssembly ++
          Stmt.switchTests supply 0 cases ++
          [Assembly.Instr.jump defaultLabel] ++
          compiledCases.code ++
          [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop] ++
          compiledBody.code ++
          [Assembly.Instr.jump endLabel, Assembly.Instr.label endLabel]) := by
    simpa [Stmt.compileFromCtxCore, endLabel, defaultLabel, compiledCases,
      compiledBody, hDefaultBody, SwitchDefault.compileFromCtx,
      List.append_assoc] using hFits
  have hScrutineeFitsAsm :
      AssemblyProgram.PCFitsFrom pre scrutinee.toAssembly :=
    AssemblyProgram.PCFitsFrom.left (pre := pre)
      (first := scrutinee.toAssembly)
      (second :=
        Stmt.switchTests supply 0 cases ++
          [Assembly.Instr.jump defaultLabel] ++
          compiledCases.code ++
          [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop] ++
          compiledBody.code ++
          [Assembly.Instr.jump endLabel, Assembly.Instr.label endLabel])
      (by simpa [List.append_assoc] using hFitsSwitch)
  have hScrutineeFits : Code.PCFitsFrom pre scrutinee :=
    Code.PCFitsFrom.of_assembly hScrutineeFitsAsm
  have hAfterScrutineeFits :
      AssemblyProgram.PCFitsFrom preTests
        (Stmt.switchTests supply 0 cases ++
          [Assembly.Instr.jump defaultLabel] ++
          compiledCases.code ++
          [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop] ++
          compiledBody.code ++
          [Assembly.Instr.jump endLabel, Assembly.Instr.label endLabel]) := by
    simpa [preTests, List.append_assoc] using
      AssemblyProgram.PCFitsFrom.right (pre := pre)
        (first := scrutinee.toAssembly)
        (second :=
          Stmt.switchTests supply 0 cases ++
            [Assembly.Instr.jump defaultLabel] ++
            compiledCases.code ++
            [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop] ++
            compiledBody.code ++
            [Assembly.Instr.jump endLabel, Assembly.Instr.label endLabel])
        (by simpa [List.append_assoc] using hFitsSwitch)
  have hTestsFits :
      AssemblyProgram.PCFitsFrom preTests
        (Stmt.switchTests supply 0 cases) :=
    AssemblyProgram.PCFitsFrom.left (pre := preTests)
      (first := Stmt.switchTests supply 0 cases)
      (second :=
        [Assembly.Instr.jump defaultLabel] ++ compiledCases.code ++
          [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop] ++
          compiledBody.code ++
          [Assembly.Instr.jump endLabel, Assembly.Instr.label endLabel])
      (by simpa [List.append_assoc] using hAfterScrutineeFits)
  have hFitJumpDefault : PCFits preTail := by
    simpa [preTail, List.append_assoc] using
      AssemblyProgram.PCFitsFrom.end hTestsFits
  have hFitDefaultLabel :
      PCFits (preTail ++ [Assembly.Instr.jump defaultLabel] ++
        compiledCases.code) := by
    have hPrefix :
        AssemblyProgram.PCFitsFrom pre
          (scrutinee.toAssembly ++
            Stmt.switchTests supply 0 cases ++
            [Assembly.Instr.jump defaultLabel] ++
            compiledCases.code) :=
      AssemblyProgram.PCFitsFrom.left (pre := pre)
        (first :=
          scrutinee.toAssembly ++
            Stmt.switchTests supply 0 cases ++
            [Assembly.Instr.jump defaultLabel] ++
            compiledCases.code)
        (second :=
          [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop] ++
            compiledBody.code ++
            [Assembly.Instr.jump endLabel, Assembly.Instr.label endLabel])
        (by simpa [List.append_assoc] using hFitsSwitch)
    simpa [preTests, preTail, List.append_assoc] using
      AssemblyProgram.PCFitsFrom.end hPrefix
  have hFitPop :
      PCFits (preTail ++ [Assembly.Instr.jump defaultLabel] ++
        compiledCases.code ++ [Assembly.Instr.label defaultLabel]) := by
    have hPrefix :
        AssemblyProgram.PCFitsFrom pre
          (scrutinee.toAssembly ++
            Stmt.switchTests supply 0 cases ++
            [Assembly.Instr.jump defaultLabel] ++
            compiledCases.code ++ [Assembly.Instr.label defaultLabel]) :=
      AssemblyProgram.PCFitsFrom.left (pre := pre)
        (first :=
          scrutinee.toAssembly ++
            Stmt.switchTests supply 0 cases ++
            [Assembly.Instr.jump defaultLabel] ++
            compiledCases.code ++ [Assembly.Instr.label defaultLabel])
        (second :=
          [Assembly.Instr.prim .pop] ++ compiledBody.code ++
            [Assembly.Instr.jump endLabel, Assembly.Instr.label endLabel])
        (by simpa [List.append_assoc] using hFitsSwitch)
    simpa [preTests, preTail, List.append_assoc] using
      AssemblyProgram.PCFitsFrom.end hPrefix
  have hBodyFits :
      AssemblyProgram.PCFitsFrom
        (preTail ++ [Assembly.Instr.jump defaultLabel] ++
          compiledCases.code ++
          [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop])
        compiledBody.code := by
    have hAfterPop :
        AssemblyProgram.PCFitsFrom
          (preTail ++ [Assembly.Instr.jump defaultLabel] ++
            compiledCases.code ++
            [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop])
          (compiledBody.code ++
            [Assembly.Instr.jump endLabel, Assembly.Instr.label endLabel]) := by
      simpa [preTests, preTail, List.append_assoc] using
        AssemblyProgram.PCFitsFrom.right (pre := pre)
          (first :=
            scrutinee.toAssembly ++
              Stmt.switchTests supply 0 cases ++
              [Assembly.Instr.jump defaultLabel] ++
              compiledCases.code ++
              [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop])
          (second :=
            compiledBody.code ++
              [Assembly.Instr.jump endLabel, Assembly.Instr.label endLabel])
          (by simpa [List.append_assoc] using hFitsSwitch)
    exact AssemblyProgram.PCFitsFrom.left
      (pre :=
        preTail ++ [Assembly.Instr.jump defaultLabel] ++
          compiledCases.code ++
          [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop])
      (first := compiledBody.code)
      (second :=
        [Assembly.Instr.jump endLabel, Assembly.Instr.label endLabel])
      hAfterPop
  have hFitJumpEnd :
      PCFits
        (preTail ++ [Assembly.Instr.jump defaultLabel] ++
          compiledCases.code ++
          [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop] ++
          compiledBody.code) := by
    simpa [List.append_assoc] using
      AssemblyProgram.PCFitsFrom.end hBodyFits
  have hFitEndLabel :
      PCFits
        (preTail ++ [Assembly.Instr.jump defaultLabel] ++
          compiledCases.code ++
          [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop] ++
          compiledBody.code ++ [Assembly.Instr.jump endLabel]) := by
    have hPrefix :
        AssemblyProgram.PCFitsFrom pre
          (scrutinee.toAssembly ++
            Stmt.switchTests supply 0 cases ++
            [Assembly.Instr.jump defaultLabel] ++
            compiledCases.code ++
            [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop] ++
            compiledBody.code ++ [Assembly.Instr.jump endLabel]) :=
      AssemblyProgram.PCFitsFrom.left (pre := pre)
        (first :=
          scrutinee.toAssembly ++
            Stmt.switchTests supply 0 cases ++
            [Assembly.Instr.jump defaultLabel] ++
            compiledCases.code ++
            [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop] ++
            compiledBody.code ++ [Assembly.Instr.jump endLabel])
        (second := [Assembly.Instr.label endLabel])
        (by simpa [List.append_assoc] using hFitsSwitch)
    simpa [preTests, preTail, List.append_assoc] using
      AssemblyProgram.PCFitsFrom.end hPrefix
  have hExactSwitch :
      ExactLabels
        (pre ++
          (scrutinee.toAssembly ++
            Stmt.switchTests supply 0 cases ++
            [Assembly.Instr.jump defaultLabel] ++
            compiledCases.code ++
            [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop] ++
            compiledBody.code ++
            [Assembly.Instr.jump endLabel, Assembly.Instr.label endLabel]) ++
            post) := by
    simpa [Stmt.compileFromCtxCore, endLabel, defaultLabel, compiledCases,
      compiledBody, hDefaultBody, SwitchDefault.compileFromCtx,
      List.append_assoc] using hExact
  have hResolveSwitch :
      ContextLabelsResolve
        (pre ++
          (scrutinee.toAssembly ++
            Stmt.switchTests supply 0 cases ++
            [Assembly.Instr.jump defaultLabel] ++
            compiledCases.code ++
            [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop] ++
            compiledBody.code ++
            [Assembly.Instr.jump endLabel, Assembly.Instr.label endLabel]) ++
            post)
        ctx := by
    simpa [Stmt.compileFromCtxCore, endLabel, defaultLabel, compiledCases,
      compiledBody, hDefaultBody, SwitchDefault.compileFromCtx,
      List.append_assoc] using hResolve
  have hTestsResolve :
      EvmCompiler.Structured.Preservation.SwitchPreservation.TestsLabelsResolve
        (preTests ++ Stmt.switchTests supply 0 cases ++
          ([Assembly.Instr.jump defaultLabel] ++
            compiledCases.code ++
            [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop] ++
            compiledBody.code ++
            [Assembly.Instr.jump endLabel, Assembly.Instr.label endLabel] ++
            post))
        supply 0 cases := by
    have hCasesExact :
        ExactLabels
          ((preTests ++ Stmt.switchTests supply 0 cases ++
              [Assembly.Instr.jump defaultLabel]) ++
            compiledCases.code ++
            ([Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop] ++
              compiledBody.code ++
              [Assembly.Instr.jump endLabel, Assembly.Instr.label endLabel] ++
              post)) := by
      simpa [preTests, compiledCases, List.append_assoc] using hExactSwitch
    have hResolveCases :=
      EvmCompiler.Structured.Preservation.SwitchPreservation.testsLabelsResolve_of_exact
        (cases := cases) (ctx := ctx)
        (endLabel := endLabel) (base := supply)
        (supply := LabelSupply.next supply) (idx := 0)
        (pre := preTests ++ Stmt.switchTests supply 0 cases ++
          [Assembly.Instr.jump defaultLabel])
        (suffix :=
          [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop] ++
            compiledBody.code ++
            [Assembly.Instr.jump endLabel, Assembly.Instr.label endLabel] ++
            post)
        hCasesExact
    simpa [compiledCases, List.append_assoc] using hResolveCases
  have hDefaultLabel :
      Assembly.Program.labelPc
          (preTail ++ [Assembly.Instr.jump defaultLabel] ++
            compiledCases.code ++
            [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop] ++
            compiledBody.code ++
            [Assembly.Instr.jump endLabel, Assembly.Instr.label endLabel] ++
            post)
          defaultLabel =
        some
          (Assembly.Program.byteLength
            (preTail ++ [Assembly.Instr.jump defaultLabel] ++
              compiledCases.code)) := by
    have hHere :=
      hExactSwitch.labelPc_at
        (preTail ++ [Assembly.Instr.jump defaultLabel] ++ compiledCases.code)
        defaultLabel
        ([Assembly.Instr.prim .pop] ++ compiledBody.code ++
          [Assembly.Instr.jump endLabel, Assembly.Instr.label endLabel] ++ post)
        (by simp [preTests, preTail, List.append_assoc])
    simpa [preTests, preTail, List.append_assoc] using hHere
  have hEndLabel :
      Assembly.Program.labelPc
          (preTail ++ [Assembly.Instr.jump defaultLabel] ++
            compiledCases.code ++
            [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop] ++
            compiledBody.code ++
            [Assembly.Instr.jump endLabel, Assembly.Instr.label endLabel] ++
            post)
          endLabel =
        some
          (Assembly.Program.byteLength
            (preTail ++ [Assembly.Instr.jump defaultLabel] ++
              compiledCases.code ++
              [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop] ++
              compiledBody.code ++ [Assembly.Instr.jump endLabel])) := by
    have hHere :=
      hExactSwitch.labelPc_at
        (preTail ++ [Assembly.Instr.jump defaultLabel] ++
          compiledCases.code ++
          [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop] ++
          compiledBody.code ++ [Assembly.Instr.jump endLabel])
        endLabel post
        (by simp [preTests, preTail, List.append_assoc])
    simpa [preTests, preTail, List.append_assoc] using hHere
  have hBodyResolve :
      ContextLabelsResolve
        (preTail ++ [Assembly.Instr.jump defaultLabel] ++
          compiledCases.code ++
          [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop] ++
          compiledBody.code ++
          ([Assembly.Instr.jump endLabel, Assembly.Instr.label endLabel] ++
            post))
        ctx := by
    simpa [preTests, preTail, List.append_assoc] using hResolveSwitch
  have hBodyExact :
      ExactLabels
        (preTail ++ [Assembly.Instr.jump defaultLabel] ++
          compiledCases.code ++
          [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop] ++
          compiledBody.code ++
          ([Assembly.Instr.jump endLabel, Assembly.Instr.label endLabel] ++
            post)) := by
    simpa [preTests, preTail, List.append_assoc] using hExactSwitch
  have hScrutineeRun :
      ARunResultWithGasOracle
        (pre ++
          (Stmt.compileFromCtxCore
            (.switch scrutinee cases defaultBody) ctx supply).code ++ post)
        oracle cursor target
        (fun result targetCursorAfterScrutinee =>
          match result with
          | .running targetAfterScrutinee =>
              targetCursorAfterScrutinee = cursorAfterScrutinee ∧
                Frame.StateRel stateAfterScrutinee targetAfterScrutinee tokens ∧
                  targetAfterScrutinee.pc =
                    Assembly.Program.pcAfter preTests
          | .halted _ => False) := by
    have hRun :=
      FrameStateRel.source_run_code_ctx_result_withGasOracle
        (source := source) (final := stateAfterScrutinee)
        (target := target) (tokens := tokens) (code := scrutinee)
        (pre := pre)
        (post :=
          Stmt.switchTests supply 0 cases ++
            [Assembly.Instr.jump defaultLabel] ++
            compiledCases.code ++
            [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop] ++
            compiledBody.code ++
            [Assembly.Instr.jump endLabel, Assembly.Instr.label endLabel] ++
            post)
        hScrutineeSafe hScrutineeFrame hScrutineeFits hPc hRel hScrutinee
    simpa [Stmt.compileFromCtxCore, endLabel, defaultLabel, compiledCases,
      compiledBody, hDefaultBody, SwitchDefault.compileFromCtx,
      preTests, List.append_assoc] using hRun
  refine
    ARunResultWithGasOracle.bind_running
      (program :=
        pre ++
          (Stmt.compileFromCtxCore
            (.switch scrutinee cases defaultBody) ctx supply).code ++ post)
      (middle := fun targetAfterScrutinee targetCursorAfterScrutinee =>
        targetCursorAfterScrutinee = cursorAfterScrutinee ∧
          Frame.StateRel stateAfterScrutinee targetAfterScrutinee tokens ∧
            targetAfterScrutinee.pc = Assembly.Program.pcAfter preTests)
      hScrutineeRun ?_
  intro targetAfterScrutinee targetCursorAfterScrutinee hAfterScrutinee
  rcases hAfterScrutinee with
    ⟨hTargetCursorAfterScrutinee, hRelAfterScrutinee, hPcAfterScrutinee⟩
  subst targetCursorAfterScrutinee
  have hTestsRun :
      ARunResultWithGasOracle
        (pre ++
          (Stmt.compileFromCtxCore
            (.switch scrutinee cases defaultBody) ctx supply).code ++ post)
        oracle cursorAfterScrutinee targetAfterScrutinee
        (fun result targetCursorAfterTests =>
          match result with
          | .running targetAfterTests =>
              targetCursorAfterTests = cursorAfterScrutinee ∧
                Frame.StateRel stateAfterScrutinee targetAfterTests tokens ∧
                  targetAfterTests.pc = Assembly.Program.pcAfter preTail
          | .halted _ => False) := by
    have hRun :=
      tests_fallthrough_result_ctx_withGasOracle
        (base := supply) (idx := 0) (cases := cases)
        (pre := preTests)
        (post :=
          [Assembly.Instr.jump defaultLabel] ++
            compiledCases.code ++
            [Assembly.Instr.label defaultLabel, Assembly.Instr.prim .pop] ++
            compiledBody.code ++
            [Assembly.Instr.jump endLabel, Assembly.Instr.label endLabel] ++
            post)
        (source := stateAfterScrutinee)
        (target := targetAfterScrutinee) (tokens := tokens)
        (stack := stack) (value := value)
        (oracle := oracle) (cursor := cursorAfterScrutinee)
        hTestsFits
        (by simpa [List.append_assoc] using hTestsResolve)
        hNoMatch
        hPcAfterScrutinee hRelAfterScrutinee hPop
    simpa [Stmt.compileFromCtxCore, endLabel, defaultLabel, compiledCases,
      compiledBody, hDefaultBody, SwitchDefault.compileFromCtx,
      preTests, preTail, List.append_assoc] using hRun
  refine
    ARunResultWithGasOracle.bind_running
      (program :=
        pre ++
          (Stmt.compileFromCtxCore
            (.switch scrutinee cases defaultBody) ctx supply).code ++ post)
      (middle := fun targetAfterTests targetCursorAfterTests =>
        targetCursorAfterTests = cursorAfterScrutinee ∧
          Frame.StateRel stateAfterScrutinee targetAfterTests tokens ∧
            targetAfterTests.pc = Assembly.Program.pcAfter preTail)
      hTestsRun ?_
  intro targetAfterTests targetCursorAfterTests hAfterTests
  rcases hAfterTests with
    ⟨hTargetCursorAfterTests, hRelAfterTests, hPcAfterTests⟩
  subst targetCursorAfterTests
  have hTailRun :=
    default_some_tail_result_ctx_withGasOracle
      (program := program) (ctx := ctx) (bodySupply := compiledCases.next)
      (body := body)
      (pre := preTail) (between := compiledCases.code) (post := post)
      (defaultLabel := defaultLabel) (endLabel := endLabel)
      (fuel := fuel) (source := stateAfterScrutinee)
      (outcome := outcome) (target := targetAfterTests) (tokens := tokens)
      (stack := stack) (value := value)
      (oracle := oracle) (cursor := cursorAfterScrutinee)
      (cursorFinal := cursorFinal)
      hBodyPreserves
      hFitJumpDefault hFitDefaultLabel hFitPop
      (by simpa [compiledBody] using hBodyFits)
      (by simpa [compiledBody] using hFitJumpEnd)
      (by simpa [compiledBody] using hFitEndLabel)
      (by simpa [compiledBody, List.append_assoc] using hBodyResolve)
      (by simpa [compiledBody, List.append_assoc] using hBodyExact)
      (by simpa [compiledBody, List.append_assoc] using hDefaultLabel)
      (by simpa [compiledBody, List.append_assoc] using hEndLabel)
      hPcAfterTests hRelAfterTests hPop hBodyEval
  exact ARunResultWithGasOracle.mono
    (by
      simpa [Stmt.compileFromCtxCore, endLabel, defaultLabel, compiledCases,
        compiledBody, hDefaultBody, SwitchDefault.compileFromCtx,
        preTests, preTail, List.append_assoc] using hTailRun)
    (by
      intro result targetCursorFinal hResult
      simpa [Stmt.compileFromCtxCore, endLabel, defaultLabel, compiledCases,
        compiledBody, hDefaultBody, SwitchDefault.compileFromCtx,
        preTests, preTail, List.append_assoc] using hResult)

end SwitchPreservation

namespace ProcedureLayoutPreservation

set_option maxHeartbeats 800000 in
theorem preserves_switch_in_programLayout_upTo_withGasOracle
    {program : Program}
    {layout :
      _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.ProgramLayout
        program}
    {maxFuel : Nat}
    {ctx : CompileContext} {supply : LabelSupply}
    {scrutinee : Code} {cases : List (Word × Block)}
    {defaultBody : Option Block}
    (hScrutineeSafe : Code.RunnerSafeWithGasOracle scrutinee)
    (hScrutineeFrame : Code.FrameSafeWithGasOracle scrutinee)
    (hCases :
      SwitchCasesPreservesInProgramLayoutWithGasOracleUpTo layout maxFuel ctx
        (LabelSupply.label supply 0) supply (LabelSupply.next supply) 0
        cases)
    (hDefault :
      SwitchDefaultPreservesInProgramLayoutWithGasOracleUpTo layout maxFuel ctx
        (SwitchCases.compileFromCtx cases ctx (LabelSupply.label supply 0)
          supply (LabelSupply.next supply) 0).next defaultBody) :
    StmtPreservesInProgramLayoutWithGasOracleUpTo layout maxFuel ctx supply
      (.switch scrutinee cases defaultBody) := by
  intro fuel source outcome target tokens oracle cursor cursorFinal hLt
    hProgramWF hCtxProcs hCalls hResolve segment hPc hRel hEval
  let pre := segment.pre
  let post := segment.post
  let endLabel := LabelSupply.label supply 0
  let defaultLabel := LabelSupply.label supply 1
  let compiledCases :=
    SwitchCases.compileFromCtx cases ctx endLabel supply
      (LabelSupply.next supply) 0
  let compiledDefault :=
    SwitchDefault.compileFromCtx defaultBody ctx endLabel defaultLabel
      compiledCases.next
  let preTests : Assembly.Program := pre ++ scrutinee.toAssembly
  let tailCode : Assembly.Program :=
    Stmt.switchTests supply 0 cases ++
      [Assembly.Instr.jump defaultLabel] ++ ([] : Assembly.Program) ++
      compiledCases.code ++ compiledDefault.code ++
      [Assembly.Instr.label endLabel]
  have hLocalAsm :
      pre ++
        (Stmt.compileFromCtxCore
          (.switch scrutinee cases defaultBody) ctx supply).code ++ post =
        layout.asm := by
    simpa [pre, post] using segment.hAsm.symm
  have hCallsAppend :
      CallsIncluded (compiledCases.calls ++ compiledDefault.calls)
        layout.sites := by
    simpa [Stmt.compileFromCtxCore, endLabel, defaultLabel, compiledCases,
      compiledDefault, List.append_assoc] using hCalls
  have hCaseCalls : CallsIncluded compiledCases.calls layout.sites :=
    _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.CallsIncluded.left
      hCallsAppend
  have hDefaultCalls : CallsIncluded compiledDefault.calls layout.sites :=
    _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.CallsIncluded.right
      hCallsAppend
  have hFitsSwitch :
      AssemblyProgram.PCFitsFrom pre
        (scrutinee.toAssembly ++
          Stmt.switchTests supply 0 cases ++
          [Assembly.Instr.jump defaultLabel] ++
          compiledCases.code ++ compiledDefault.code ++
          [Assembly.Instr.label endLabel]) := by
    simpa [pre, Stmt.compileFromCtxCore, endLabel, defaultLabel,
      compiledCases, compiledDefault, List.append_assoc] using segment.hFits
  have hScrutineeFitsAsm :
      AssemblyProgram.PCFitsFrom pre scrutinee.toAssembly :=
    AssemblyProgram.PCFitsFrom.left (pre := pre)
      (first := scrutinee.toAssembly)
      (second :=
        Stmt.switchTests supply 0 cases ++
          [Assembly.Instr.jump defaultLabel] ++
          compiledCases.code ++ compiledDefault.code ++
          [Assembly.Instr.label endLabel])
      (by simpa [List.append_assoc] using hFitsSwitch)
  have hScrutineeFits : Code.PCFitsFrom pre scrutinee :=
    Code.PCFitsFrom.of_assembly hScrutineeFitsAsm
  have hTailFits :
      AssemblyProgram.PCFitsFrom preTests tailCode := by
    have hRight :
        AssemblyProgram.PCFitsFrom preTests
          (Stmt.switchTests supply 0 cases ++
            [Assembly.Instr.jump defaultLabel] ++
            compiledCases.code ++ compiledDefault.code ++
            [Assembly.Instr.label endLabel]) := by
      simpa [preTests, List.append_assoc] using
        AssemblyProgram.PCFitsFrom.right (pre := pre)
          (first := scrutinee.toAssembly)
          (second :=
            Stmt.switchTests supply 0 cases ++
              [Assembly.Instr.jump defaultLabel] ++
              compiledCases.code ++ compiledDefault.code ++
              [Assembly.Instr.label endLabel])
          (by simpa [List.append_assoc] using hFitsSwitch)
    simpa [tailCode, List.append_assoc] using hRight
  have hExactLocal :
      ExactLabels
        (pre ++
          (Stmt.compileFromCtxCore
            (.switch scrutinee cases defaultBody) ctx supply).code ++ post) :=
    ExactLabels.cast_asm hLocalAsm.symm layout.exactLabels
  cases hEval with
  | switch_none hScrutinee hPop hSelect =>
      have hRunLocal :=
        SwitchPreservation.switch_none_result_ctx_withGasOracle
          (ctx := ctx) (supply := supply) (scrutinee := scrutinee)
          (cases := cases) (defaultBody := defaultBody)
          (source := source) (stateAfterScrutinee := _)
          (target := target) (tokens := tokens)
          (stack := _) (value := _) (pre := pre) (post := post)
          (oracle := oracle) (cursor := cursor)
          (cursorAfterScrutinee := cursorFinal)
          hScrutineeSafe hScrutineeFrame
          (by simpa [pre] using segment.hFits)
          hExactLocal
          (by simpa [pre, CodeSegment.startPc] using hPc)
          hRel hScrutinee hPop hSelect
      exact
        ARunResultWithGasOracle.cast_program_mono hLocalAsm hRunLocal
          (by
            intro result targetCursorFinal hResult
            rcases hResult with ⟨hCursorFinal, hCompiled⟩
            cases result with
            | halted halt =>
                cases hCompiled
            | running targetState =>
                exact
                  ⟨hCursorFinal, by
                    simpa [pre, post, CodeSegment.fallthroughPc,
                      Stmt.compileFromCtxCore, endLabel, defaultLabel,
                      compiledCases, compiledDefault, CompiledOutcomeRel,
                      Outcome.regular, List.append_assoc] using hCompiled⟩)
  | switch_some hScrutinee hPop hStateAfterPop hSelect hBodyEval =>
      rename_i bodyFuel cursorAfterScrutinee stateAfterScrutinee stateAfterPop stack value selected
      subst stateAfterPop
      have hBodyLt : bodyFuel < maxFuel := by omega
      have hScrutineeRunLocal :
          ARunResultWithGasOracle
            (pre ++
              (Stmt.compileFromCtxCore
                (.switch scrutinee cases defaultBody) ctx supply).code ++ post)
            oracle cursor target
            (fun result targetCursorAfterScrutinee =>
              match result with
              | .running targetAfterScrutinee =>
                  targetCursorAfterScrutinee = cursorAfterScrutinee ∧
                    Frame.StateRel stateAfterScrutinee targetAfterScrutinee
                      tokens ∧
                      targetAfterScrutinee.pc =
                        Assembly.Program.pcAfter preTests
              | .halted _ => False) := by
        have hRun :=
          FrameStateRel.source_run_code_ctx_result_withGasOracle
            (source := source) (final := stateAfterScrutinee)
            (target := target) (tokens := tokens) (code := scrutinee)
            (pre := pre)
            (post :=
              Stmt.switchTests supply 0 cases ++
                [Assembly.Instr.jump defaultLabel] ++
                compiledCases.code ++ compiledDefault.code ++
                [Assembly.Instr.label endLabel] ++ post)
            hScrutineeSafe hScrutineeFrame hScrutineeFits
            (by simpa [pre, CodeSegment.startPc] using hPc)
            hRel hScrutinee
        simpa [Stmt.compileFromCtxCore, endLabel, defaultLabel, compiledCases,
          compiledDefault, preTests, List.append_assoc] using hRun
      have hScrutineeRun :
          ARunResultWithGasOracle layout.asm oracle cursor target
            (fun result targetCursorAfterScrutinee =>
              match result with
              | .running targetAfterScrutinee =>
                  targetCursorAfterScrutinee = cursorAfterScrutinee ∧
                    Frame.StateRel stateAfterScrutinee targetAfterScrutinee
                      tokens ∧
                      targetAfterScrutinee.pc =
                        Assembly.Program.pcAfter preTests
              | .halted _ => False) :=
        ARunResultWithGasOracle.cast_program hLocalAsm hScrutineeRunLocal
      refine
        ARunResultWithGasOracle.bind_running
          (program := layout.asm)
          (middle := fun targetAfterScrutinee targetCursorAfterScrutinee =>
            targetCursorAfterScrutinee = cursorAfterScrutinee ∧
              Frame.StateRel stateAfterScrutinee targetAfterScrutinee tokens ∧
                targetAfterScrutinee.pc = Assembly.Program.pcAfter preTests)
          hScrutineeRun ?_
      intro targetAfterScrutinee targetCursorAfterScrutinee hAfterScrutinee
      rcases hAfterScrutinee with
        ⟨hTargetCursorAfterScrutinee, hRelAfterScrutinee,
          hPcAfterScrutinee⟩
      subst targetCursorAfterScrutinee
      let selectedSeg : CodeSegment layout.asm tailCode :=
        { pre := preTests
          post := post
          hAsm := by
            simpa [pre, post, preTests, tailCode, Stmt.compileFromCtxCore,
              endLabel, defaultLabel, compiledCases, compiledDefault,
              List.append_assoc] using segment.hAsm
          hFits := hTailFits }
      have hSelected :=
        selected_cases_result_ctx_in_programLayout_withGasOracle
          (program := program) (layout := layout) (ctx := ctx)
          (base := supply) (supply := LabelSupply.next supply) (idx := 0)
          (cases := cases) (defaultBody := defaultBody)
          (selected := selected) (casePrefix := ([] : Assembly.Program))
          (defaultLabel := defaultLabel) (endLabel := endLabel)
          (fuel := bodyFuel)
          (source := stateAfterScrutinee) (outcome := outcome)
          (target := targetAfterScrutinee) (tokens := tokens)
          (stack := stack) (value := value)
          (oracle := oracle) (cursor := cursorAfterScrutinee)
          (cursorFinal := cursorFinal)
          (switchCasesPreservesInProgramLayoutWithGasOracleAtFuel_of_upTo
            (fuel := bodyFuel) hBodyLt
            (by simpa [endLabel] using hCases))
          (switchDefaultPreservesInProgramLayoutWithGasOracleAtFuel_of_upTo
            (fuel := bodyFuel) hBodyLt
            (by simpa [endLabel, compiledCases] using hDefault))
          (by simpa [endLabel, compiledCases] using hCaseCalls)
          (by simpa [endLabel, defaultLabel, compiledCases, compiledDefault]
            using hDefaultCalls)
          selectedSeg hProgramWF hCtxProcs hResolve
          (by simpa [selectedSeg, CodeSegment.startPc] using hPcAfterScrutinee)
          hRelAfterScrutinee hPop hSelect hBodyEval
      exact
        ARunResultWithGasOracle.mono hSelected
          (by
            intro result targetCursorFinal hResult
            rcases hResult with ⟨hCursorFinal, hCompiled⟩
            exact
              ⟨hCursorFinal, by
                simpa [selectedSeg, tailCode, pre, post, preTests,
                  CodeSegment.fallthroughPc, Stmt.compileFromCtxCore, endLabel,
                  defaultLabel, compiledCases, compiledDefault,
                  List.append_assoc] using hCompiled⟩)

end ProcedureLayoutPreservation

namespace ForLoopPreservation

theorem false_case_withGasOracle {ctx : CompileContext}
    {pre suffix bodyCode postCode : Assembly.Program}
    {cond : Code}
    {loopLabel bodyLabel postLabel endLabel : Assembly.Label}
    {source stateAfterCond : RunState} {target : EVMState}
    {tokens : List Word} {oracle : GasOracle} {cursor cursorAfterCond : Nat}
    (hCondSafe : Code.RunnerSafeWithGasOracle cond)
    (hCondFrame : Code.FrameSafeWithGasOracle cond)
    (hLayout :
      ForLoop.Layout pre suffix cond bodyCode postCode loopLabel bodyLabel
        postLabel endLabel)
    (hPc : target.pc = Assembly.Program.pcAfter pre)
    (hRel : Frame.StateRel source target tokens)
    (hCond :
      Code.runConditionStateWithGasOracle cond oracle cursor source =
        .ok (stateAfterCond, false, cursorAfterCond)) :
    ARunResultWithGasOracle
      (pre ++
        ForLoop.coreCode cond bodyCode postCode loopLabel bodyLabel postLabel
          endLabel ++ suffix)
      oracle cursor target
      (fun result targetCursorFinal =>
        targetCursorFinal = cursorAfterCond ∧
          CompiledOutcomeRel
            (pre ++
              ForLoop.coreCode cond bodyCode postCode loopLabel bodyLabel
                postLabel endLabel ++ suffix)
            ctx
            (Assembly.Program.pcAfter
              (pre ++
                ForLoop.coreCode cond bodyCode postCode loopLabel bodyLabel
                  postLabel endLabel))
            (Outcome.regular stateAfterCond) result tokens) := by
  let loopPre := ForLoop.afterLoopLabel pre loopLabel
  let afterJumpi := ForLoop.afterCondJumpi pre cond loopLabel bodyLabel
  let bodyLabelPre :=
    ForLoop.bodyLabelPre pre cond loopLabel bodyLabel endLabel
  let endLabelPre :=
    ForLoop.endLabelPre pre cond bodyCode postCode loopLabel bodyLabel
      postLabel endLabel
  have hLoopLabelRun :=
    FrameStateRel.label_runResult_at_withGasOracle
      (label := loopLabel) (pre := pre)
      (post :=
        cond.toAssembly ++
          [ Assembly.Instr.jumpi bodyLabel
          , Assembly.Instr.jump endLabel
          , Assembly.Instr.label bodyLabel
          ] ++
          bodyCode ++ [Assembly.Instr.label postLabel] ++ postCode ++
          [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel] ++
          suffix)
      (oracle := oracle) (cursor := cursor)
      hLayout.fitLoopLabel hPc hRel
  refine
    ARunResultWithGasOracle.bind_running
      (program :=
        pre ++
          ForLoop.coreCode cond bodyCode postCode loopLabel bodyLabel
            postLabel endLabel ++ suffix)
      (middle := fun targetAtCond targetCursorAtCond =>
        targetCursorAtCond = cursor ∧
          Frame.StateRel source targetAtCond tokens ∧
            targetAtCond.pc = Assembly.Program.pcAfter loopPre)
      ?_ ?_
  · simpa [ForLoop.coreCode, ForLoop.afterLoopLabel, loopPre,
      List.append_assoc] using hLoopLabelRun
  · intro targetAtCond targetCursorAtCond hAtCond
    rcases hAtCond with ⟨hCursorAtCond, hRelAtCond, hPcAtCond⟩
    subst targetCursorAtCond
    have hBodyLabel :
        Assembly.Program.labelPc
            (loopPre ++ cond.toAssembly ++ [Assembly.Instr.jumpi bodyLabel] ++
              ([Assembly.Instr.jump endLabel, Assembly.Instr.label bodyLabel] ++
                bodyCode ++ [Assembly.Instr.label postLabel] ++ postCode ++
                [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel] ++
                suffix))
            bodyLabel =
          some (Assembly.Program.byteLength bodyLabelPre) := by
      simpa [ForLoop.coreCode, ForLoop.afterLoopLabel,
        ForLoop.afterCondJumpi, ForLoop.bodyLabelPre, loopPre, afterJumpi,
        bodyLabelPre, List.append_assoc] using hLayout.bodyLabelPc
    have hCondJump :=
      FrameStateRel.runCondition_jumpi_result_ctx_withGasOracle
        (cond := cond) (label := bodyLabel)
        (dest := Assembly.Program.byteLength bodyLabelPre)
        (pre := loopPre)
        (post :=
          [Assembly.Instr.jump endLabel, Assembly.Instr.label bodyLabel] ++
            bodyCode ++ [Assembly.Instr.label postLabel] ++ postCode ++
            [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel] ++
            suffix)
        (oracle := oracle) (cursor := cursor)
        hCondSafe hCondFrame hLayout.fitCond hPcAtCond hRelAtCond
        hBodyLabel hCond
    have hCondFalse :
        ARunResultWithGasOracle
          (pre ++
            ForLoop.coreCode cond bodyCode postCode loopLabel bodyLabel
              postLabel endLabel ++ suffix)
          oracle cursor targetAtCond
          (fun result targetCursorAfterCond =>
            match result with
            | .running targetAfterCond =>
                targetCursorAfterCond = cursorAfterCond ∧
                  Frame.StateRel stateAfterCond targetAfterCond tokens ∧
                    targetAfterCond.pc = Assembly.Program.pcAfter afterJumpi
            | .halted _ => False) := by
      exact ARunResultWithGasOracle.mono
        (by
          simpa [ForLoop.coreCode, ForLoop.afterLoopLabel,
            ForLoop.afterCondJumpi, loopPre, afterJumpi, List.append_assoc]
            using hCondJump)
        (by
          intro result targetCursorAfterCond hResult
          cases result with
          | halted halt =>
              cases hResult
          | running targetAfterCond =>
              simpa [afterJumpi, ForLoop.afterCondJumpi,
                ForLoop.afterLoopLabel, loopPre, List.append_assoc] using
                hResult)
    refine
      ARunResultWithGasOracle.bind_running
        (program :=
          pre ++
            ForLoop.coreCode cond bodyCode postCode loopLabel bodyLabel
              postLabel endLabel ++ suffix)
        (middle := fun targetAfterCond targetCursorAfterCond =>
          targetCursorAfterCond = cursorAfterCond ∧
            Frame.StateRel stateAfterCond targetAfterCond tokens ∧
              targetAfterCond.pc = Assembly.Program.pcAfter afterJumpi)
        hCondFalse ?_
    intro targetAfterCond targetCursorAfterCond hAfterCond
    rcases hAfterCond with
      ⟨hTargetCursorAfterCond, hRelAfterCond, hPcAfterCond⟩
    subst targetCursorAfterCond
    have hEndLabel :
        Assembly.Program.labelPc
            (afterJumpi ++ [Assembly.Instr.jump endLabel] ++
              ([Assembly.Instr.label bodyLabel] ++ bodyCode ++
                [Assembly.Instr.label postLabel] ++ postCode ++
                [Assembly.Instr.jump loopLabel]) ++
              [Assembly.Instr.label endLabel] ++ suffix)
            endLabel =
          some
            (Assembly.Program.byteLength
              (afterJumpi ++ [Assembly.Instr.jump endLabel] ++
                ([Assembly.Instr.label bodyLabel] ++ bodyCode ++
                  [Assembly.Instr.label postLabel] ++ postCode ++
                  [Assembly.Instr.jump loopLabel]))) := by
      simpa [ForLoop.coreCode, ForLoop.afterLoopLabel,
        ForLoop.afterCondJumpi, ForLoop.bodyLabelPre, ForLoop.bodyPre,
        ForLoop.postLabelPre, ForLoop.postPre, ForLoop.endLabelPre,
        loopPre, afterJumpi, bodyLabelPre, endLabelPre, List.append_assoc]
        using hLayout.endLabelPc
    have hJumpEnd :=
      FrameStateRel.jump_then_label_runResult_at_withGasOracle
        (label := endLabel) (pre := afterJumpi)
        (between :=
          [Assembly.Instr.label bodyLabel] ++ bodyCode ++
            [Assembly.Instr.label postLabel] ++ postCode ++
            [Assembly.Instr.jump loopLabel])
        (post := suffix) (oracle := oracle) (cursor := cursorAfterCond)
        hLayout.fitJumpEnd
        (by
          simpa [ForLoop.afterCondJumpi, ForLoop.bodyLabelPre,
            ForLoop.bodyPre, ForLoop.postLabelPre, ForLoop.postPre,
            ForLoop.endLabelPre, afterJumpi, endLabelPre, List.append_assoc]
            using hLayout.fitEndLabel)
        hPcAfterCond hRelAfterCond hEndLabel
    exact ARunResultWithGasOracle.mono
      (by
        simpa [ForLoop.coreCode, ForLoop.afterLoopLabel,
          ForLoop.afterCondJumpi, ForLoop.bodyLabelPre, ForLoop.bodyPre,
          ForLoop.postLabelPre, ForLoop.postPre, ForLoop.endLabelPre,
          loopPre, afterJumpi, bodyLabelPre, endLabelPre, List.append_assoc]
          using hJumpEnd)
      (by
        intro result targetCursorFinal hResult
        cases result with
        | halted halt =>
            cases hResult
        | running targetFinal =>
            rcases hResult with ⟨hCursorFinal, hRelFinal, hPcFinal⟩
            exact
              ⟨ hCursorFinal
              , by
                  simpa [ForLoop.coreCode, ForLoop.afterLoopLabel,
                    ForLoop.afterCondJumpi, ForLoop.bodyLabelPre,
                    ForLoop.bodyPre, ForLoop.postLabelPre, ForLoop.postPre,
                    ForLoop.endLabelPre, loopPre, afterJumpi, bodyLabelPre,
                    endLabelPre, CompiledOutcomeRel, Outcome.regular,
                    List.append_assoc] using And.intro hRelFinal hPcFinal
              ⟩)

theorem enter_body_withGasOracle
    {pre suffix bodyCode postCode : Assembly.Program}
    {cond : Code}
    {loopLabel bodyLabel postLabel endLabel : Assembly.Label}
    {source stateAfterCond : RunState} {target : EVMState}
    {tokens : List Word} {oracle : GasOracle} {cursor cursorAfterCond : Nat}
    (hCondSafe : Code.RunnerSafeWithGasOracle cond)
    (hCondFrame : Code.FrameSafeWithGasOracle cond)
    (hLayout :
      ForLoop.Layout pre suffix cond bodyCode postCode loopLabel bodyLabel
        postLabel endLabel)
    (hPc : target.pc = Assembly.Program.pcAfter pre)
    (hRel : Frame.StateRel source target tokens)
    (hCond :
      Code.runConditionStateWithGasOracle cond oracle cursor source =
        .ok (stateAfterCond, true, cursorAfterCond)) :
    ARunResultWithGasOracle
      (pre ++
        ForLoop.coreCode cond bodyCode postCode loopLabel bodyLabel postLabel
          endLabel ++ suffix)
      oracle cursor target
      (fun result targetCursorFinal =>
        match result with
        | .running targetAtBody =>
            targetCursorFinal = cursorAfterCond ∧
              Frame.StateRel stateAfterCond targetAtBody tokens ∧
                targetAtBody.pc =
                  Assembly.Program.pcAfter
                    (ForLoop.bodyPre pre cond loopLabel bodyLabel endLabel)
        | .halted _ => False) := by
  let loopPre := ForLoop.afterLoopLabel pre loopLabel
  let bodyLabelPre :=
    ForLoop.bodyLabelPre pre cond loopLabel bodyLabel endLabel
  let bodyPre := ForLoop.bodyPre pre cond loopLabel bodyLabel endLabel
  have hLoopLabelRun :=
    FrameStateRel.label_runResult_at_withGasOracle
      (label := loopLabel) (pre := pre)
      (post :=
        cond.toAssembly ++
          [ Assembly.Instr.jumpi bodyLabel
          , Assembly.Instr.jump endLabel
          , Assembly.Instr.label bodyLabel
          ] ++
          bodyCode ++ [Assembly.Instr.label postLabel] ++ postCode ++
          [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel] ++
          suffix)
      (oracle := oracle) (cursor := cursor)
      hLayout.fitLoopLabel hPc hRel
  refine
    ARunResultWithGasOracle.bind_running
      (program :=
        pre ++
          ForLoop.coreCode cond bodyCode postCode loopLabel bodyLabel
            postLabel endLabel ++ suffix)
      (middle := fun targetAtCond targetCursorAtCond =>
        targetCursorAtCond = cursor ∧
          Frame.StateRel source targetAtCond tokens ∧
            targetAtCond.pc = Assembly.Program.pcAfter loopPre)
      ?_ ?_
  · simpa [ForLoop.coreCode, ForLoop.afterLoopLabel, loopPre,
      List.append_assoc] using hLoopLabelRun
  · intro targetAtCond targetCursorAtCond hAtCond
    rcases hAtCond with ⟨hCursorAtCond, hRelAtCond, hPcAtCond⟩
    subst targetCursorAtCond
    have hBodyLabel :
        Assembly.Program.labelPc
            (loopPre ++ cond.toAssembly ++ [Assembly.Instr.jumpi bodyLabel] ++
              ([Assembly.Instr.jump endLabel, Assembly.Instr.label bodyLabel] ++
                bodyCode ++ [Assembly.Instr.label postLabel] ++ postCode ++
                [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel] ++
                suffix))
            bodyLabel =
          some (Assembly.Program.byteLength bodyLabelPre) := by
      simpa [ForLoop.coreCode, ForLoop.afterLoopLabel,
        ForLoop.afterCondJumpi, ForLoop.bodyLabelPre, loopPre,
        bodyLabelPre, List.append_assoc] using hLayout.bodyLabelPc
    have hCondJump :=
      FrameStateRel.runCondition_jumpi_result_ctx_withGasOracle
        (cond := cond) (label := bodyLabel)
        (dest := Assembly.Program.byteLength bodyLabelPre)
        (pre := loopPre)
        (post :=
          [Assembly.Instr.jump endLabel, Assembly.Instr.label bodyLabel] ++
            bodyCode ++ [Assembly.Instr.label postLabel] ++ postCode ++
            [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel] ++
            suffix)
        (oracle := oracle) (cursor := cursor)
        hCondSafe hCondFrame hLayout.fitCond hPcAtCond hRelAtCond
        hBodyLabel hCond
    have hCondTrue :
        ARunResultWithGasOracle
          (pre ++
            ForLoop.coreCode cond bodyCode postCode loopLabel bodyLabel
              postLabel endLabel ++ suffix)
          oracle cursor targetAtCond
          (fun result targetCursorAfterCond =>
            match result with
            | .running targetAfterCond =>
                targetCursorAfterCond = cursorAfterCond ∧
                  Frame.StateRel stateAfterCond targetAfterCond tokens ∧
                    targetAfterCond.pc = Assembly.Program.pcAfter bodyLabelPre
            | .halted _ => False) := by
      exact ARunResultWithGasOracle.mono
        (by
          simpa [ForLoop.coreCode, ForLoop.afterLoopLabel,
            ForLoop.afterCondJumpi, loopPre, bodyLabelPre, List.append_assoc]
            using hCondJump)
        (by
          intro result targetCursorAfterCond hResult
          cases result with
          | halted halt =>
              cases hResult
          | running targetAfterCond =>
              simpa [bodyLabelPre] using hResult)
    refine
      ARunResultWithGasOracle.bind_running
        (program :=
          pre ++
            ForLoop.coreCode cond bodyCode postCode loopLabel bodyLabel
              postLabel endLabel ++ suffix)
        (middle := fun targetAfterCond targetCursorAfterCond =>
          targetCursorAfterCond = cursorAfterCond ∧
            Frame.StateRel stateAfterCond targetAfterCond tokens ∧
              targetAfterCond.pc = Assembly.Program.pcAfter bodyLabelPre)
        hCondTrue ?_
    intro targetAfterCond targetCursorAfterCond hAfterCond
    rcases hAfterCond with
      ⟨hTargetCursorAfterCond, hRelAfterCond, hPcAfterCond⟩
    subst targetCursorAfterCond
    have hBodyLabelRun :=
      FrameStateRel.label_runResult_at_withGasOracle
        (label := bodyLabel) (pre := bodyLabelPre)
        (post :=
          bodyCode ++ [Assembly.Instr.label postLabel] ++ postCode ++
            [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel] ++
            suffix)
        (oracle := oracle) (cursor := cursorAfterCond)
        hLayout.fitBodyLabel hPcAfterCond hRelAfterCond
    exact ARunResultWithGasOracle.mono
      (by
        simpa [ForLoop.coreCode, ForLoop.afterLoopLabel,
          ForLoop.afterCondJumpi, ForLoop.bodyLabelPre, ForLoop.bodyPre,
          loopPre, bodyLabelPre, bodyPre, List.append_assoc] using
          hBodyLabelRun)
      (by
        intro result targetCursorFinal hResult
        cases result with
        | halted halt =>
            cases hResult
        | running targetAtBody =>
            simpa [ForLoop.afterLoopLabel, ForLoop.afterCondJumpi,
              ForLoop.bodyLabelPre, ForLoop.bodyPre, loopPre, bodyLabelPre,
              bodyPre, List.append_assoc] using hResult)

theorem body_brk_case_withGasOracle {program : Program} {ctx : CompileContext}
    {pre suffix postCode : Assembly.Program}
    {cond : Code} {body : Block} {bodySupply : LabelSupply}
    {loopLabel bodyLabel postLabel endLabel : Assembly.Label}
    {fuel : Nat}
    {source stateAfterCond bodyState : RunState} {target : EVMState}
    {tokens : List Word} {oracle : GasOracle}
    {cursor cursorAfterCond cursorFinal : Nat}
    (hCondSafe : Code.RunnerSafeWithGasOracle cond)
    (hCondFrame : Code.FrameSafeWithGasOracle cond)
    (hBody :
      BlockPreservesWithGasOracle program
        { ctx with
          breakLabel? := some endLabel
          continueLabel? := some postLabel }
        bodySupply body)
    (hLayout :
      ForLoop.Layout pre suffix cond
        (Block.compileFromCtx body
          { ctx with
            breakLabel? := some endLabel
            continueLabel? := some postLabel }
          bodySupply).code
        postCode loopLabel bodyLabel postLabel endLabel)
    (hResolve :
      ContextLabelsResolve
        (pre ++
          ForLoop.coreCode cond
            (Block.compileFromCtx body
              { ctx with
                breakLabel? := some endLabel
                continueLabel? := some postLabel }
              bodySupply).code
            postCode loopLabel bodyLabel postLabel endLabel ++ suffix)
        ctx)
    (hExact :
      ExactLabels
        (pre ++
          ForLoop.coreCode cond
            (Block.compileFromCtx body
              { ctx with
                breakLabel? := some endLabel
                continueLabel? := some postLabel }
              bodySupply).code
            postCode loopLabel bodyLabel postLabel endLabel ++ suffix))
    (hPc : target.pc = Assembly.Program.pcAfter pre)
    (hRel : Frame.StateRel source target tokens)
    (hCond :
      Code.runConditionStateWithGasOracle cond oracle cursor source =
        .ok (stateAfterCond, true, cursorAfterCond))
    (hBodyEval :
      Block.EvalWithGasOracle program oracle fuel body cursorAfterCond
        stateAfterCond (Outcome.brk bodyState) cursorFinal) :
    ARunResultWithGasOracle
      (pre ++
        ForLoop.coreCode cond
          (Block.compileFromCtx body
            { ctx with
              breakLabel? := some endLabel
              continueLabel? := some postLabel }
            bodySupply).code
          postCode loopLabel bodyLabel postLabel endLabel ++ suffix)
      oracle cursor target
      (fun result targetCursorFinal =>
        targetCursorFinal = cursorFinal ∧
          CompiledOutcomeRel
            (pre ++
              ForLoop.coreCode cond
                (Block.compileFromCtx body
                  { ctx with
                    breakLabel? := some endLabel
                    continueLabel? := some postLabel }
                  bodySupply).code
                postCode loopLabel bodyLabel postLabel endLabel ++ suffix)
            ctx
            (Assembly.Program.pcAfter
              (pre ++
                ForLoop.coreCode cond
                  (Block.compileFromCtx body
                    { ctx with
                      breakLabel? := some endLabel
                      continueLabel? := some postLabel }
                    bodySupply).code
                  postCode loopLabel bodyLabel postLabel endLabel))
            (Outcome.regular bodyState) result tokens) := by
  let bodyCtx : CompileContext :=
    { ctx with
      breakLabel? := some endLabel
      continueLabel? := some postLabel }
  let bodyCode := (Block.compileFromCtx body bodyCtx bodySupply).code
  let bodyPre := ForLoop.bodyPre pre cond loopLabel bodyLabel endLabel
  let endLabelPre :=
    ForLoop.endLabelPre pre cond bodyCode postCode loopLabel bodyLabel
      postLabel endLabel
  have hEnter :=
    enter_body_withGasOracle
      (pre := pre) (suffix := suffix) (bodyCode := bodyCode)
      (postCode := postCode) (cond := cond) (loopLabel := loopLabel)
      (bodyLabel := bodyLabel) (postLabel := postLabel)
      (endLabel := endLabel) (source := source)
      (stateAfterCond := stateAfterCond) (target := target)
      (tokens := tokens) (oracle := oracle) (cursor := cursor)
      (cursorAfterCond := cursorAfterCond)
      hCondSafe hCondFrame
      (by simpa [bodyCtx, bodyCode] using hLayout)
      hPc hRel hCond
  refine
    ARunResultWithGasOracle.bind_running
      (program :=
        pre ++
          ForLoop.coreCode cond bodyCode postCode loopLabel bodyLabel
            postLabel endLabel ++ suffix)
      (middle := fun targetAtBody targetCursorAtBody =>
        targetCursorAtBody = cursorAfterCond ∧
          Frame.StateRel stateAfterCond targetAtBody tokens ∧
            targetAtBody.pc = Assembly.Program.pcAfter bodyPre)
      ?_ ?_
  · simpa [bodyCtx, bodyCode, bodyPre] using hEnter
  · intro targetAtBody targetCursorAtBody hAtBody
    rcases hAtBody with ⟨hCursorAtBody, hRelAtBody, hPcAtBody⟩
    subst targetCursorAtBody
    have hBodyCtxResolve :
        ContextLabelsResolve
          (pre ++
            ForLoop.coreCode cond bodyCode postCode loopLabel bodyLabel
              postLabel endLabel ++ suffix)
          bodyCtx :=
      ContextLabelsResolve.with_break_continue
        (ctx := ctx)
        (breakLabel := endLabel) (continueLabel := postLabel)
        (by simpa [bodyCtx, bodyCode] using hResolve)
        ⟨Assembly.Program.byteLength endLabelPre, by
          simpa [bodyCtx, bodyCode, endLabelPre] using hLayout.endLabelPc⟩
        ⟨Assembly.Program.byteLength
            (ForLoop.postLabelPre pre cond bodyCode loopLabel bodyLabel
              endLabel),
          by simpa [bodyCtx, bodyCode] using hLayout.postLabelPc⟩
    have hBodyResolve :
        ContextLabelsResolve
          (bodyPre ++ bodyCode ++
            ([Assembly.Instr.label postLabel] ++ postCode ++
              [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel] ++
              suffix))
          bodyCtx := by
      simpa [bodyCtx, bodyCode, ForLoop.coreCode, ForLoop.afterLoopLabel,
        ForLoop.afterCondJumpi, ForLoop.bodyLabelPre, ForLoop.bodyPre,
        bodyPre, List.append_assoc] using hBodyCtxResolve
    have hBodyExact :
        ExactLabels
          (bodyPre ++ bodyCode ++
            ([Assembly.Instr.label postLabel] ++ postCode ++
              [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel] ++
              suffix)) := by
      simpa [bodyCtx, bodyCode, ForLoop.coreCode, ForLoop.afterLoopLabel,
        ForLoop.afterCondJumpi, ForLoop.bodyLabelPre, ForLoop.bodyPre,
        bodyPre, List.append_assoc] using hExact
    have hBodyRun :=
      hBody (pre := bodyPre)
        (post :=
          [Assembly.Instr.label postLabel] ++ postCode ++
            [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel] ++
            suffix)
        (fuel := fuel) (source := stateAfterCond)
        (outcome := Outcome.brk bodyState) (target := targetAtBody)
        (tokens := tokens) (oracle := oracle) (cursor := cursorAfterCond)
        (cursorFinal := cursorFinal)
        hLayout.fitBody hBodyResolve hBodyExact hPcAtBody hRelAtBody hBodyEval
    have hBodyBrk :
        ARunResultWithGasOracle
          (bodyPre ++ bodyCode ++
            ([Assembly.Instr.label postLabel] ++ postCode ++
              [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel] ++
              suffix))
          oracle cursorAfterCond targetAtBody
          (fun result targetCursorAtEnd =>
            match result with
            | .running targetAtEnd =>
                targetCursorAtEnd = cursorFinal ∧
                  Frame.StateRel bodyState targetAtEnd tokens ∧
                    targetAtEnd.pc = Assembly.Program.pcAfter endLabelPre
            | .halted _ => False) := by
      exact ARunResultWithGasOracle.mono hBodyRun (by
        intro result targetCursorAtEnd hResult
        cases result with
        | halted halt =>
            cases hResult.2
        | running targetAtEnd =>
            rcases hResult with ⟨hCursorAtEnd, hCompiled⟩
            rcases hCompiled with
              ⟨label, dest, hBreak, hLabel, hRelEnd, hPcEnd⟩
            simp at hBreak
            cases hBreak
            have hDest :
                dest = Assembly.Program.byteLength endLabelPre := by
              have hLabelFull :
                  Assembly.Program.labelPc
                      (pre ++
                        ForLoop.coreCode cond bodyCode postCode loopLabel
                          bodyLabel postLabel endLabel ++ suffix) endLabel =
                    some dest := by
                simpa [bodyCtx, bodyCode, ForLoop.coreCode,
                  ForLoop.afterLoopLabel, ForLoop.afterCondJumpi,
                  ForLoop.bodyLabelPre, ForLoop.bodyPre, bodyPre,
                  List.append_assoc] using hLabel
              have hExactEnd :
                  Assembly.Program.labelPc
                      (pre ++
                        ForLoop.coreCode cond bodyCode postCode loopLabel
                          bodyLabel postLabel endLabel ++ suffix) endLabel =
                    some (Assembly.Program.byteLength endLabelPre) := by
                simpa [bodyCtx, bodyCode, endLabelPre] using
                  hLayout.endLabelPc
              rw [hLabelFull] at hExactEnd
              cases hExactEnd
              rfl
            refine ⟨hCursorAtEnd, hRelEnd, ?_⟩
            simpa [endLabelPre, hDest] using hPcEnd)
    refine
      ARunResultWithGasOracle.bind_running
        (program :=
          pre ++
            ForLoop.coreCode cond bodyCode postCode loopLabel bodyLabel
              postLabel endLabel ++ suffix)
        (middle := fun targetAtEnd targetCursorAtEnd =>
          targetCursorAtEnd = cursorFinal ∧
            Frame.StateRel bodyState targetAtEnd tokens ∧
              targetAtEnd.pc = Assembly.Program.pcAfter endLabelPre)
        ?_ ?_
    · simpa [bodyCtx, bodyCode, ForLoop.coreCode, ForLoop.afterLoopLabel,
        ForLoop.afterCondJumpi, ForLoop.bodyLabelPre, ForLoop.bodyPre,
        bodyPre, List.append_assoc] using hBodyBrk
    · intro targetAtEnd targetCursorAtEnd hAtEnd
      rcases hAtEnd with ⟨hCursorAtEnd, hRelAtEnd, hPcAtEnd⟩
      subst targetCursorAtEnd
      have hEndRun :=
        FrameStateRel.label_runResult_at_withGasOracle
          (label := endLabel) (pre := endLabelPre) (post := suffix)
          (oracle := oracle) (cursor := cursorFinal)
          hLayout.fitEndLabel hPcAtEnd hRelAtEnd
      exact ARunResultWithGasOracle.mono
        (by
          simpa [bodyCtx, bodyCode, ForLoop.coreCode,
            ForLoop.afterLoopLabel, ForLoop.afterCondJumpi,
            ForLoop.bodyLabelPre, ForLoop.bodyPre, ForLoop.postLabelPre,
            ForLoop.postPre, ForLoop.endLabelPre, bodyPre, endLabelPre,
            List.append_assoc] using hEndRun)
        (by
          intro result targetCursorFinal hResult
          cases result with
          | halted halt =>
              cases hResult
          | running targetFinal =>
              rcases hResult with ⟨hCursorFinal, hRelFinal, hPcFinal⟩
              exact
                ⟨ hCursorFinal
                , by
                    simpa [bodyCtx, bodyCode, ForLoop.coreCode,
                      ForLoop.afterLoopLabel, ForLoop.afterCondJumpi,
                      ForLoop.bodyLabelPre, ForLoop.bodyPre,
                      ForLoop.postLabelPre, ForLoop.postPre,
                      ForLoop.endLabelPre, bodyPre, endLabelPre,
                      CompiledOutcomeRel, Outcome.regular, List.append_assoc]
                      using And.intro hRelFinal hPcFinal
                ⟩)

theorem body_leave_case_withGasOracle {program : Program}
    {ctx : CompileContext}
    {pre suffix postCode : Assembly.Program}
    {cond : Code} {body : Block} {bodySupply : LabelSupply}
    {loopLabel bodyLabel postLabel endLabel : Assembly.Label}
    {fuel : Nat}
    {source stateAfterCond bodyState : RunState} {target : EVMState}
    {tokens : List Word} {oracle : GasOracle}
    {cursor cursorAfterCond cursorFinal : Nat}
    (hCondSafe : Code.RunnerSafeWithGasOracle cond)
    (hCondFrame : Code.FrameSafeWithGasOracle cond)
    (hBody :
      BlockPreservesWithGasOracle program
        { ctx with
          breakLabel? := some endLabel
          continueLabel? := some postLabel }
        bodySupply body)
    (hLayout :
      ForLoop.Layout pre suffix cond
        (Block.compileFromCtx body
          { ctx with
            breakLabel? := some endLabel
            continueLabel? := some postLabel }
          bodySupply).code
        postCode loopLabel bodyLabel postLabel endLabel)
    (hResolve :
      ContextLabelsResolve
        (pre ++
          ForLoop.coreCode cond
            (Block.compileFromCtx body
              { ctx with
                breakLabel? := some endLabel
                continueLabel? := some postLabel }
              bodySupply).code
            postCode loopLabel bodyLabel postLabel endLabel ++ suffix)
        ctx)
    (hExact :
      ExactLabels
        (pre ++
          ForLoop.coreCode cond
            (Block.compileFromCtx body
              { ctx with
                breakLabel? := some endLabel
                continueLabel? := some postLabel }
              bodySupply).code
            postCode loopLabel bodyLabel postLabel endLabel ++ suffix))
    (hPc : target.pc = Assembly.Program.pcAfter pre)
    (hRel : Frame.StateRel source target tokens)
    (hCond :
      Code.runConditionStateWithGasOracle cond oracle cursor source =
        .ok (stateAfterCond, true, cursorAfterCond))
    (hBodyEval :
      Block.EvalWithGasOracle program oracle fuel body cursorAfterCond
        stateAfterCond (Outcome.leave bodyState) cursorFinal) :
    ARunResultWithGasOracle
      (pre ++
        ForLoop.coreCode cond
          (Block.compileFromCtx body
            { ctx with
              breakLabel? := some endLabel
              continueLabel? := some postLabel }
            bodySupply).code
          postCode loopLabel bodyLabel postLabel endLabel ++ suffix)
      oracle cursor target
      (fun result targetCursorFinal =>
        targetCursorFinal = cursorFinal ∧
          CompiledOutcomeRel
            (pre ++
              ForLoop.coreCode cond
                (Block.compileFromCtx body
                  { ctx with
                    breakLabel? := some endLabel
                    continueLabel? := some postLabel }
                  bodySupply).code
                postCode loopLabel bodyLabel postLabel endLabel ++ suffix)
            ctx
            (Assembly.Program.pcAfter
              (pre ++
                ForLoop.coreCode cond
                  (Block.compileFromCtx body
                    { ctx with
                      breakLabel? := some endLabel
                      continueLabel? := some postLabel }
                    bodySupply).code
                  postCode loopLabel bodyLabel postLabel endLabel))
            (Outcome.leave bodyState) result tokens) := by
  let bodyCtx : CompileContext :=
    { ctx with
      breakLabel? := some endLabel
      continueLabel? := some postLabel }
  let bodyCode := (Block.compileFromCtx body bodyCtx bodySupply).code
  let bodyPre := ForLoop.bodyPre pre cond loopLabel bodyLabel endLabel
  let endLabelPre :=
    ForLoop.endLabelPre pre cond bodyCode postCode loopLabel bodyLabel
      postLabel endLabel
  have hEnter :=
    enter_body_withGasOracle
      (pre := pre) (suffix := suffix) (bodyCode := bodyCode)
      (postCode := postCode) (cond := cond) (loopLabel := loopLabel)
      (bodyLabel := bodyLabel) (postLabel := postLabel)
      (endLabel := endLabel) (source := source)
      (stateAfterCond := stateAfterCond) (target := target)
      (tokens := tokens) (oracle := oracle) (cursor := cursor)
      (cursorAfterCond := cursorAfterCond)
      hCondSafe hCondFrame
      (by simpa [bodyCtx, bodyCode] using hLayout)
      hPc hRel hCond
  refine
    ARunResultWithGasOracle.bind_running
      (program :=
        pre ++
          ForLoop.coreCode cond bodyCode postCode loopLabel bodyLabel
            postLabel endLabel ++ suffix)
      (middle := fun targetAtBody targetCursorAtBody =>
        targetCursorAtBody = cursorAfterCond ∧
          Frame.StateRel stateAfterCond targetAtBody tokens ∧
            targetAtBody.pc = Assembly.Program.pcAfter bodyPre)
      ?_ ?_
  · simpa [bodyCtx, bodyCode, bodyPre] using hEnter
  · intro targetAtBody targetCursorAtBody hAtBody
    rcases hAtBody with ⟨hCursorAtBody, hRelAtBody, hPcAtBody⟩
    subst targetCursorAtBody
    have hBodyCtxResolve :
        ContextLabelsResolve
          (pre ++
            ForLoop.coreCode cond bodyCode postCode loopLabel bodyLabel
              postLabel endLabel ++ suffix)
          bodyCtx :=
      ContextLabelsResolve.with_break_continue
        (ctx := ctx)
        (breakLabel := endLabel) (continueLabel := postLabel)
        (by simpa [bodyCtx, bodyCode] using hResolve)
        ⟨Assembly.Program.byteLength endLabelPre, by
          simpa [bodyCtx, bodyCode, endLabelPre] using hLayout.endLabelPc⟩
        ⟨Assembly.Program.byteLength
            (ForLoop.postLabelPre pre cond bodyCode loopLabel bodyLabel
              endLabel),
          by simpa [bodyCtx, bodyCode] using hLayout.postLabelPc⟩
    have hBodyResolve :
        ContextLabelsResolve
          (bodyPre ++ bodyCode ++
            ([Assembly.Instr.label postLabel] ++ postCode ++
              [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel] ++
              suffix))
          bodyCtx := by
      simpa [bodyCtx, bodyCode, ForLoop.coreCode, ForLoop.afterLoopLabel,
        ForLoop.afterCondJumpi, ForLoop.bodyLabelPre, ForLoop.bodyPre,
        bodyPre, List.append_assoc] using hBodyCtxResolve
    have hBodyExact :
        ExactLabels
          (bodyPre ++ bodyCode ++
            ([Assembly.Instr.label postLabel] ++ postCode ++
              [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel] ++
              suffix)) := by
      simpa [bodyCtx, bodyCode, ForLoop.coreCode, ForLoop.afterLoopLabel,
        ForLoop.afterCondJumpi, ForLoop.bodyLabelPre, ForLoop.bodyPre,
        bodyPre, List.append_assoc] using hExact
    have hBodyRun :=
      hBody (pre := bodyPre)
        (post :=
          [Assembly.Instr.label postLabel] ++ postCode ++
            [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel] ++
            suffix)
        (fuel := fuel) (source := stateAfterCond)
        (outcome := Outcome.leave bodyState) (target := targetAtBody)
        (tokens := tokens) (oracle := oracle) (cursor := cursorAfterCond)
        (cursorFinal := cursorFinal)
        hLayout.fitBody hBodyResolve hBodyExact hPcAtBody hRelAtBody hBodyEval
    exact ARunResultWithGasOracle.mono
      (by
        simpa [bodyCtx, bodyCode, ForLoop.coreCode,
          ForLoop.afterLoopLabel, ForLoop.afterCondJumpi,
          ForLoop.bodyLabelPre, ForLoop.bodyPre, bodyPre, List.append_assoc]
          using hBodyRun)
      (by
        intro result targetCursorFinal hResult
        rcases hResult with ⟨hCursorFinal, hCompiled⟩
        cases result with
        | running target' =>
            exact
              ⟨ hCursorFinal
              , by
                  simpa [bodyCtx, bodyCode, ForLoop.coreCode,
                    ForLoop.afterLoopLabel, ForLoop.afterCondJumpi,
                    ForLoop.bodyLabelPre, ForLoop.bodyPre, bodyPre,
                    CompiledOutcomeRel, Outcome.leave, List.append_assoc] using
                    hCompiled
              ⟩
        | halted halt =>
            cases hCompiled)

theorem body_halt_case_withGasOracle {program : Program}
    {ctx : CompileContext}
    {pre suffix postCode : Assembly.Program}
    {cond : Code} {body : Block} {bodySupply : LabelSupply}
    {loopLabel bodyLabel postLabel endLabel : Assembly.Label}
    {fuel : Nat}
    {source stateAfterCond bodyState : RunState} {target : EVMState}
    {tokens : List Word} {kind : Assembly.HaltKind} {oracle : GasOracle}
    {cursor cursorAfterCond cursorFinal : Nat}
    (hCondSafe : Code.RunnerSafeWithGasOracle cond)
    (hCondFrame : Code.FrameSafeWithGasOracle cond)
    (hBody :
      BlockPreservesWithGasOracle program
        { ctx with
          breakLabel? := some endLabel
          continueLabel? := some postLabel }
        bodySupply body)
    (hLayout :
      ForLoop.Layout pre suffix cond
        (Block.compileFromCtx body
          { ctx with
            breakLabel? := some endLabel
            continueLabel? := some postLabel }
          bodySupply).code
        postCode loopLabel bodyLabel postLabel endLabel)
    (hResolve :
      ContextLabelsResolve
        (pre ++
          ForLoop.coreCode cond
            (Block.compileFromCtx body
              { ctx with
                breakLabel? := some endLabel
                continueLabel? := some postLabel }
              bodySupply).code
            postCode loopLabel bodyLabel postLabel endLabel ++ suffix)
        ctx)
    (hExact :
      ExactLabels
        (pre ++
          ForLoop.coreCode cond
            (Block.compileFromCtx body
              { ctx with
                breakLabel? := some endLabel
                continueLabel? := some postLabel }
              bodySupply).code
            postCode loopLabel bodyLabel postLabel endLabel ++ suffix))
    (hPc : target.pc = Assembly.Program.pcAfter pre)
    (hRel : Frame.StateRel source target tokens)
    (hCond :
      Code.runConditionStateWithGasOracle cond oracle cursor source =
        .ok (stateAfterCond, true, cursorAfterCond))
    (hBodyEval :
      Block.EvalWithGasOracle program oracle fuel body cursorAfterCond
        stateAfterCond (Outcome.halt kind bodyState) cursorFinal) :
    ARunResultWithGasOracle
      (pre ++
        ForLoop.coreCode cond
          (Block.compileFromCtx body
            { ctx with
              breakLabel? := some endLabel
              continueLabel? := some postLabel }
            bodySupply).code
          postCode loopLabel bodyLabel postLabel endLabel ++ suffix)
      oracle cursor target
      (fun result targetCursorFinal =>
        targetCursorFinal = cursorFinal ∧
          CompiledOutcomeRel
            (pre ++
              ForLoop.coreCode cond
                (Block.compileFromCtx body
                  { ctx with
                    breakLabel? := some endLabel
                    continueLabel? := some postLabel }
                  bodySupply).code
                postCode loopLabel bodyLabel postLabel endLabel ++ suffix)
            ctx
            (Assembly.Program.pcAfter
              (pre ++
                ForLoop.coreCode cond
                  (Block.compileFromCtx body
                    { ctx with
                      breakLabel? := some endLabel
                      continueLabel? := some postLabel }
                    bodySupply).code
                  postCode loopLabel bodyLabel postLabel endLabel))
            (Outcome.halt kind bodyState) result tokens) := by
  let bodyCtx : CompileContext :=
    { ctx with
      breakLabel? := some endLabel
      continueLabel? := some postLabel }
  let bodyCode := (Block.compileFromCtx body bodyCtx bodySupply).code
  let bodyPre := ForLoop.bodyPre pre cond loopLabel bodyLabel endLabel
  let endLabelPre :=
    ForLoop.endLabelPre pre cond bodyCode postCode loopLabel bodyLabel
      postLabel endLabel
  have hEnter :=
    enter_body_withGasOracle
      (pre := pre) (suffix := suffix) (bodyCode := bodyCode)
      (postCode := postCode) (cond := cond) (loopLabel := loopLabel)
      (bodyLabel := bodyLabel) (postLabel := postLabel)
      (endLabel := endLabel) (source := source)
      (stateAfterCond := stateAfterCond) (target := target)
      (tokens := tokens) (oracle := oracle) (cursor := cursor)
      (cursorAfterCond := cursorAfterCond)
      hCondSafe hCondFrame
      (by simpa [bodyCtx, bodyCode] using hLayout)
      hPc hRel hCond
  refine
    ARunResultWithGasOracle.bind_running
      (program :=
        pre ++
          ForLoop.coreCode cond bodyCode postCode loopLabel bodyLabel
            postLabel endLabel ++ suffix)
      (middle := fun targetAtBody targetCursorAtBody =>
        targetCursorAtBody = cursorAfterCond ∧
          Frame.StateRel stateAfterCond targetAtBody tokens ∧
            targetAtBody.pc = Assembly.Program.pcAfter bodyPre)
      ?_ ?_
  · simpa [bodyCtx, bodyCode, bodyPre] using hEnter
  · intro targetAtBody targetCursorAtBody hAtBody
    rcases hAtBody with ⟨hCursorAtBody, hRelAtBody, hPcAtBody⟩
    subst targetCursorAtBody
    have hBodyCtxResolve :
        ContextLabelsResolve
          (pre ++
            ForLoop.coreCode cond bodyCode postCode loopLabel bodyLabel
              postLabel endLabel ++ suffix)
          bodyCtx :=
      ContextLabelsResolve.with_break_continue
        (ctx := ctx)
        (breakLabel := endLabel) (continueLabel := postLabel)
        (by simpa [bodyCtx, bodyCode] using hResolve)
        ⟨Assembly.Program.byteLength endLabelPre, by
          simpa [bodyCtx, bodyCode, endLabelPre] using hLayout.endLabelPc⟩
        ⟨Assembly.Program.byteLength
            (ForLoop.postLabelPre pre cond bodyCode loopLabel bodyLabel
              endLabel),
          by simpa [bodyCtx, bodyCode] using hLayout.postLabelPc⟩
    have hBodyResolve :
        ContextLabelsResolve
          (bodyPre ++ bodyCode ++
            ([Assembly.Instr.label postLabel] ++ postCode ++
              [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel] ++
              suffix))
          bodyCtx := by
      simpa [bodyCtx, bodyCode, ForLoop.coreCode, ForLoop.afterLoopLabel,
        ForLoop.afterCondJumpi, ForLoop.bodyLabelPre, ForLoop.bodyPre,
        bodyPre, List.append_assoc] using hBodyCtxResolve
    have hBodyExact :
        ExactLabels
          (bodyPre ++ bodyCode ++
            ([Assembly.Instr.label postLabel] ++ postCode ++
              [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel] ++
              suffix)) := by
      simpa [bodyCtx, bodyCode, ForLoop.coreCode, ForLoop.afterLoopLabel,
        ForLoop.afterCondJumpi, ForLoop.bodyLabelPre, ForLoop.bodyPre,
        bodyPre, List.append_assoc] using hExact
    have hBodyRun :=
      hBody (pre := bodyPre)
        (post :=
          [Assembly.Instr.label postLabel] ++ postCode ++
            [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel] ++
            suffix)
        (fuel := fuel) (source := stateAfterCond)
        (outcome := Outcome.halt kind bodyState) (target := targetAtBody)
        (tokens := tokens) (oracle := oracle) (cursor := cursorAfterCond)
        (cursorFinal := cursorFinal)
        hLayout.fitBody hBodyResolve hBodyExact hPcAtBody hRelAtBody hBodyEval
    exact ARunResultWithGasOracle.mono
      (by
        simpa [bodyCtx, bodyCode, ForLoop.coreCode,
          ForLoop.afterLoopLabel, ForLoop.afterCondJumpi,
          ForLoop.bodyLabelPre, ForLoop.bodyPre, bodyPre, List.append_assoc]
          using hBodyRun)
      (by
        intro result targetCursorFinal hResult
        rcases hResult with ⟨hCursorFinal, hCompiled⟩
        cases result with
        | running target' =>
            cases hCompiled
        | halted halt =>
            exact
              ⟨ hCursorFinal
              , by
                  simpa [bodyCtx, bodyCode, ForLoop.coreCode,
                    ForLoop.afterLoopLabel, ForLoop.afterCondJumpi,
                    ForLoop.bodyLabelPre, ForLoop.bodyPre, bodyPre,
                    CompiledOutcomeRel, Outcome.halt, List.append_assoc] using
                    hCompiled
              ⟩)

theorem body_regular_enter_post_withGasOracle {program : Program}
    {ctx : CompileContext}
    {pre suffix postCode : Assembly.Program}
    {cond : Code} {body : Block} {bodySupply : LabelSupply}
    {loopLabel bodyLabel postLabel endLabel : Assembly.Label}
    {fuel : Nat}
    {source stateAfterCond bodyState : RunState} {target : EVMState}
    {tokens : List Word} {oracle : GasOracle}
    {cursor cursorAfterCond cursorAfterBody : Nat}
    (hCondSafe : Code.RunnerSafeWithGasOracle cond)
    (hCondFrame : Code.FrameSafeWithGasOracle cond)
    (hBody :
      BlockPreservesWithGasOracle program
        { ctx with
          breakLabel? := some endLabel
          continueLabel? := some postLabel }
        bodySupply body)
    (hLayout :
      ForLoop.Layout pre suffix cond
        (Block.compileFromCtx body
          { ctx with
            breakLabel? := some endLabel
            continueLabel? := some postLabel }
          bodySupply).code
        postCode loopLabel bodyLabel postLabel endLabel)
    (hResolve :
      ContextLabelsResolve
        (pre ++
          ForLoop.coreCode cond
            (Block.compileFromCtx body
              { ctx with
                breakLabel? := some endLabel
                continueLabel? := some postLabel }
              bodySupply).code
            postCode loopLabel bodyLabel postLabel endLabel ++ suffix)
        ctx)
    (hExact :
      ExactLabels
        (pre ++
          ForLoop.coreCode cond
            (Block.compileFromCtx body
              { ctx with
                breakLabel? := some endLabel
                continueLabel? := some postLabel }
              bodySupply).code
            postCode loopLabel bodyLabel postLabel endLabel ++ suffix))
    (hPc : target.pc = Assembly.Program.pcAfter pre)
    (hRel : Frame.StateRel source target tokens)
    (hCond :
      Code.runConditionStateWithGasOracle cond oracle cursor source =
        .ok (stateAfterCond, true, cursorAfterCond))
    (hBodyEval :
      Block.EvalWithGasOracle program oracle fuel body cursorAfterCond
        stateAfterCond (Outcome.regular bodyState) cursorAfterBody) :
    ARunResultWithGasOracle
      (pre ++
        ForLoop.coreCode cond
          (Block.compileFromCtx body
            { ctx with
              breakLabel? := some endLabel
              continueLabel? := some postLabel }
            bodySupply).code
          postCode loopLabel bodyLabel postLabel endLabel ++ suffix)
      oracle cursor target
      (fun result targetCursorAtPost =>
        match result with
        | .running targetAtPost =>
            targetCursorAtPost = cursorAfterBody ∧
              Frame.StateRel bodyState targetAtPost tokens ∧
                targetAtPost.pc =
                  Assembly.Program.pcAfter
                    (ForLoop.postPre pre cond
                      (Block.compileFromCtx body
                        { ctx with
                          breakLabel? := some endLabel
                          continueLabel? := some postLabel }
                        bodySupply).code
                      loopLabel bodyLabel postLabel endLabel)
        | .halted _ => False) := by
  let bodyCtx : CompileContext :=
    { ctx with
      breakLabel? := some endLabel
      continueLabel? := some postLabel }
  let bodyCode := (Block.compileFromCtx body bodyCtx bodySupply).code
  let bodyPre := ForLoop.bodyPre pre cond loopLabel bodyLabel endLabel
  let postLabelPre :=
    ForLoop.postLabelPre pre cond bodyCode loopLabel bodyLabel endLabel
  let postPre :=
    ForLoop.postPre pre cond bodyCode loopLabel bodyLabel postLabel endLabel
  let endLabelPre :=
    ForLoop.endLabelPre pre cond bodyCode postCode loopLabel bodyLabel
      postLabel endLabel
  have hEnter :=
    enter_body_withGasOracle
      (pre := pre) (suffix := suffix) (bodyCode := bodyCode)
      (postCode := postCode) (cond := cond) (loopLabel := loopLabel)
      (bodyLabel := bodyLabel) (postLabel := postLabel)
      (endLabel := endLabel) (source := source)
      (stateAfterCond := stateAfterCond) (target := target)
      (tokens := tokens) (oracle := oracle) (cursor := cursor)
      (cursorAfterCond := cursorAfterCond)
      hCondSafe hCondFrame
      (by simpa [bodyCtx, bodyCode] using hLayout)
      hPc hRel hCond
  refine
    ARunResultWithGasOracle.bind_running
      (program :=
        pre ++
          ForLoop.coreCode cond bodyCode postCode loopLabel bodyLabel
            postLabel endLabel ++ suffix)
      (middle := fun targetAtBody targetCursorAtBody =>
        targetCursorAtBody = cursorAfterCond ∧
          Frame.StateRel stateAfterCond targetAtBody tokens ∧
            targetAtBody.pc = Assembly.Program.pcAfter bodyPre)
      ?_ ?_
  · simpa [bodyCtx, bodyCode, bodyPre] using hEnter
  · intro targetAtBody targetCursorAtBody hAtBody
    rcases hAtBody with ⟨hCursorAtBody, hRelAtBody, hPcAtBody⟩
    subst targetCursorAtBody
    have hBodyCtxResolve :
        ContextLabelsResolve
          (pre ++
            ForLoop.coreCode cond bodyCode postCode loopLabel bodyLabel
              postLabel endLabel ++ suffix)
          bodyCtx :=
      ContextLabelsResolve.with_break_continue
        (ctx := ctx)
        (breakLabel := endLabel) (continueLabel := postLabel)
        (by simpa [bodyCtx, bodyCode] using hResolve)
        ⟨Assembly.Program.byteLength endLabelPre, by
          simpa [bodyCtx, bodyCode, endLabelPre] using hLayout.endLabelPc⟩
        ⟨Assembly.Program.byteLength postLabelPre,
          by simpa [bodyCtx, bodyCode, postLabelPre] using hLayout.postLabelPc⟩
    have hBodyResolve :
        ContextLabelsResolve
          (bodyPre ++ bodyCode ++
            ([Assembly.Instr.label postLabel] ++ postCode ++
              [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel] ++
              suffix))
          bodyCtx := by
      simpa [bodyCtx, bodyCode, ForLoop.coreCode, ForLoop.afterLoopLabel,
        ForLoop.afterCondJumpi, ForLoop.bodyLabelPre, ForLoop.bodyPre,
        bodyPre, List.append_assoc] using hBodyCtxResolve
    have hBodyExact :
        ExactLabels
          (bodyPre ++ bodyCode ++
            ([Assembly.Instr.label postLabel] ++ postCode ++
              [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel] ++
              suffix)) := by
      simpa [bodyCtx, bodyCode, ForLoop.coreCode, ForLoop.afterLoopLabel,
        ForLoop.afterCondJumpi, ForLoop.bodyLabelPre, ForLoop.bodyPre,
        bodyPre, List.append_assoc] using hExact
    have hBodyRun :=
      hBody (pre := bodyPre)
        (post :=
          [Assembly.Instr.label postLabel] ++ postCode ++
            [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel] ++
            suffix)
        (fuel := fuel) (source := stateAfterCond)
        (outcome := Outcome.regular bodyState) (target := targetAtBody)
        (tokens := tokens) (oracle := oracle) (cursor := cursorAfterCond)
        (cursorFinal := cursorAfterBody)
        hLayout.fitBody hBodyResolve hBodyExact hPcAtBody hRelAtBody hBodyEval
    have hBodyRegular :
        ARunResultWithGasOracle
          (bodyPre ++ bodyCode ++
            ([Assembly.Instr.label postLabel] ++ postCode ++
              [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel] ++
              suffix))
          oracle cursorAfterCond targetAtBody
          (fun result targetCursorAtPostLabel =>
            match result with
            | .running targetAtPostLabel =>
                targetCursorAtPostLabel = cursorAfterBody ∧
                  Frame.StateRel bodyState targetAtPostLabel tokens ∧
                    targetAtPostLabel.pc =
                      Assembly.Program.pcAfter postLabelPre
            | .halted _ => False) := by
      exact ARunResultWithGasOracle.mono hBodyRun (by
        intro result targetCursorAtPostLabel hResult
        cases result with
        | halted halt =>
            cases hResult.2
        | running targetAtPostLabel =>
            rcases hResult with ⟨hCursorAtPostLabel, hCompiled⟩
            exact
              ⟨ hCursorAtPostLabel
              , by
                  simpa [bodyCtx, bodyCode, ForLoop.postLabelPre,
                    postLabelPre, CompiledOutcomeRel, Outcome.regular,
                    List.append_assoc] using hCompiled
              ⟩)
    refine
      ARunResultWithGasOracle.bind_running
        (program :=
          pre ++
            ForLoop.coreCode cond bodyCode postCode loopLabel bodyLabel
              postLabel endLabel ++ suffix)
        (middle := fun targetAtPostLabel targetCursorAtPostLabel =>
          targetCursorAtPostLabel = cursorAfterBody ∧
            Frame.StateRel bodyState targetAtPostLabel tokens ∧
              targetAtPostLabel.pc = Assembly.Program.pcAfter postLabelPre)
        ?_ ?_
    · simpa [bodyCtx, bodyCode, ForLoop.coreCode, ForLoop.afterLoopLabel,
        ForLoop.afterCondJumpi, ForLoop.bodyLabelPre, ForLoop.bodyPre,
        bodyPre, postLabelPre, List.append_assoc] using hBodyRegular
    · intro targetAtPostLabel targetCursorAtPostLabel hAtPostLabel
      rcases hAtPostLabel with
        ⟨hCursorAtPostLabel, hRelAtPostLabel, hPcAtPostLabel⟩
      subst targetCursorAtPostLabel
      have hPostLabelRun :=
        FrameStateRel.label_runResult_at_withGasOracle
          (label := postLabel) (pre := postLabelPre)
          (post :=
            postCode ++
              [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel] ++
              suffix)
          (oracle := oracle) (cursor := cursorAfterBody)
          hLayout.fitPostLabel hPcAtPostLabel hRelAtPostLabel
      exact ARunResultWithGasOracle.mono
        (by
          simpa [bodyCtx, bodyCode, ForLoop.coreCode,
            ForLoop.afterLoopLabel, ForLoop.afterCondJumpi,
            ForLoop.bodyLabelPre, ForLoop.bodyPre, ForLoop.postLabelPre,
            ForLoop.postPre, bodyPre, postLabelPre, postPre,
            List.append_assoc] using hPostLabelRun)
        (by
          intro result targetCursorAtPost hResult
          cases result with
          | halted halt =>
              cases hResult
          | running targetAtPost =>
              simpa [bodyCtx, bodyCode, ForLoop.afterLoopLabel,
                ForLoop.afterCondJumpi, ForLoop.bodyLabelPre,
                ForLoop.bodyPre, ForLoop.postLabelPre, ForLoop.postPre,
                bodyPre, postLabelPre, postPre, List.append_assoc] using
                hResult)

theorem post_leave_from_entry_withGasOracle {program : Program}
    {ctx : CompileContext}
    {pre suffix bodyCode : Assembly.Program}
    {cond : Code} {post : Block} {postSupply : LabelSupply}
    {loopLabel bodyLabel postLabel endLabel : Assembly.Label}
    {fuel : Nat}
    {bodyState postState : RunState} {target : EVMState}
    {tokens : List Word} {oracle : GasOracle} {cursor cursorFinal : Nat}
    (hPost :
      BlockPreservesWithGasOracle program
        { ctx with breakLabel? := none, continueLabel? := none }
        postSupply post)
    (hLayout :
      ForLoop.Layout pre suffix cond bodyCode
        (Block.compileFromCtx post
          { ctx with breakLabel? := none, continueLabel? := none }
          postSupply).code
        loopLabel bodyLabel postLabel endLabel)
    (hResolve :
      ContextLabelsResolve
        (pre ++
          ForLoop.coreCode cond bodyCode
            (Block.compileFromCtx post
              { ctx with breakLabel? := none, continueLabel? := none }
              postSupply).code
            loopLabel bodyLabel postLabel endLabel ++ suffix)
        ctx)
    (hExact :
      ExactLabels
        (pre ++
          ForLoop.coreCode cond bodyCode
            (Block.compileFromCtx post
              { ctx with breakLabel? := none, continueLabel? := none }
              postSupply).code
            loopLabel bodyLabel postLabel endLabel ++ suffix))
    (hPc :
      target.pc =
        Assembly.Program.pcAfter
          (ForLoop.postPre pre cond bodyCode loopLabel bodyLabel postLabel
            endLabel))
    (hRel : Frame.StateRel bodyState target tokens)
    (hPostEval :
      Block.EvalWithGasOracle program oracle fuel post cursor bodyState
        (Outcome.leave postState) cursorFinal) :
    ARunResultWithGasOracle
      (pre ++
        ForLoop.coreCode cond bodyCode
          (Block.compileFromCtx post
            { ctx with breakLabel? := none, continueLabel? := none }
            postSupply).code
          loopLabel bodyLabel postLabel endLabel ++ suffix)
      oracle cursor target
      (fun result targetCursorFinal =>
        targetCursorFinal = cursorFinal ∧
          CompiledOutcomeRel
            (pre ++
              ForLoop.coreCode cond bodyCode
                (Block.compileFromCtx post
                  { ctx with breakLabel? := none, continueLabel? := none }
                  postSupply).code
                loopLabel bodyLabel postLabel endLabel ++ suffix)
            ctx
            (Assembly.Program.pcAfter
              (pre ++
                ForLoop.coreCode cond bodyCode
                  (Block.compileFromCtx post
                    { ctx with breakLabel? := none, continueLabel? := none }
                    postSupply).code
                  loopLabel bodyLabel postLabel endLabel))
            (Outcome.leave postState) result tokens) := by
  let postCtx : CompileContext :=
    { ctx with breakLabel? := none, continueLabel? := none }
  let postCode := (Block.compileFromCtx post postCtx postSupply).code
  let postPre :=
    ForLoop.postPre pre cond bodyCode loopLabel bodyLabel postLabel endLabel
  have hPostCtxResolve :
      ContextLabelsResolve
        (pre ++
          ForLoop.coreCode cond bodyCode postCode loopLabel bodyLabel
            postLabel endLabel ++ suffix)
        postCtx :=
    ContextLabelsResolve.without_break_continue
      (ctx := ctx) (by simpa [postCtx, postCode] using hResolve)
  have hPostResolve :
      ContextLabelsResolve
        (postPre ++ postCode ++
          ([Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel] ++
            suffix))
        postCtx := by
    simpa [postCtx, postCode, ForLoop.coreCode, ForLoop.afterLoopLabel,
      ForLoop.afterCondJumpi, ForLoop.bodyLabelPre, ForLoop.bodyPre,
      ForLoop.postLabelPre, ForLoop.postPre, postPre, List.append_assoc]
      using hPostCtxResolve
  have hPostExact :
      ExactLabels
        (postPre ++ postCode ++
          ([Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel] ++
            suffix)) := by
    simpa [postCtx, postCode, ForLoop.coreCode, ForLoop.afterLoopLabel,
      ForLoop.afterCondJumpi, ForLoop.bodyLabelPre, ForLoop.bodyPre,
      ForLoop.postLabelPre, ForLoop.postPre, postPre, List.append_assoc]
      using hExact
  have hPostRun :=
    hPost (pre := postPre)
      (post := [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel] ++
        suffix)
      (fuel := fuel) (source := bodyState)
      (outcome := Outcome.leave postState) (target := target)
      (tokens := tokens) (oracle := oracle) (cursor := cursor)
      (cursorFinal := cursorFinal)
      hLayout.fitPost hPostResolve hPostExact hPc hRel hPostEval
  exact ARunResultWithGasOracle.mono
    (by
      simpa [postCtx, postCode, ForLoop.coreCode, ForLoop.afterLoopLabel,
        ForLoop.afterCondJumpi, ForLoop.bodyLabelPre, ForLoop.bodyPre,
        ForLoop.postLabelPre, ForLoop.postPre, postPre, List.append_assoc]
        using hPostRun)
    (by
      intro result targetCursorFinal hResult
      rcases hResult with ⟨hCursorFinal, hCompiled⟩
      cases result with
      | halted halt =>
          cases hCompiled
      | running target' =>
          exact
            ⟨ hCursorFinal
            , by
                simpa [postCtx, postCode, ForLoop.coreCode,
                  ForLoop.afterLoopLabel, ForLoop.afterCondJumpi,
                  ForLoop.bodyLabelPre, ForLoop.bodyPre, ForLoop.postLabelPre,
                  ForLoop.postPre, postPre, CompiledOutcomeRel,
                  Outcome.leave, List.append_assoc] using hCompiled
            ⟩)

theorem post_halt_from_entry_withGasOracle {program : Program}
    {ctx : CompileContext}
    {pre suffix bodyCode : Assembly.Program}
    {cond : Code} {post : Block} {postSupply : LabelSupply}
    {loopLabel bodyLabel postLabel endLabel : Assembly.Label}
    {fuel : Nat}
    {bodyState postState : RunState} {target : EVMState}
    {tokens : List Word} {kind : Assembly.HaltKind}
    {oracle : GasOracle} {cursor cursorFinal : Nat}
    (hPost :
      BlockPreservesWithGasOracle program
        { ctx with breakLabel? := none, continueLabel? := none }
        postSupply post)
    (hLayout :
      ForLoop.Layout pre suffix cond bodyCode
        (Block.compileFromCtx post
          { ctx with breakLabel? := none, continueLabel? := none }
          postSupply).code
        loopLabel bodyLabel postLabel endLabel)
    (hResolve :
      ContextLabelsResolve
        (pre ++
          ForLoop.coreCode cond bodyCode
            (Block.compileFromCtx post
              { ctx with breakLabel? := none, continueLabel? := none }
              postSupply).code
            loopLabel bodyLabel postLabel endLabel ++ suffix)
        ctx)
    (hExact :
      ExactLabels
        (pre ++
          ForLoop.coreCode cond bodyCode
            (Block.compileFromCtx post
              { ctx with breakLabel? := none, continueLabel? := none }
              postSupply).code
            loopLabel bodyLabel postLabel endLabel ++ suffix))
    (hPc :
      target.pc =
        Assembly.Program.pcAfter
          (ForLoop.postPre pre cond bodyCode loopLabel bodyLabel postLabel
            endLabel))
    (hRel : Frame.StateRel bodyState target tokens)
    (hPostEval :
      Block.EvalWithGasOracle program oracle fuel post cursor bodyState
        (Outcome.halt kind postState) cursorFinal) :
    ARunResultWithGasOracle
      (pre ++
        ForLoop.coreCode cond bodyCode
          (Block.compileFromCtx post
            { ctx with breakLabel? := none, continueLabel? := none }
            postSupply).code
          loopLabel bodyLabel postLabel endLabel ++ suffix)
      oracle cursor target
      (fun result targetCursorFinal =>
        targetCursorFinal = cursorFinal ∧
          CompiledOutcomeRel
            (pre ++
              ForLoop.coreCode cond bodyCode
                (Block.compileFromCtx post
                  { ctx with breakLabel? := none, continueLabel? := none }
                  postSupply).code
                loopLabel bodyLabel postLabel endLabel ++ suffix)
            ctx
            (Assembly.Program.pcAfter
              (pre ++
                ForLoop.coreCode cond bodyCode
                  (Block.compileFromCtx post
                    { ctx with breakLabel? := none, continueLabel? := none }
                    postSupply).code
                  loopLabel bodyLabel postLabel endLabel))
            (Outcome.halt kind postState) result tokens) := by
  let postCtx : CompileContext :=
    { ctx with breakLabel? := none, continueLabel? := none }
  let postCode := (Block.compileFromCtx post postCtx postSupply).code
  let postPre :=
    ForLoop.postPre pre cond bodyCode loopLabel bodyLabel postLabel endLabel
  have hPostCtxResolve :
      ContextLabelsResolve
        (pre ++
          ForLoop.coreCode cond bodyCode postCode loopLabel bodyLabel
            postLabel endLabel ++ suffix)
        postCtx :=
    ContextLabelsResolve.without_break_continue
      (ctx := ctx) (by simpa [postCtx, postCode] using hResolve)
  have hPostResolve :
      ContextLabelsResolve
        (postPre ++ postCode ++
          ([Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel] ++
            suffix))
        postCtx := by
    simpa [postCtx, postCode, ForLoop.coreCode, ForLoop.afterLoopLabel,
      ForLoop.afterCondJumpi, ForLoop.bodyLabelPre, ForLoop.bodyPre,
      ForLoop.postLabelPre, ForLoop.postPre, postPre, List.append_assoc]
      using hPostCtxResolve
  have hPostExact :
      ExactLabels
        (postPre ++ postCode ++
          ([Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel] ++
            suffix)) := by
    simpa [postCtx, postCode, ForLoop.coreCode, ForLoop.afterLoopLabel,
      ForLoop.afterCondJumpi, ForLoop.bodyLabelPre, ForLoop.bodyPre,
      ForLoop.postLabelPre, ForLoop.postPre, postPre, List.append_assoc]
      using hExact
  have hPostRun :=
    hPost (pre := postPre)
      (post := [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel] ++
        suffix)
      (fuel := fuel) (source := bodyState)
      (outcome := Outcome.halt kind postState) (target := target)
      (tokens := tokens) (oracle := oracle) (cursor := cursor)
      (cursorFinal := cursorFinal)
      hLayout.fitPost hPostResolve hPostExact hPc hRel hPostEval
  exact ARunResultWithGasOracle.mono
    (by
      simpa [postCtx, postCode, ForLoop.coreCode, ForLoop.afterLoopLabel,
        ForLoop.afterCondJumpi, ForLoop.bodyLabelPre, ForLoop.bodyPre,
        ForLoop.postLabelPre, ForLoop.postPre, postPre, List.append_assoc]
        using hPostRun)
    (by
      intro result targetCursorFinal hResult
      rcases hResult with ⟨hCursorFinal, hCompiled⟩
      cases result with
      | running target' =>
          cases hCompiled
      | halted halt =>
          exact
            ⟨ hCursorFinal
            , by
                simpa [postCtx, postCode, ForLoop.coreCode,
                  ForLoop.afterLoopLabel, ForLoop.afterCondJumpi,
                  ForLoop.bodyLabelPre, ForLoop.bodyPre, ForLoop.postLabelPre,
                  ForLoop.postPre, postPre, CompiledOutcomeRel, Outcome.halt,
                  List.append_assoc] using hCompiled
            ⟩)

theorem post_regular_jump_loop_withGasOracle {program : Program}
    {ctx : CompileContext}
    {pre suffix bodyCode : Assembly.Program}
    {cond : Code} {post : Block} {postSupply : LabelSupply}
    {loopLabel bodyLabel postLabel endLabel : Assembly.Label}
    {fuel : Nat}
    {bodyState postState : RunState} {target : EVMState}
    {tokens : List Word} {oracle : GasOracle} {cursor cursorAfterPost : Nat}
    (hPost :
      BlockPreservesWithGasOracle program
        { ctx with breakLabel? := none, continueLabel? := none }
        postSupply post)
    (hLayout :
      ForLoop.Layout pre suffix cond bodyCode
        (Block.compileFromCtx post
          { ctx with breakLabel? := none, continueLabel? := none }
          postSupply).code
        loopLabel bodyLabel postLabel endLabel)
    (hResolve :
      ContextLabelsResolve
        (pre ++
          ForLoop.coreCode cond bodyCode
            (Block.compileFromCtx post
              { ctx with breakLabel? := none, continueLabel? := none }
              postSupply).code
            loopLabel bodyLabel postLabel endLabel ++ suffix)
        ctx)
    (hExact :
      ExactLabels
        (pre ++
          ForLoop.coreCode cond bodyCode
            (Block.compileFromCtx post
              { ctx with breakLabel? := none, continueLabel? := none }
              postSupply).code
            loopLabel bodyLabel postLabel endLabel ++ suffix))
    (hPc :
      target.pc =
        Assembly.Program.pcAfter
          (ForLoop.postPre pre cond bodyCode loopLabel bodyLabel postLabel
            endLabel))
    (hRel : Frame.StateRel bodyState target tokens)
    (hPostEval :
      Block.EvalWithGasOracle program oracle fuel post cursor bodyState
        (Outcome.regular postState) cursorAfterPost) :
    ARunResultWithGasOracle
      (pre ++
        ForLoop.coreCode cond bodyCode
          (Block.compileFromCtx post
            { ctx with breakLabel? := none, continueLabel? := none }
            postSupply).code
          loopLabel bodyLabel postLabel endLabel ++ suffix)
      oracle cursor target
      (fun result targetCursorAtLoop =>
        match result with
        | .running targetAtLoop =>
            targetCursorAtLoop = cursorAfterPost ∧
              Frame.StateRel postState targetAtLoop tokens ∧
                targetAtLoop.pc = Assembly.Program.pcAfter pre
        | .halted _ => False) := by
  let postCtx : CompileContext :=
    { ctx with breakLabel? := none, continueLabel? := none }
  let postCode := (Block.compileFromCtx post postCtx postSupply).code
  let postPre :=
    ForLoop.postPre pre cond bodyCode loopLabel bodyLabel postLabel endLabel
  have hPostCtxResolve :
      ContextLabelsResolve
        (pre ++
          ForLoop.coreCode cond bodyCode postCode loopLabel bodyLabel
            postLabel endLabel ++ suffix)
        postCtx :=
    ContextLabelsResolve.without_break_continue
      (ctx := ctx) (by simpa [postCtx, postCode] using hResolve)
  have hPostResolve :
      ContextLabelsResolve
        (postPre ++ postCode ++
          ([Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel] ++
            suffix))
        postCtx := by
    simpa [postCtx, postCode, ForLoop.coreCode, ForLoop.afterLoopLabel,
      ForLoop.afterCondJumpi, ForLoop.bodyLabelPre, ForLoop.bodyPre,
      ForLoop.postLabelPre, ForLoop.postPre, postPre, List.append_assoc]
      using hPostCtxResolve
  have hPostExact :
      ExactLabels
        (postPre ++ postCode ++
          ([Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel] ++
            suffix)) := by
    simpa [postCtx, postCode, ForLoop.coreCode, ForLoop.afterLoopLabel,
      ForLoop.afterCondJumpi, ForLoop.bodyLabelPre, ForLoop.bodyPre,
      ForLoop.postLabelPre, ForLoop.postPre, postPre, List.append_assoc]
      using hExact
  have hPostRun :=
    hPost (pre := postPre)
      (post := [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel] ++
        suffix)
      (fuel := fuel) (source := bodyState)
      (outcome := Outcome.regular postState) (target := target)
      (tokens := tokens) (oracle := oracle) (cursor := cursor)
      (cursorFinal := cursorAfterPost)
      hLayout.fitPost hPostResolve hPostExact hPc hRel hPostEval
  have hPostRegular :
      ARunResultWithGasOracle
        (pre ++
          ForLoop.coreCode cond bodyCode postCode loopLabel bodyLabel
            postLabel endLabel ++ suffix)
        oracle cursor target
        (fun result targetCursorAtBackJump =>
          match result with
          | .running targetAtBackJump =>
              targetCursorAtBackJump = cursorAfterPost ∧
                Frame.StateRel postState targetAtBackJump tokens ∧
                  targetAtBackJump.pc =
                    Assembly.Program.pcAfter (postPre ++ postCode)
          | .halted _ => False) := by
    exact ARunResultWithGasOracle.mono
      (by
        simpa [postCtx, postCode, ForLoop.coreCode, ForLoop.afterLoopLabel,
          ForLoop.afterCondJumpi, ForLoop.bodyLabelPre, ForLoop.bodyPre,
          ForLoop.postLabelPre, ForLoop.postPre, postPre, List.append_assoc]
          using hPostRun)
      (by
        intro result targetCursorAtBackJump hResult
        cases result with
        | halted halt =>
            cases hResult.2
        | running targetAtBackJump =>
            rcases hResult with ⟨hCursorAtBackJump, hCompiled⟩
            exact
              ⟨ hCursorAtBackJump
              , by
                  simpa [postCtx, postCode, ForLoop.coreCode,
                    ForLoop.afterLoopLabel, ForLoop.afterCondJumpi,
                    ForLoop.bodyLabelPre, ForLoop.bodyPre,
                    ForLoop.postLabelPre, ForLoop.postPre, postPre,
                    CompiledOutcomeRel, Outcome.regular, List.append_assoc]
                    using hCompiled
              ⟩)
  refine
    ARunResultWithGasOracle.bind_running
      (program :=
        pre ++
          ForLoop.coreCode cond bodyCode postCode loopLabel bodyLabel
            postLabel endLabel ++ suffix)
      (middle := fun targetAtBackJump targetCursorAtBackJump =>
        targetCursorAtBackJump = cursorAfterPost ∧
          Frame.StateRel postState targetAtBackJump tokens ∧
            targetAtBackJump.pc =
              Assembly.Program.pcAfter (postPre ++ postCode))
      hPostRegular ?_
  intro targetAtBackJump targetCursorAtBackJump hAtBackJump
  rcases hAtBackJump with
    ⟨hCursorAtBackJump, hRelAtBackJump, hPcAtBackJump⟩
  subst targetCursorAtBackJump
  have hLoopLabel :
      Assembly.Program.labelPc
        ((postPre ++ postCode) ++ [Assembly.Instr.jump loopLabel] ++
          ([Assembly.Instr.label endLabel] ++ suffix))
        loopLabel = some (Assembly.Program.byteLength pre) := by
    simpa [postCtx, postCode, ForLoop.coreCode, ForLoop.afterLoopLabel,
      ForLoop.afterCondJumpi, ForLoop.bodyLabelPre, ForLoop.bodyPre,
      ForLoop.postLabelPre, ForLoop.postPre, postPre, List.append_assoc]
      using hLayout.loopLabelPc
  rcases FrameStateRel.jump_stepResult_at_withGasOracle
      (label := loopLabel) (dest := Assembly.Program.byteLength pre)
      (pre := postPre ++ postCode)
      (post := [Assembly.Instr.label endLabel] ++ suffix)
      (oracle := oracle) (cursor := cursorAfterPost)
      hLayout.fitBackJump hPcAtBackJump hRelAtBackJump hLoopLabel with
    ⟨targetAtLoop, hJump, hRelLoop, hPcLoop⟩
  refine ⟨1, .running targetAtLoop, cursorAfterPost, ?_, ?_⟩
  · change
      Assembly.GasParametric.sourceRunNResultWithGasOracle
          (pre ++
            ForLoop.coreCode cond bodyCode postCode loopLabel bodyLabel
              postLabel endLabel ++ suffix)
          oracle 1 cursorAfterPost targetAtBackJump =
        .ok (.running targetAtLoop, cursorAfterPost)
    have hJump' :
        Assembly.GasParametric.sourceStepResultWithGasOracle
            ((postPre ++ postCode) ++ [Assembly.Instr.jump loopLabel] ++
              ([Assembly.Instr.label endLabel] ++ suffix))
            oracle cursorAfterPost targetAtBackJump =
          .ok (.running targetAtLoop, cursorAfterPost) := by
      simpa using hJump
    rw [show
        pre ++
            ForLoop.coreCode cond bodyCode postCode loopLabel bodyLabel
              postLabel endLabel ++ suffix =
          (postPre ++ postCode) ++ [Assembly.Instr.jump loopLabel] ++
            ([Assembly.Instr.label endLabel] ++ suffix) by
        simp [ForLoop.coreCode, ForLoop.afterLoopLabel,
          ForLoop.afterCondJumpi, ForLoop.bodyLabelPre, ForLoop.bodyPre,
          ForLoop.postLabelPre, ForLoop.postPre, postPre, List.append_assoc]]
    unfold Assembly.GasParametric.sourceRunNResultWithGasOracle
    rw [hJump']
    rfl
  · exact ⟨rfl, hRelLoop, by rw [hPcLoop]; rfl⟩

theorem body_cont_enter_post_withGasOracle {program : Program}
    {ctx : CompileContext}
    {pre suffix postCode : Assembly.Program}
    {cond : Code} {body : Block} {bodySupply : LabelSupply}
    {loopLabel bodyLabel postLabel endLabel : Assembly.Label}
    {fuel : Nat}
    {source stateAfterCond bodyState : RunState} {target : EVMState}
    {tokens : List Word} {oracle : GasOracle}
    {cursor cursorAfterCond cursorAfterBody : Nat}
    (hCondSafe : Code.RunnerSafeWithGasOracle cond)
    (hCondFrame : Code.FrameSafeWithGasOracle cond)
    (hBody :
      BlockPreservesWithGasOracle program
        { ctx with
          breakLabel? := some endLabel
          continueLabel? := some postLabel }
        bodySupply body)
    (hLayout :
      ForLoop.Layout pre suffix cond
        (Block.compileFromCtx body
          { ctx with
            breakLabel? := some endLabel
            continueLabel? := some postLabel }
          bodySupply).code
        postCode loopLabel bodyLabel postLabel endLabel)
    (hResolve :
      ContextLabelsResolve
        (pre ++
          ForLoop.coreCode cond
            (Block.compileFromCtx body
              { ctx with
                breakLabel? := some endLabel
                continueLabel? := some postLabel }
              bodySupply).code
            postCode loopLabel bodyLabel postLabel endLabel ++ suffix)
        ctx)
    (hExact :
      ExactLabels
        (pre ++
          ForLoop.coreCode cond
            (Block.compileFromCtx body
              { ctx with
                breakLabel? := some endLabel
                continueLabel? := some postLabel }
              bodySupply).code
            postCode loopLabel bodyLabel postLabel endLabel ++ suffix))
    (hPc : target.pc = Assembly.Program.pcAfter pre)
    (hRel : Frame.StateRel source target tokens)
    (hCond :
      Code.runConditionStateWithGasOracle cond oracle cursor source =
        .ok (stateAfterCond, true, cursorAfterCond))
    (hBodyEval :
      Block.EvalWithGasOracle program oracle fuel body cursorAfterCond
        stateAfterCond (Outcome.cont bodyState) cursorAfterBody) :
    ARunResultWithGasOracle
      (pre ++
        ForLoop.coreCode cond
          (Block.compileFromCtx body
            { ctx with
              breakLabel? := some endLabel
              continueLabel? := some postLabel }
            bodySupply).code
          postCode loopLabel bodyLabel postLabel endLabel ++ suffix)
      oracle cursor target
      (fun result targetCursorAtPost =>
        match result with
        | .running targetAtPost =>
            targetCursorAtPost = cursorAfterBody ∧
              Frame.StateRel bodyState targetAtPost tokens ∧
                targetAtPost.pc =
                  Assembly.Program.pcAfter
                    (ForLoop.postPre pre cond
                      (Block.compileFromCtx body
                        { ctx with
                          breakLabel? := some endLabel
                          continueLabel? := some postLabel }
                        bodySupply).code
                      loopLabel bodyLabel postLabel endLabel)
        | .halted _ => False) := by
  let bodyCtx : CompileContext :=
    { ctx with
      breakLabel? := some endLabel
      continueLabel? := some postLabel }
  let bodyCode := (Block.compileFromCtx body bodyCtx bodySupply).code
  let bodyPre := ForLoop.bodyPre pre cond loopLabel bodyLabel endLabel
  let postLabelPre :=
    ForLoop.postLabelPre pre cond bodyCode loopLabel bodyLabel endLabel
  let postPre :=
    ForLoop.postPre pre cond bodyCode loopLabel bodyLabel postLabel endLabel
  let endLabelPre :=
    ForLoop.endLabelPre pre cond bodyCode postCode loopLabel bodyLabel
      postLabel endLabel
  have hEnter :=
    enter_body_withGasOracle
      (pre := pre) (suffix := suffix) (bodyCode := bodyCode)
      (postCode := postCode) (cond := cond) (loopLabel := loopLabel)
      (bodyLabel := bodyLabel) (postLabel := postLabel)
      (endLabel := endLabel) (source := source)
      (stateAfterCond := stateAfterCond) (target := target)
      (tokens := tokens) (oracle := oracle) (cursor := cursor)
      (cursorAfterCond := cursorAfterCond)
      hCondSafe hCondFrame
      (by simpa [bodyCtx, bodyCode] using hLayout)
      hPc hRel hCond
  refine
    ARunResultWithGasOracle.bind_running
      (program :=
        pre ++
          ForLoop.coreCode cond bodyCode postCode loopLabel bodyLabel
            postLabel endLabel ++ suffix)
      (middle := fun targetAtBody targetCursorAtBody =>
        targetCursorAtBody = cursorAfterCond ∧
          Frame.StateRel stateAfterCond targetAtBody tokens ∧
            targetAtBody.pc = Assembly.Program.pcAfter bodyPre)
      ?_ ?_
  · simpa [bodyCtx, bodyCode, bodyPre] using hEnter
  · intro targetAtBody targetCursorAtBody hAtBody
    rcases hAtBody with ⟨hCursorAtBody, hRelAtBody, hPcAtBody⟩
    subst targetCursorAtBody
    have hBodyCtxResolve :
        ContextLabelsResolve
          (pre ++
            ForLoop.coreCode cond bodyCode postCode loopLabel bodyLabel
              postLabel endLabel ++ suffix)
          bodyCtx :=
      ContextLabelsResolve.with_break_continue
        (ctx := ctx)
        (breakLabel := endLabel) (continueLabel := postLabel)
        (by simpa [bodyCtx, bodyCode] using hResolve)
        ⟨Assembly.Program.byteLength endLabelPre, by
          simpa [bodyCtx, bodyCode, endLabelPre] using hLayout.endLabelPc⟩
        ⟨Assembly.Program.byteLength postLabelPre,
          by simpa [bodyCtx, bodyCode, postLabelPre] using hLayout.postLabelPc⟩
    have hBodyResolve :
        ContextLabelsResolve
          (bodyPre ++ bodyCode ++
            ([Assembly.Instr.label postLabel] ++ postCode ++
              [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel] ++
              suffix))
          bodyCtx := by
      simpa [bodyCtx, bodyCode, ForLoop.coreCode, ForLoop.afterLoopLabel,
        ForLoop.afterCondJumpi, ForLoop.bodyLabelPre, ForLoop.bodyPre,
        bodyPre, List.append_assoc] using hBodyCtxResolve
    have hBodyExact :
        ExactLabels
          (bodyPre ++ bodyCode ++
            ([Assembly.Instr.label postLabel] ++ postCode ++
              [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel] ++
              suffix)) := by
      simpa [bodyCtx, bodyCode, ForLoop.coreCode, ForLoop.afterLoopLabel,
        ForLoop.afterCondJumpi, ForLoop.bodyLabelPre, ForLoop.bodyPre,
        bodyPre, List.append_assoc] using hExact
    have hBodyRun :=
      hBody (pre := bodyPre)
        (post :=
          [Assembly.Instr.label postLabel] ++ postCode ++
            [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel] ++
            suffix)
        (fuel := fuel) (source := stateAfterCond)
        (outcome := Outcome.cont bodyState) (target := targetAtBody)
        (tokens := tokens) (oracle := oracle) (cursor := cursorAfterCond)
        (cursorFinal := cursorAfterBody)
        hLayout.fitBody hBodyResolve hBodyExact hPcAtBody hRelAtBody hBodyEval
    have hBodyCont :
        ARunResultWithGasOracle
          (bodyPre ++ bodyCode ++
            ([Assembly.Instr.label postLabel] ++ postCode ++
              [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel] ++
              suffix))
          oracle cursorAfterCond targetAtBody
          (fun result targetCursorAtPostLabel =>
            match result with
            | .running targetAtPostLabel =>
                targetCursorAtPostLabel = cursorAfterBody ∧
                  Frame.StateRel bodyState targetAtPostLabel tokens ∧
                    targetAtPostLabel.pc =
                      Assembly.Program.pcAfter postLabelPre
            | .halted _ => False) := by
      exact ARunResultWithGasOracle.mono hBodyRun (by
        intro result targetCursorAtPostLabel hResult
        cases result with
        | halted halt =>
            cases hResult.2
        | running targetAtPostLabel =>
            rcases hResult with ⟨hCursorAtPostLabel, hCompiled⟩
            rcases hCompiled with
              ⟨label, dest, hCtxCont, hLabel, hTargetRel, hTargetPc⟩
            simp at hCtxCont
            subst label
            have hPostLabelHere :
                Assembly.Program.labelPc
                  (bodyPre ++ bodyCode ++
                    ([Assembly.Instr.label postLabel] ++ postCode ++
                      [ Assembly.Instr.jump loopLabel
                      , Assembly.Instr.label endLabel
                      ] ++ suffix))
                  postLabel =
                    some (Assembly.Program.byteLength postLabelPre) := by
              simpa [bodyCtx, bodyCode, ForLoop.coreCode,
                ForLoop.afterLoopLabel, ForLoop.afterCondJumpi,
                ForLoop.bodyLabelPre, ForLoop.bodyPre,
                ForLoop.postLabelPre, bodyPre, postLabelPre,
                List.append_assoc] using hLayout.postLabelPc
            have hDest : dest = Assembly.Program.byteLength postLabelPre := by
              rw [hPostLabelHere] at hLabel
              cases hLabel
              rfl
            refine ⟨hCursorAtPostLabel, hTargetRel, ?_⟩
            rw [hTargetPc, hDest]
            rfl)
    refine
      ARunResultWithGasOracle.bind_running
        (program :=
          pre ++
            ForLoop.coreCode cond bodyCode postCode loopLabel bodyLabel
              postLabel endLabel ++ suffix)
        (middle := fun targetAtPostLabel targetCursorAtPostLabel =>
          targetCursorAtPostLabel = cursorAfterBody ∧
            Frame.StateRel bodyState targetAtPostLabel tokens ∧
              targetAtPostLabel.pc = Assembly.Program.pcAfter postLabelPre)
        ?_ ?_
    · simpa [bodyCtx, bodyCode, ForLoop.coreCode, ForLoop.afterLoopLabel,
        ForLoop.afterCondJumpi, ForLoop.bodyLabelPre, ForLoop.bodyPre,
        bodyPre, postLabelPre, List.append_assoc] using hBodyCont
    · intro targetAtPostLabel targetCursorAtPostLabel hAtPostLabel
      rcases hAtPostLabel with
        ⟨hCursorAtPostLabel, hRelAtPostLabel, hPcAtPostLabel⟩
      subst targetCursorAtPostLabel
      have hPostLabelRun :=
        FrameStateRel.label_runResult_at_withGasOracle
          (label := postLabel) (pre := postLabelPre)
          (post :=
            postCode ++
              [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel] ++
              suffix)
          (oracle := oracle) (cursor := cursorAfterBody)
          hLayout.fitPostLabel hPcAtPostLabel hRelAtPostLabel
      exact ARunResultWithGasOracle.mono
        (by
          simpa [bodyCtx, bodyCode, ForLoop.coreCode,
            ForLoop.afterLoopLabel, ForLoop.afterCondJumpi,
            ForLoop.bodyLabelPre, ForLoop.bodyPre, ForLoop.postLabelPre,
            ForLoop.postPre, bodyPre, postLabelPre, postPre,
            List.append_assoc] using hPostLabelRun)
        (by
          intro result targetCursorAtPost hResult
          cases result with
          | halted halt =>
              cases hResult
          | running targetAtPost =>
              simpa [bodyCtx, bodyCode, ForLoop.afterLoopLabel,
                ForLoop.afterCondJumpi, ForLoop.bodyLabelPre,
                ForLoop.bodyPre, ForLoop.postLabelPre, ForLoop.postPre,
                bodyPre, postLabelPre, postPre, List.append_assoc] using
                hResult)

theorem preserves_eval_withGasOracle {program : Program} {ctx : CompileContext}
    {cond : Code} {body post : Block}
    {bodySupply postSupply : LabelSupply}
    {loopLabel bodyLabel postLabel endLabel : Assembly.Label}
    (hCondSafe : Code.RunnerSafeWithGasOracle cond)
    (hCondFrame : Code.FrameSafeWithGasOracle cond)
    (hBody :
      BlockPreservesWithGasOracle program
        { ctx with
          breakLabel? := some endLabel
          continueLabel? := some postLabel }
        bodySupply body)
    (hPost :
      BlockPreservesWithGasOracle program
        { ctx with breakLabel? := none, continueLabel? := none }
        postSupply post) :
    ∀ {pre suffix : Assembly.Program} {fuel : Nat}
      {source : RunState} {outcome : Outcome} {target : EVMState}
      {tokens : List Word} {oracle : GasOracle} {cursor cursorFinal : Nat},
      ForLoop.Layout pre suffix cond
        (Block.compileFromCtx body
          { ctx with
            breakLabel? := some endLabel
            continueLabel? := some postLabel }
          bodySupply).code
        (Block.compileFromCtx post
          { ctx with breakLabel? := none, continueLabel? := none }
          postSupply).code
        loopLabel bodyLabel postLabel endLabel →
      ContextLabelsResolve
        (pre ++
          ForLoop.coreCode cond
            (Block.compileFromCtx body
              { ctx with
                breakLabel? := some endLabel
                continueLabel? := some postLabel }
              bodySupply).code
            (Block.compileFromCtx post
              { ctx with breakLabel? := none, continueLabel? := none }
              postSupply).code
            loopLabel bodyLabel postLabel endLabel ++ suffix)
        ctx →
      ExactLabels
        (pre ++
          ForLoop.coreCode cond
            (Block.compileFromCtx body
              { ctx with
                breakLabel? := some endLabel
                continueLabel? := some postLabel }
              bodySupply).code
            (Block.compileFromCtx post
              { ctx with breakLabel? := none, continueLabel? := none }
              postSupply).code
            loopLabel bodyLabel postLabel endLabel ++ suffix) →
      target.pc = Assembly.Program.pcAfter pre →
      Frame.StateRel source target tokens →
      For.EvalWithGasOracle program oracle fuel cond post body cursor source
        outcome cursorFinal →
      ARunResultWithGasOracle
        (pre ++
          ForLoop.coreCode cond
            (Block.compileFromCtx body
              { ctx with
                breakLabel? := some endLabel
                continueLabel? := some postLabel }
              bodySupply).code
            (Block.compileFromCtx post
              { ctx with breakLabel? := none, continueLabel? := none }
              postSupply).code
            loopLabel bodyLabel postLabel endLabel ++ suffix)
        oracle cursor target
        (fun result targetCursorFinal =>
          targetCursorFinal = cursorFinal ∧
            CompiledOutcomeRel
              (pre ++
                ForLoop.coreCode cond
                  (Block.compileFromCtx body
                    { ctx with
                      breakLabel? := some endLabel
                      continueLabel? := some postLabel }
                    bodySupply).code
                  (Block.compileFromCtx post
                    { ctx with breakLabel? := none, continueLabel? := none }
                    postSupply).code
                  loopLabel bodyLabel postLabel endLabel ++ suffix)
              ctx
              (Assembly.Program.pcAfter
                (pre ++
                  ForLoop.coreCode cond
                    (Block.compileFromCtx body
                      { ctx with
                        breakLabel? := some endLabel
                        continueLabel? := some postLabel }
                      bodySupply).code
                    (Block.compileFromCtx post
                      { ctx with breakLabel? := none, continueLabel? := none }
                      postSupply).code
                    loopLabel bodyLabel postLabel endLabel))
              outcome result tokens) := by
  intro pre suffix fuel source outcome target tokens oracle cursor cursorFinal
    hLayout hResolve hExact hPc hRel hEval
  induction fuel generalizing pre suffix source outcome target tokens oracle
      cursor cursorFinal with
  | zero =>
      cases hEval
  | succ fuel ih =>
    cases hEval with
    | false hCond =>
      exact
        false_case_withGasOracle (ctx := ctx) (pre := pre) (suffix := suffix)
          (bodyCode :=
            (Block.compileFromCtx body
              { ctx with
                breakLabel? := some endLabel
                continueLabel? := some postLabel }
              bodySupply).code)
          (postCode :=
            (Block.compileFromCtx post
              { ctx with breakLabel? := none, continueLabel? := none }
              postSupply).code)
          (cond := cond) (loopLabel := loopLabel)
          (bodyLabel := bodyLabel) (postLabel := postLabel)
          (endLabel := endLabel)
          hCondSafe hCondFrame hLayout hPc hRel hCond
    | body_brk hCond hBodyEval =>
      exact
        body_brk_case_withGasOracle (program := program) (ctx := ctx)
          (pre := pre) (suffix := suffix)
          (postCode :=
            (Block.compileFromCtx post
              { ctx with breakLabel? := none, continueLabel? := none }
              postSupply).code)
          (cond := cond) (body := body) (bodySupply := bodySupply)
          (loopLabel := loopLabel) (bodyLabel := bodyLabel)
          (postLabel := postLabel) (endLabel := endLabel)
          hCondSafe hCondFrame hBody hLayout hResolve hExact hPc hRel
          hCond hBodyEval
    | body_leave hCond hBodyEval =>
      exact
        body_leave_case_withGasOracle (program := program) (ctx := ctx)
          (pre := pre) (suffix := suffix)
          (postCode :=
            (Block.compileFromCtx post
              { ctx with breakLabel? := none, continueLabel? := none }
              postSupply).code)
          (cond := cond) (body := body) (bodySupply := bodySupply)
          (loopLabel := loopLabel) (bodyLabel := bodyLabel)
          (postLabel := postLabel) (endLabel := endLabel)
          hCondSafe hCondFrame hBody hLayout hResolve hExact hPc hRel
          hCond hBodyEval
    | body_halt hCond hBodyEval =>
      exact
        body_halt_case_withGasOracle (program := program) (ctx := ctx)
          (pre := pre) (suffix := suffix)
          (postCode :=
            (Block.compileFromCtx post
              { ctx with breakLabel? := none, continueLabel? := none }
              postSupply).code)
          (cond := cond) (body := body) (bodySupply := bodySupply)
          (loopLabel := loopLabel) (bodyLabel := bodyLabel)
          (postLabel := postLabel) (endLabel := endLabel)
          hCondSafe hCondFrame hBody hLayout hResolve hExact hPc hRel
          hCond hBodyEval
    | regular_post_regular hCond hBodyEval hPostEval hLoop =>
      rename_i cursorAfterCond cursorAfterBody cursorAfterPost
        stateAfterCond bodyState postState
      let bodyCtx : CompileContext :=
        { ctx with
          breakLabel? := some endLabel
          continueLabel? := some postLabel }
      let postCtx : CompileContext :=
        { ctx with breakLabel? := none, continueLabel? := none }
      let bodyCode := (Block.compileFromCtx body bodyCtx bodySupply).code
      let postCode := (Block.compileFromCtx post postCtx postSupply).code
      let postPre :=
        ForLoop.postPre pre cond bodyCode loopLabel bodyLabel postLabel
          endLabel
      have hEnterPost :=
        body_regular_enter_post_withGasOracle
          (program := program) (ctx := ctx) (pre := pre)
          (suffix := suffix) (postCode := postCode) (cond := cond)
          (body := body) (bodySupply := bodySupply)
          (loopLabel := loopLabel) (bodyLabel := bodyLabel)
          (postLabel := postLabel) (endLabel := endLabel)
          (fuel := fuel) (source := source)
          (stateAfterCond := stateAfterCond) (bodyState := bodyState)
          (target := target) (tokens := tokens) (oracle := oracle)
          (cursor := cursor) (cursorAfterCond := cursorAfterCond)
          (cursorAfterBody := cursorAfterBody)
          hCondSafe hCondFrame hBody
          (by simpa [bodyCtx, postCtx, bodyCode, postCode] using hLayout)
          (by simpa [bodyCtx, postCtx, bodyCode, postCode] using hResolve)
          (by simpa [bodyCtx, postCtx, bodyCode, postCode] using hExact)
          hPc hRel hCond hBodyEval
      refine
        ARunResultWithGasOracle.bind_running
          (program :=
            pre ++
              ForLoop.coreCode cond bodyCode postCode loopLabel bodyLabel
                postLabel endLabel ++ suffix)
          (middle := fun targetAtPost targetCursorAtPost =>
            targetCursorAtPost = cursorAfterBody ∧
              Frame.StateRel bodyState targetAtPost tokens ∧
                targetAtPost.pc = Assembly.Program.pcAfter postPre)
          ?_ ?_
      · simpa [bodyCtx, postCtx, bodyCode, postCode, postPre] using hEnterPost
      · intro targetAtPost targetCursorAtPost hAtPost
        rcases hAtPost with
          ⟨hCursorAtPost, hRelAtPost, hPcAtPost⟩
        subst targetCursorAtPost
        have hBackToLoop :=
          post_regular_jump_loop_withGasOracle
            (program := program) (ctx := ctx) (pre := pre)
            (suffix := suffix) (bodyCode := bodyCode) (cond := cond)
            (post := post) (postSupply := postSupply)
            (loopLabel := loopLabel) (bodyLabel := bodyLabel)
            (postLabel := postLabel) (endLabel := endLabel)
            (fuel := fuel) (bodyState := bodyState)
            (postState := postState) (target := targetAtPost)
            (tokens := tokens) (oracle := oracle)
            (cursor := cursorAfterBody)
            (cursorAfterPost := cursorAfterPost)
            hPost
            (by simpa [bodyCtx, postCtx, bodyCode, postCode] using hLayout)
            (by simpa [bodyCtx, postCtx, bodyCode, postCode] using hResolve)
            (by simpa [bodyCtx, postCtx, bodyCode, postCode] using hExact)
            hPcAtPost hRelAtPost hPostEval
        refine
          ARunResultWithGasOracle.bind_running
            (program :=
              pre ++
                ForLoop.coreCode cond bodyCode postCode loopLabel bodyLabel
                  postLabel endLabel ++ suffix)
            (middle := fun targetAtLoop targetCursorAtLoop =>
              targetCursorAtLoop = cursorAfterPost ∧
                Frame.StateRel postState targetAtLoop tokens ∧
                  targetAtLoop.pc = Assembly.Program.pcAfter pre)
            ?_ ?_
        · simpa [bodyCtx, postCtx, bodyCode, postCode] using hBackToLoop
        · intro targetAtLoop targetCursorAtLoop hAtLoop
          rcases hAtLoop with
            ⟨hCursorAtLoop, hRelAtLoop, hPcAtLoop⟩
          subst targetCursorAtLoop
          simpa [bodyCtx, postCtx, bodyCode, postCode] using
            ih hLayout hResolve hExact hPcAtLoop hRelAtLoop hLoop
    | cont_post_regular hCond hBodyEval hPostEval hLoop =>
      rename_i cursorAfterCond cursorAfterBody cursorAfterPost
        stateAfterCond bodyState postState
      let bodyCtx : CompileContext :=
        { ctx with
          breakLabel? := some endLabel
          continueLabel? := some postLabel }
      let postCtx : CompileContext :=
        { ctx with breakLabel? := none, continueLabel? := none }
      let bodyCode := (Block.compileFromCtx body bodyCtx bodySupply).code
      let postCode := (Block.compileFromCtx post postCtx postSupply).code
      let postPre :=
        ForLoop.postPre pre cond bodyCode loopLabel bodyLabel postLabel
          endLabel
      have hEnterPost :=
        body_cont_enter_post_withGasOracle
          (program := program) (ctx := ctx) (pre := pre)
          (suffix := suffix) (postCode := postCode) (cond := cond)
          (body := body) (bodySupply := bodySupply)
          (loopLabel := loopLabel) (bodyLabel := bodyLabel)
          (postLabel := postLabel) (endLabel := endLabel)
          (fuel := fuel) (source := source)
          (stateAfterCond := stateAfterCond) (bodyState := bodyState)
          (target := target) (tokens := tokens) (oracle := oracle)
          (cursor := cursor) (cursorAfterCond := cursorAfterCond)
          (cursorAfterBody := cursorAfterBody)
          hCondSafe hCondFrame hBody
          (by simpa [bodyCtx, postCtx, bodyCode, postCode] using hLayout)
          (by simpa [bodyCtx, postCtx, bodyCode, postCode] using hResolve)
          (by simpa [bodyCtx, postCtx, bodyCode, postCode] using hExact)
          hPc hRel hCond hBodyEval
      refine
        ARunResultWithGasOracle.bind_running
          (program :=
            pre ++
              ForLoop.coreCode cond bodyCode postCode loopLabel bodyLabel
                postLabel endLabel ++ suffix)
          (middle := fun targetAtPost targetCursorAtPost =>
            targetCursorAtPost = cursorAfterBody ∧
              Frame.StateRel bodyState targetAtPost tokens ∧
                targetAtPost.pc = Assembly.Program.pcAfter postPre)
          ?_ ?_
      · simpa [bodyCtx, postCtx, bodyCode, postCode, postPre] using hEnterPost
      · intro targetAtPost targetCursorAtPost hAtPost
        rcases hAtPost with
          ⟨hCursorAtPost, hRelAtPost, hPcAtPost⟩
        subst targetCursorAtPost
        have hBackToLoop :=
          post_regular_jump_loop_withGasOracle
            (program := program) (ctx := ctx) (pre := pre)
            (suffix := suffix) (bodyCode := bodyCode) (cond := cond)
            (post := post) (postSupply := postSupply)
            (loopLabel := loopLabel) (bodyLabel := bodyLabel)
            (postLabel := postLabel) (endLabel := endLabel)
            (fuel := fuel) (bodyState := bodyState)
            (postState := postState) (target := targetAtPost)
            (tokens := tokens) (oracle := oracle)
            (cursor := cursorAfterBody)
            (cursorAfterPost := cursorAfterPost)
            hPost
            (by simpa [bodyCtx, postCtx, bodyCode, postCode] using hLayout)
            (by simpa [bodyCtx, postCtx, bodyCode, postCode] using hResolve)
            (by simpa [bodyCtx, postCtx, bodyCode, postCode] using hExact)
            hPcAtPost hRelAtPost hPostEval
        refine
          ARunResultWithGasOracle.bind_running
            (program :=
              pre ++
                ForLoop.coreCode cond bodyCode postCode loopLabel bodyLabel
                  postLabel endLabel ++ suffix)
            (middle := fun targetAtLoop targetCursorAtLoop =>
              targetCursorAtLoop = cursorAfterPost ∧
                Frame.StateRel postState targetAtLoop tokens ∧
                  targetAtLoop.pc = Assembly.Program.pcAfter pre)
            ?_ ?_
        · simpa [bodyCtx, postCtx, bodyCode, postCode] using hBackToLoop
        · intro targetAtLoop targetCursorAtLoop hAtLoop
          rcases hAtLoop with
            ⟨hCursorAtLoop, hRelAtLoop, hPcAtLoop⟩
          subst targetCursorAtLoop
          simpa [bodyCtx, postCtx, bodyCode, postCode] using
            ih hLayout hResolve hExact hPcAtLoop hRelAtLoop hLoop
    | regular_post_leave hCond hBodyEval hPostEval =>
      rename_i cursorAfterCond cursorAfterBody stateAfterCond bodyState
        postState
      let bodyCtx : CompileContext :=
        { ctx with
          breakLabel? := some endLabel
          continueLabel? := some postLabel }
      let postCtx : CompileContext :=
        { ctx with breakLabel? := none, continueLabel? := none }
      let bodyCode := (Block.compileFromCtx body bodyCtx bodySupply).code
      let postCode := (Block.compileFromCtx post postCtx postSupply).code
      let postPre :=
        ForLoop.postPre pre cond bodyCode loopLabel bodyLabel postLabel
          endLabel
      have hEnterPost :=
        body_regular_enter_post_withGasOracle
          (program := program) (ctx := ctx) (pre := pre)
          (suffix := suffix) (postCode := postCode) (cond := cond)
          (body := body) (bodySupply := bodySupply)
          (loopLabel := loopLabel) (bodyLabel := bodyLabel)
          (postLabel := postLabel) (endLabel := endLabel)
          (fuel := fuel) (source := source)
          (stateAfterCond := stateAfterCond) (bodyState := bodyState)
          (target := target) (tokens := tokens) (oracle := oracle)
          (cursor := cursor) (cursorAfterCond := cursorAfterCond)
          (cursorAfterBody := cursorAfterBody)
          hCondSafe hCondFrame hBody
          (by simpa [bodyCtx, postCtx, bodyCode, postCode] using hLayout)
          (by simpa [bodyCtx, postCtx, bodyCode, postCode] using hResolve)
          (by simpa [bodyCtx, postCtx, bodyCode, postCode] using hExact)
          hPc hRel hCond hBodyEval
      refine
        ARunResultWithGasOracle.bind_running
          (program :=
            pre ++
              ForLoop.coreCode cond bodyCode postCode loopLabel bodyLabel
                postLabel endLabel ++ suffix)
          (middle := fun targetAtPost targetCursorAtPost =>
            targetCursorAtPost = cursorAfterBody ∧
              Frame.StateRel bodyState targetAtPost tokens ∧
                targetAtPost.pc = Assembly.Program.pcAfter postPre)
          ?_ ?_
      · simpa [bodyCtx, postCtx, bodyCode, postCode, postPre] using hEnterPost
      · intro targetAtPost targetCursorAtPost hAtPost
        rcases hAtPost with
          ⟨hCursorAtPost, hRelAtPost, hPcAtPost⟩
        subst targetCursorAtPost
        simpa [bodyCtx, postCtx, bodyCode, postCode] using
          post_leave_from_entry_withGasOracle
            (program := program) (ctx := ctx) (pre := pre)
            (suffix := suffix) (bodyCode := bodyCode) (cond := cond)
            (post := post) (postSupply := postSupply)
            (loopLabel := loopLabel) (bodyLabel := bodyLabel)
            (postLabel := postLabel) (endLabel := endLabel)
            (fuel := fuel) (bodyState := bodyState)
            (postState := postState) (target := targetAtPost)
            (tokens := tokens) (oracle := oracle)
            (cursor := cursorAfterBody) (cursorFinal := cursorFinal)
            hPost
            (by simpa [bodyCtx, postCtx, bodyCode, postCode] using hLayout)
            (by simpa [bodyCtx, postCtx, bodyCode, postCode] using hResolve)
            (by simpa [bodyCtx, postCtx, bodyCode, postCode] using hExact)
            hPcAtPost hRelAtPost hPostEval
    | cont_post_leave hCond hBodyEval hPostEval =>
      rename_i cursorAfterCond cursorAfterBody stateAfterCond bodyState
        postState
      let bodyCtx : CompileContext :=
        { ctx with
          breakLabel? := some endLabel
          continueLabel? := some postLabel }
      let postCtx : CompileContext :=
        { ctx with breakLabel? := none, continueLabel? := none }
      let bodyCode := (Block.compileFromCtx body bodyCtx bodySupply).code
      let postCode := (Block.compileFromCtx post postCtx postSupply).code
      let postPre :=
        ForLoop.postPre pre cond bodyCode loopLabel bodyLabel postLabel
          endLabel
      have hEnterPost :=
        body_cont_enter_post_withGasOracle
          (program := program) (ctx := ctx) (pre := pre)
          (suffix := suffix) (postCode := postCode) (cond := cond)
          (body := body) (bodySupply := bodySupply)
          (loopLabel := loopLabel) (bodyLabel := bodyLabel)
          (postLabel := postLabel) (endLabel := endLabel)
          (fuel := fuel) (source := source)
          (stateAfterCond := stateAfterCond) (bodyState := bodyState)
          (target := target) (tokens := tokens) (oracle := oracle)
          (cursor := cursor) (cursorAfterCond := cursorAfterCond)
          (cursorAfterBody := cursorAfterBody)
          hCondSafe hCondFrame hBody
          (by simpa [bodyCtx, postCtx, bodyCode, postCode] using hLayout)
          (by simpa [bodyCtx, postCtx, bodyCode, postCode] using hResolve)
          (by simpa [bodyCtx, postCtx, bodyCode, postCode] using hExact)
          hPc hRel hCond hBodyEval
      refine
        ARunResultWithGasOracle.bind_running
          (program :=
            pre ++
              ForLoop.coreCode cond bodyCode postCode loopLabel bodyLabel
                postLabel endLabel ++ suffix)
          (middle := fun targetAtPost targetCursorAtPost =>
            targetCursorAtPost = cursorAfterBody ∧
              Frame.StateRel bodyState targetAtPost tokens ∧
                targetAtPost.pc = Assembly.Program.pcAfter postPre)
          ?_ ?_
      · simpa [bodyCtx, postCtx, bodyCode, postCode, postPre] using hEnterPost
      · intro targetAtPost targetCursorAtPost hAtPost
        rcases hAtPost with
          ⟨hCursorAtPost, hRelAtPost, hPcAtPost⟩
        subst targetCursorAtPost
        simpa [bodyCtx, postCtx, bodyCode, postCode] using
          post_leave_from_entry_withGasOracle
            (program := program) (ctx := ctx) (pre := pre)
            (suffix := suffix) (bodyCode := bodyCode) (cond := cond)
            (post := post) (postSupply := postSupply)
            (loopLabel := loopLabel) (bodyLabel := bodyLabel)
            (postLabel := postLabel) (endLabel := endLabel)
            (fuel := fuel) (bodyState := bodyState)
            (postState := postState) (target := targetAtPost)
            (tokens := tokens) (oracle := oracle)
            (cursor := cursorAfterBody) (cursorFinal := cursorFinal)
            hPost
            (by simpa [bodyCtx, postCtx, bodyCode, postCode] using hLayout)
            (by simpa [bodyCtx, postCtx, bodyCode, postCode] using hResolve)
            (by simpa [bodyCtx, postCtx, bodyCode, postCode] using hExact)
            hPcAtPost hRelAtPost hPostEval
    | regular_post_halt hCond hBodyEval hPostEval =>
      rename_i cursorAfterCond cursorAfterBody stateAfterCond bodyState
        postState kind
      let bodyCtx : CompileContext :=
        { ctx with
          breakLabel? := some endLabel
          continueLabel? := some postLabel }
      let postCtx : CompileContext :=
        { ctx with breakLabel? := none, continueLabel? := none }
      let bodyCode := (Block.compileFromCtx body bodyCtx bodySupply).code
      let postCode := (Block.compileFromCtx post postCtx postSupply).code
      let postPre :=
        ForLoop.postPre pre cond bodyCode loopLabel bodyLabel postLabel
          endLabel
      have hEnterPost :=
        body_regular_enter_post_withGasOracle
          (program := program) (ctx := ctx) (pre := pre)
          (suffix := suffix) (postCode := postCode) (cond := cond)
          (body := body) (bodySupply := bodySupply)
          (loopLabel := loopLabel) (bodyLabel := bodyLabel)
          (postLabel := postLabel) (endLabel := endLabel)
          (fuel := fuel) (source := source)
          (stateAfterCond := stateAfterCond) (bodyState := bodyState)
          (target := target) (tokens := tokens) (oracle := oracle)
          (cursor := cursor) (cursorAfterCond := cursorAfterCond)
          (cursorAfterBody := cursorAfterBody)
          hCondSafe hCondFrame hBody
          (by simpa [bodyCtx, postCtx, bodyCode, postCode] using hLayout)
          (by simpa [bodyCtx, postCtx, bodyCode, postCode] using hResolve)
          (by simpa [bodyCtx, postCtx, bodyCode, postCode] using hExact)
          hPc hRel hCond hBodyEval
      refine
        ARunResultWithGasOracle.bind_running
          (program :=
            pre ++
              ForLoop.coreCode cond bodyCode postCode loopLabel bodyLabel
                postLabel endLabel ++ suffix)
          (middle := fun targetAtPost targetCursorAtPost =>
            targetCursorAtPost = cursorAfterBody ∧
              Frame.StateRel bodyState targetAtPost tokens ∧
                targetAtPost.pc = Assembly.Program.pcAfter postPre)
          ?_ ?_
      · simpa [bodyCtx, postCtx, bodyCode, postCode, postPre] using hEnterPost
      · intro targetAtPost targetCursorAtPost hAtPost
        rcases hAtPost with
          ⟨hCursorAtPost, hRelAtPost, hPcAtPost⟩
        subst targetCursorAtPost
        simpa [bodyCtx, postCtx, bodyCode, postCode] using
          post_halt_from_entry_withGasOracle
            (program := program) (ctx := ctx) (pre := pre)
            (suffix := suffix) (bodyCode := bodyCode) (cond := cond)
            (post := post) (postSupply := postSupply)
            (loopLabel := loopLabel) (bodyLabel := bodyLabel)
            (postLabel := postLabel) (endLabel := endLabel)
            (fuel := fuel) (bodyState := bodyState)
            (postState := postState) (target := targetAtPost)
            (tokens := tokens) (kind := kind) (oracle := oracle)
            (cursor := cursorAfterBody) (cursorFinal := cursorFinal)
            hPost
            (by simpa [bodyCtx, postCtx, bodyCode, postCode] using hLayout)
            (by simpa [bodyCtx, postCtx, bodyCode, postCode] using hResolve)
            (by simpa [bodyCtx, postCtx, bodyCode, postCode] using hExact)
            hPcAtPost hRelAtPost hPostEval
    | cont_post_halt hCond hBodyEval hPostEval =>
      rename_i cursorAfterCond cursorAfterBody stateAfterCond bodyState
        postState kind
      let bodyCtx : CompileContext :=
        { ctx with
          breakLabel? := some endLabel
          continueLabel? := some postLabel }
      let postCtx : CompileContext :=
        { ctx with breakLabel? := none, continueLabel? := none }
      let bodyCode := (Block.compileFromCtx body bodyCtx bodySupply).code
      let postCode := (Block.compileFromCtx post postCtx postSupply).code
      let postPre :=
        ForLoop.postPre pre cond bodyCode loopLabel bodyLabel postLabel
          endLabel
      have hEnterPost :=
        body_cont_enter_post_withGasOracle
          (program := program) (ctx := ctx) (pre := pre)
          (suffix := suffix) (postCode := postCode) (cond := cond)
          (body := body) (bodySupply := bodySupply)
          (loopLabel := loopLabel) (bodyLabel := bodyLabel)
          (postLabel := postLabel) (endLabel := endLabel)
          (fuel := fuel) (source := source)
          (stateAfterCond := stateAfterCond) (bodyState := bodyState)
          (target := target) (tokens := tokens) (oracle := oracle)
          (cursor := cursor) (cursorAfterCond := cursorAfterCond)
          (cursorAfterBody := cursorAfterBody)
          hCondSafe hCondFrame hBody
          (by simpa [bodyCtx, postCtx, bodyCode, postCode] using hLayout)
          (by simpa [bodyCtx, postCtx, bodyCode, postCode] using hResolve)
          (by simpa [bodyCtx, postCtx, bodyCode, postCode] using hExact)
          hPc hRel hCond hBodyEval
      refine
        ARunResultWithGasOracle.bind_running
          (program :=
            pre ++
              ForLoop.coreCode cond bodyCode postCode loopLabel bodyLabel
                postLabel endLabel ++ suffix)
          (middle := fun targetAtPost targetCursorAtPost =>
            targetCursorAtPost = cursorAfterBody ∧
              Frame.StateRel bodyState targetAtPost tokens ∧
                targetAtPost.pc = Assembly.Program.pcAfter postPre)
          ?_ ?_
      · simpa [bodyCtx, postCtx, bodyCode, postCode, postPre] using hEnterPost
      · intro targetAtPost targetCursorAtPost hAtPost
        rcases hAtPost with
          ⟨hCursorAtPost, hRelAtPost, hPcAtPost⟩
        subst targetCursorAtPost
        simpa [bodyCtx, postCtx, bodyCode, postCode] using
          post_halt_from_entry_withGasOracle
            (program := program) (ctx := ctx) (pre := pre)
            (suffix := suffix) (bodyCode := bodyCode) (cond := cond)
            (post := post) (postSupply := postSupply)
            (loopLabel := loopLabel) (bodyLabel := bodyLabel)
            (postLabel := postLabel) (endLabel := endLabel)
            (fuel := fuel) (bodyState := bodyState)
            (postState := postState) (target := targetAtPost)
            (tokens := tokens) (kind := kind) (oracle := oracle)
            (cursor := cursorAfterBody) (cursorFinal := cursorFinal)
            hPost
            (by simpa [bodyCtx, postCtx, bodyCode, postCode] using hLayout)
            (by simpa [bodyCtx, postCtx, bodyCode, postCode] using hResolve)
            (by simpa [bodyCtx, postCtx, bodyCode, postCode] using hExact)
            hPcAtPost hRelAtPost hPostEval

end ForLoopPreservation

namespace ProcedureLayoutPreservation

theorem for_false_case_in_programLayout_withGasOracle {program : Program}
    {layout :
      _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.ProgramLayout
        program}
    {ctx : CompileContext} {cond : Code}
    {bodyCode postCode : Assembly.Program}
    {loopLabel bodyLabel postLabel endLabel : Assembly.Label}
    {source stateAfterCond : RunState} {target : EVMState}
    {tokens : List Word} {oracle : GasOracle}
    {cursor cursorAfterCond : Nat}
    (hCondSafe : Code.RunnerSafeWithGasOracle cond)
    (hCondFrame : Code.FrameSafeWithGasOracle cond)
    (segment :
      CodeSegment layout.asm
        (ForLoop.coreCode cond bodyCode postCode loopLabel bodyLabel postLabel
          endLabel))
    (hPc : target.pc = segment.startPc)
    (hRel : Frame.StateRel source target tokens)
    (hCond :
      Code.runConditionStateWithGasOracle cond oracle cursor source =
        .ok (stateAfterCond, false, cursorAfterCond)) :
    ARunResultWithGasOracle layout.asm oracle cursor target
      (fun result targetCursorFinal =>
        targetCursorFinal = cursorAfterCond ∧
          CompiledOutcomeRel layout.asm ctx segment.fallthroughPc
            (Outcome.regular stateAfterCond) result tokens) := by
  let pre := segment.pre
  let suffix := segment.post
  let coreCode :=
    ForLoop.coreCode cond bodyCode postCode loopLabel bodyLabel postLabel
      endLabel
  have hLocalAsm : pre ++ coreCode ++ suffix = layout.asm := by
    simpa [pre, suffix, coreCode] using segment.hAsm.symm
  have hExactLocal : ExactLabels (pre ++ coreCode ++ suffix) :=
    ExactLabels.cast_asm hLocalAsm.symm layout.exactLabels
  have hLayout :
      ForLoop.Layout pre suffix cond bodyCode postCode loopLabel bodyLabel
        postLabel endLabel :=
    ForLoop.Layout.of_fits_exact
      (pre := pre) (suffix := suffix) (cond := cond)
      (bodyCode := bodyCode) (postCode := postCode)
      (loopLabel := loopLabel) (bodyLabel := bodyLabel)
      (postLabel := postLabel) (endLabel := endLabel)
      (by simpa [coreCode] using segment.hFits)
      (by simpa [coreCode] using hExactLocal)
  have hRunLocal :=
    ForLoopPreservation.false_case_withGasOracle
      (ctx := ctx) (pre := pre) (suffix := suffix)
      (bodyCode := bodyCode) (postCode := postCode) (cond := cond)
      (loopLabel := loopLabel) (bodyLabel := bodyLabel)
      (postLabel := postLabel) (endLabel := endLabel)
      (source := source) (stateAfterCond := stateAfterCond)
      (target := target) (tokens := tokens) (oracle := oracle)
      (cursor := cursor) (cursorAfterCond := cursorAfterCond)
      hCondSafe hCondFrame hLayout
      (by simpa [pre, CodeSegment.startPc] using hPc)
      hRel hCond
  exact
    ARunResultWithGasOracle.cast_program_mono hLocalAsm hRunLocal
      (by
        intro result targetCursorFinal hResult
        rcases hResult with ⟨hCursorFinal, hCompiled⟩
        cases result with
        | halted halt =>
            cases hCompiled
        | running targetFinal =>
            exact
              ⟨ hCursorFinal
              , by
                  simpa [pre, suffix, coreCode, CodeSegment.fallthroughPc,
                    CompiledOutcomeRel, Outcome.regular, List.append_assoc]
                    using hCompiled
              ⟩)

theorem for_enter_body_result_ctx_in_programLayout_withGasOracle
    {program : Program}
    {layout :
      _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.ProgramLayout
        program}
    {ctx : CompileContext} {cond : Code} {body : Block}
    {bodySupply : LabelSupply} {postCode : Assembly.Program}
    {loopLabel bodyLabel postLabel endLabel : Assembly.Label}
    {fuel : Nat}
    {source stateAfterCond : RunState} {bodyOutcome : Outcome}
    {target : EVMState} {tokens : List Word}
    {oracle : GasOracle} {cursor cursorAfterCond cursorFinal : Nat}
    (hCondSafe : Code.RunnerSafeWithGasOracle cond)
    (hCondFrame : Code.FrameSafeWithGasOracle cond)
    (hBody :
      BlockPreservesInProgramLayoutWithGasOracleAtFuel layout fuel
        { ctx with
          breakLabel? := some endLabel
          continueLabel? := some postLabel }
        bodySupply body)
    (segment :
      CodeSegment layout.asm
        (ForLoop.coreCode cond
          (Block.compileFromCtx body
            { ctx with
              breakLabel? := some endLabel
              continueLabel? := some postLabel }
            bodySupply).code
          postCode loopLabel bodyLabel postLabel endLabel))
    (hProgramWF : program.WF)
    (hCtxProcs : ctx.procs = program.procs)
    (hBodyCalls :
      CallsIncluded
        (Block.compileFromCtx body
          { ctx with
            breakLabel? := some endLabel
            continueLabel? := some postLabel }
          bodySupply).calls layout.sites)
    (hResolve : ContextLabelsResolve layout.asm ctx)
    (hPc : target.pc = segment.startPc)
    (hRel : Frame.StateRel source target tokens)
    (hCond :
      Code.runConditionStateWithGasOracle cond oracle cursor source =
        .ok (stateAfterCond, true, cursorAfterCond))
    (hBodyEval :
      Block.EvalWithGasOracle program oracle fuel body cursorAfterCond
        stateAfterCond bodyOutcome cursorFinal) :
    ARunResultWithGasOracle layout.asm oracle cursor target
      (fun result targetCursorFinal =>
        targetCursorFinal = cursorFinal ∧
          CompiledOutcomeRel layout.asm
            { ctx with
              breakLabel? := some endLabel
              continueLabel? := some postLabel }
            (Assembly.Program.pcAfter
              (ForLoop.postLabelPre segment.pre cond
                (Block.compileFromCtx body
                  { ctx with
                    breakLabel? := some endLabel
                    continueLabel? := some postLabel }
                  bodySupply).code
                loopLabel bodyLabel endLabel))
            bodyOutcome result tokens) := by
  let pre := segment.pre
  let suffix := segment.post
  let bodyCtx : CompileContext :=
    { ctx with
      breakLabel? := some endLabel
      continueLabel? := some postLabel }
  let bodyCode := (Block.compileFromCtx body bodyCtx bodySupply).code
  let coreCode :=
    ForLoop.coreCode cond bodyCode postCode loopLabel bodyLabel postLabel
      endLabel
  let bodyPre := ForLoop.bodyPre pre cond loopLabel bodyLabel endLabel
  have hLocalAsm : pre ++ coreCode ++ suffix = layout.asm := by
    simpa [pre, suffix, bodyCtx, bodyCode, coreCode] using segment.hAsm.symm
  have hExactLocal : ExactLabels (pre ++ coreCode ++ suffix) :=
    ExactLabels.cast_asm hLocalAsm.symm layout.exactLabels
  have hLayout :
      ForLoop.Layout pre suffix cond bodyCode postCode loopLabel bodyLabel
        postLabel endLabel :=
    ForLoop.Layout.of_fits_exact
      (pre := pre) (suffix := suffix) (cond := cond)
      (bodyCode := bodyCode) (postCode := postCode)
      (loopLabel := loopLabel) (bodyLabel := bodyLabel)
      (postLabel := postLabel) (endLabel := endLabel)
      (by simpa [bodyCtx, bodyCode, coreCode] using segment.hFits)
      (by simpa [bodyCtx, bodyCode, coreCode] using hExactLocal)
  have hEnterLocal :=
    ForLoopPreservation.enter_body_withGasOracle
      (pre := pre) (suffix := suffix) (bodyCode := bodyCode)
      (postCode := postCode) (cond := cond) (loopLabel := loopLabel)
      (bodyLabel := bodyLabel) (postLabel := postLabel)
      (endLabel := endLabel) (source := source)
      (stateAfterCond := stateAfterCond) (target := target)
      (tokens := tokens) (oracle := oracle) (cursor := cursor)
      (cursorAfterCond := cursorAfterCond)
      hCondSafe hCondFrame hLayout
      (by simpa [pre, CodeSegment.startPc] using hPc)
      hRel hCond
  have hEnter :
      ARunResultWithGasOracle layout.asm oracle cursor target
        (fun result targetCursorAtBody =>
          match result with
          | .running targetAtBody =>
              targetCursorAtBody = cursorAfterCond ∧
                Frame.StateRel stateAfterCond targetAtBody tokens ∧
                  targetAtBody.pc = Assembly.Program.pcAfter bodyPre
          | .halted _ => False) :=
    ARunResultWithGasOracle.cast_program_mono hLocalAsm hEnterLocal
      (by
        intro result targetCursorAtBody hResult
        cases result with
        | halted halt =>
            cases hResult
        | running targetAtBody =>
            simpa [bodyCtx, bodyCode, bodyPre, ForLoop.bodyPre]
              using hResult)
  refine
    ARunResultWithGasOracle.bind_running
      (program := layout.asm) (oracle := oracle) (cursor := cursor)
      (state := target)
      (middle := fun targetAtBody targetCursorAtBody =>
        targetCursorAtBody = cursorAfterCond ∧
          Frame.StateRel stateAfterCond targetAtBody tokens ∧
            targetAtBody.pc = Assembly.Program.pcAfter bodyPre)
      hEnter ?_
  intro targetAtBody targetCursorAtBody hAtBody
  rcases hAtBody with ⟨hTargetCursorAtBody, hRelAtBody, hPcAtBody⟩
  subst targetCursorAtBody
  have hBodyCtxResolve : ContextLabelsResolve layout.asm bodyCtx := by
    apply ContextLabelsResolve.with_break_continue
      (ctx := ctx) (breakLabel := endLabel) (continueLabel := postLabel)
    · exact hResolve
    · exact
        ⟨Assembly.Program.byteLength
            (ForLoop.endLabelPre pre cond bodyCode postCode loopLabel bodyLabel
              postLabel endLabel),
          by
            simpa [bodyCtx, bodyCode, coreCode, ← hLocalAsm]
              using hLayout.endLabelPc⟩
    · exact
        ⟨Assembly.Program.byteLength
            (ForLoop.postLabelPre pre cond bodyCode loopLabel bodyLabel
              endLabel),
          by
            simpa [bodyCtx, bodyCode, coreCode, ← hLocalAsm]
              using hLayout.postLabelPc⟩
  let bodySeg : CodeSegment layout.asm bodyCode :=
    { pre := bodyPre
      post :=
        [Assembly.Instr.label postLabel] ++ postCode ++
          [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel] ++
          suffix
      hAsm := by
        simpa [pre, suffix, bodyCtx, bodyCode, coreCode, bodyPre,
          ForLoop.coreCode, ForLoop.afterLoopLabel,
          ForLoop.afterCondJumpi, ForLoop.bodyLabelPre, ForLoop.bodyPre,
          List.append_assoc] using segment.hAsm
      hFits := by
        simpa [bodyCtx, bodyCode] using hLayout.fitBody }
  have hBodyRun :=
    hBody (source := stateAfterCond) (outcome := bodyOutcome)
      (target := targetAtBody) (tokens := tokens) (oracle := oracle)
      (cursor := cursorAfterCond) (cursorFinal := cursorFinal)
      hProgramWF
      (by simpa [bodyCtx] using hCtxProcs)
      (by simpa [bodyCtx, bodyCode] using hBodyCalls)
      hBodyCtxResolve bodySeg
      (by simpa [bodySeg, bodyPre, CodeSegment.startPc] using hPcAtBody)
      hRelAtBody hBodyEval
  exact
    ARunResultWithGasOracle.mono hBodyRun
      (by
        intro result targetCursorFinal hResult
        rcases hResult with ⟨hCursorFinal, hCompiled⟩
        exact
          ⟨ hCursorFinal
          , by
              simpa [bodySeg, bodyCtx, bodyCode, bodyPre,
                CodeSegment.fallthroughPc, ForLoop.postLabelPre,
                List.append_assoc] using hCompiled
          ⟩)

theorem for_body_brk_case_in_programLayout_withGasOracle {program : Program}
    {layout :
      _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.ProgramLayout
        program}
    {ctx : CompileContext} {cond : Code} {body : Block}
    {bodySupply : LabelSupply} {postCode : Assembly.Program}
    {loopLabel bodyLabel postLabel endLabel : Assembly.Label}
    {fuel : Nat}
    {source stateAfterCond bodyState : RunState}
    {target : EVMState} {tokens : List Word}
    {oracle : GasOracle} {cursor cursorAfterCond cursorFinal : Nat}
    (hCondSafe : Code.RunnerSafeWithGasOracle cond)
    (hCondFrame : Code.FrameSafeWithGasOracle cond)
    (hBody :
      BlockPreservesInProgramLayoutWithGasOracleAtFuel layout fuel
        { ctx with
          breakLabel? := some endLabel
          continueLabel? := some postLabel }
        bodySupply body)
    (segment :
      CodeSegment layout.asm
        (ForLoop.coreCode cond
          (Block.compileFromCtx body
            { ctx with
              breakLabel? := some endLabel
              continueLabel? := some postLabel }
            bodySupply).code
          postCode loopLabel bodyLabel postLabel endLabel))
    (hProgramWF : program.WF)
    (hCtxProcs : ctx.procs = program.procs)
    (hBodyCalls :
      CallsIncluded
        (Block.compileFromCtx body
          { ctx with
            breakLabel? := some endLabel
            continueLabel? := some postLabel }
          bodySupply).calls layout.sites)
    (hResolve : ContextLabelsResolve layout.asm ctx)
    (hPc : target.pc = segment.startPc)
    (hRel : Frame.StateRel source target tokens)
    (hCond :
      Code.runConditionStateWithGasOracle cond oracle cursor source =
        .ok (stateAfterCond, true, cursorAfterCond))
    (hBodyEval :
      Block.EvalWithGasOracle program oracle fuel body cursorAfterCond
        stateAfterCond (Outcome.brk bodyState) cursorFinal) :
    ARunResultWithGasOracle layout.asm oracle cursor target
      (fun result targetCursorFinal =>
        targetCursorFinal = cursorFinal ∧
          CompiledOutcomeRel layout.asm ctx segment.fallthroughPc
            (Outcome.regular bodyState) result tokens) := by
  let pre := segment.pre
  let suffix := segment.post
  let bodyCtx : CompileContext :=
    { ctx with
      breakLabel? := some endLabel
      continueLabel? := some postLabel }
  let bodyCode := (Block.compileFromCtx body bodyCtx bodySupply).code
  let coreCode :=
    ForLoop.coreCode cond bodyCode postCode loopLabel bodyLabel postLabel
      endLabel
  let endLabelPre :=
    ForLoop.endLabelPre pre cond bodyCode postCode loopLabel bodyLabel
      postLabel endLabel
  have hLocalAsm : pre ++ coreCode ++ suffix = layout.asm := by
    simpa [pre, suffix, bodyCtx, bodyCode, coreCode] using segment.hAsm.symm
  have hExactLocal : ExactLabels (pre ++ coreCode ++ suffix) :=
    ExactLabels.cast_asm hLocalAsm.symm layout.exactLabels
  have hLayout :
      ForLoop.Layout pre suffix cond bodyCode postCode loopLabel bodyLabel
        postLabel endLabel :=
    ForLoop.Layout.of_fits_exact
      (pre := pre) (suffix := suffix) (cond := cond)
      (bodyCode := bodyCode) (postCode := postCode)
      (loopLabel := loopLabel) (bodyLabel := bodyLabel)
      (postLabel := postLabel) (endLabel := endLabel)
      (by simpa [bodyCtx, bodyCode, coreCode] using segment.hFits)
      (by simpa [bodyCtx, bodyCode, coreCode] using hExactLocal)
  have hEndLabelPc :
      Assembly.Program.labelPc layout.asm endLabel =
        some (Assembly.Program.byteLength endLabelPre) := by
    simpa [bodyCtx, bodyCode, coreCode, endLabelPre, ← hLocalAsm]
      using hLayout.endLabelPc
  have hEnter :=
    for_enter_body_result_ctx_in_programLayout_withGasOracle
      (program := program) (layout := layout) (ctx := ctx)
      (cond := cond) (body := body) (bodySupply := bodySupply)
      (postCode := postCode) (loopLabel := loopLabel)
      (bodyLabel := bodyLabel) (postLabel := postLabel)
      (endLabel := endLabel) (source := source)
      (stateAfterCond := stateAfterCond)
      (bodyOutcome := Outcome.brk bodyState) (target := target)
      (tokens := tokens) (oracle := oracle) (cursor := cursor)
      (cursorAfterCond := cursorAfterCond) (cursorFinal := cursorFinal)
      hCondSafe hCondFrame hBody segment hProgramWF hCtxProcs hBodyCalls
      hResolve hPc hRel hCond hBodyEval
  have hAtEnd :
      ARunResultWithGasOracle layout.asm oracle cursor target
        (fun result targetCursorAtEnd =>
          match result with
          | .running targetAtEnd =>
              targetCursorAtEnd = cursorFinal ∧
                Frame.StateRel bodyState targetAtEnd tokens ∧
                  targetAtEnd.pc = Assembly.Program.pcAfter endLabelPre
          | .halted _ => False) := by
    exact
      ARunResultWithGasOracle.mono hEnter
        (by
          intro result targetCursorAtEnd hResult
          rcases hResult with ⟨hCursorAtEnd, hCompiled⟩
          cases result with
          | halted halt =>
              cases hCompiled
          | running targetAtEnd =>
              rcases hCompiled with
                ⟨label, dest, hBreak, hLabel, hRelEnd, hPcEnd⟩
              simp at hBreak
              cases hBreak
              have hDest : dest = Assembly.Program.byteLength endLabelPre := by
                rw [hLabel] at hEndLabelPc
                cases hEndLabelPc
                rfl
              exact
                ⟨hCursorAtEnd, hRelEnd,
                  by simpa [endLabelPre, hDest] using hPcEnd⟩)
  refine
    ARunResultWithGasOracle.bind_running
      (program := layout.asm) (oracle := oracle) (cursor := cursor)
      (state := target)
      (middle := fun targetAtEnd targetCursorAtEnd =>
        targetCursorAtEnd = cursorFinal ∧
          Frame.StateRel bodyState targetAtEnd tokens ∧
            targetAtEnd.pc = Assembly.Program.pcAfter endLabelPre)
      hAtEnd ?_
  intro targetAtEnd targetCursorAtEnd hAtEnd'
  rcases hAtEnd' with ⟨hTargetCursorAtEnd, hRelAtEnd, hPcAtEnd⟩
  subst targetCursorAtEnd
  have hEndRun :=
    FrameStateRel.label_runResult_at_withGasOracle
      (label := endLabel) (pre := endLabelPre) (post := suffix)
      (oracle := oracle) (cursor := cursorFinal)
      hLayout.fitEndLabel hPcAtEnd hRelAtEnd
  have hEndRunLocal :
      ARunResultWithGasOracle
        (endLabelPre ++ [Assembly.Instr.label endLabel] ++ suffix)
        oracle cursorFinal targetAtEnd
        (fun result targetCursorFinal =>
          targetCursorFinal = cursorFinal ∧
            CompiledOutcomeRel layout.asm ctx segment.fallthroughPc
              (Outcome.regular bodyState) result tokens) := by
    exact
      ARunResultWithGasOracle.mono hEndRun
        (by
          intro result targetCursorFinal hResult
          cases result with
          | halted halt =>
              cases hResult
          | running targetFinal =>
              rcases hResult with ⟨hCursorFinal, hRelFinal, hPcFinal⟩
              exact
                ⟨ hCursorFinal
                , by
                    simpa [pre, suffix, bodyCtx, bodyCode, coreCode,
                      endLabelPre, CodeSegment.fallthroughPc,
                      CompiledOutcomeRel, Outcome.regular, ForLoop.coreCode,
                      ForLoop.afterLoopLabel, ForLoop.afterCondJumpi,
                      ForLoop.bodyLabelPre, ForLoop.bodyPre,
                      ForLoop.postLabelPre, ForLoop.postPre,
                      ForLoop.endLabelPre, List.append_assoc] using
                      And.intro hRelFinal hPcFinal
                ⟩)
  have hEndAsm :
      endLabelPre ++ [Assembly.Instr.label endLabel] ++ suffix =
        layout.asm := by
    simpa [pre, suffix, bodyCtx, bodyCode, coreCode, endLabelPre,
      ForLoop.coreCode, ForLoop.afterLoopLabel, ForLoop.afterCondJumpi,
      ForLoop.bodyLabelPre, ForLoop.bodyPre, ForLoop.postLabelPre,
      ForLoop.postPre, ForLoop.endLabelPre, List.append_assoc]
      using hLocalAsm
  exact ARunResultWithGasOracle.cast_program hEndAsm hEndRunLocal

theorem for_body_leave_case_in_programLayout_withGasOracle
    {program : Program}
    {layout :
      _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.ProgramLayout
        program}
    {ctx : CompileContext} {cond : Code} {body : Block}
    {bodySupply : LabelSupply} {postCode : Assembly.Program}
    {loopLabel bodyLabel postLabel endLabel : Assembly.Label}
    {fuel : Nat}
    {source stateAfterCond bodyState : RunState}
    {target : EVMState} {tokens : List Word}
    {oracle : GasOracle} {cursor cursorAfterCond cursorFinal : Nat}
    (hCondSafe : Code.RunnerSafeWithGasOracle cond)
    (hCondFrame : Code.FrameSafeWithGasOracle cond)
    (hBody :
      BlockPreservesInProgramLayoutWithGasOracleAtFuel layout fuel
        { ctx with
          breakLabel? := some endLabel
          continueLabel? := some postLabel }
        bodySupply body)
    (segment :
      CodeSegment layout.asm
        (ForLoop.coreCode cond
          (Block.compileFromCtx body
            { ctx with
              breakLabel? := some endLabel
              continueLabel? := some postLabel }
            bodySupply).code
          postCode loopLabel bodyLabel postLabel endLabel))
    (hProgramWF : program.WF)
    (hCtxProcs : ctx.procs = program.procs)
    (hBodyCalls :
      CallsIncluded
        (Block.compileFromCtx body
          { ctx with
            breakLabel? := some endLabel
            continueLabel? := some postLabel }
          bodySupply).calls layout.sites)
    (hResolve : ContextLabelsResolve layout.asm ctx)
    (hPc : target.pc = segment.startPc)
    (hRel : Frame.StateRel source target tokens)
    (hCond :
      Code.runConditionStateWithGasOracle cond oracle cursor source =
        .ok (stateAfterCond, true, cursorAfterCond))
    (hBodyEval :
      Block.EvalWithGasOracle program oracle fuel body cursorAfterCond
        stateAfterCond (Outcome.leave bodyState) cursorFinal) :
    ARunResultWithGasOracle layout.asm oracle cursor target
      (fun result targetCursorFinal =>
        targetCursorFinal = cursorFinal ∧
          CompiledOutcomeRel layout.asm ctx segment.fallthroughPc
            (Outcome.leave bodyState) result tokens) := by
  let bodyCtx : CompileContext :=
    { ctx with
      breakLabel? := some endLabel
      continueLabel? := some postLabel }
  have hEnter :=
    for_enter_body_result_ctx_in_programLayout_withGasOracle
      (program := program) (layout := layout) (ctx := ctx)
      (cond := cond) (body := body) (bodySupply := bodySupply)
      (postCode := postCode) (loopLabel := loopLabel)
      (bodyLabel := bodyLabel) (postLabel := postLabel)
      (endLabel := endLabel) (source := source)
      (stateAfterCond := stateAfterCond)
      (bodyOutcome := Outcome.leave bodyState) (target := target)
      (tokens := tokens) (oracle := oracle) (cursor := cursor)
      (cursorAfterCond := cursorAfterCond) (cursorFinal := cursorFinal)
      hCondSafe hCondFrame hBody segment hProgramWF hCtxProcs hBodyCalls
      hResolve hPc hRel hCond hBodyEval
  exact
    ARunResultWithGasOracle.mono hEnter
      (by
        intro result targetCursorFinal hResult
        rcases hResult with ⟨hCursorFinal, hCompiled⟩
        cases result with
        | running target' =>
            exact
              ⟨hCursorFinal, by
                simpa [bodyCtx, CompiledOutcomeRel, Outcome.leave] using
                  hCompiled⟩
        | halted halt =>
            cases hCompiled)

theorem for_body_halt_case_in_programLayout_withGasOracle {program : Program}
    {layout :
      _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.ProgramLayout
        program}
    {ctx : CompileContext} {cond : Code} {body : Block}
    {bodySupply : LabelSupply} {postCode : Assembly.Program}
    {loopLabel bodyLabel postLabel endLabel : Assembly.Label}
    {fuel : Nat}
    {source stateAfterCond bodyState : RunState} {kind : Assembly.HaltKind}
    {target : EVMState} {tokens : List Word}
    {oracle : GasOracle} {cursor cursorAfterCond cursorFinal : Nat}
    (hCondSafe : Code.RunnerSafeWithGasOracle cond)
    (hCondFrame : Code.FrameSafeWithGasOracle cond)
    (hBody :
      BlockPreservesInProgramLayoutWithGasOracleAtFuel layout fuel
        { ctx with
          breakLabel? := some endLabel
          continueLabel? := some postLabel }
        bodySupply body)
    (segment :
      CodeSegment layout.asm
        (ForLoop.coreCode cond
          (Block.compileFromCtx body
            { ctx with
              breakLabel? := some endLabel
              continueLabel? := some postLabel }
            bodySupply).code
          postCode loopLabel bodyLabel postLabel endLabel))
    (hProgramWF : program.WF)
    (hCtxProcs : ctx.procs = program.procs)
    (hBodyCalls :
      CallsIncluded
        (Block.compileFromCtx body
          { ctx with
            breakLabel? := some endLabel
            continueLabel? := some postLabel }
          bodySupply).calls layout.sites)
    (hResolve : ContextLabelsResolve layout.asm ctx)
    (hPc : target.pc = segment.startPc)
    (hRel : Frame.StateRel source target tokens)
    (hCond :
      Code.runConditionStateWithGasOracle cond oracle cursor source =
        .ok (stateAfterCond, true, cursorAfterCond))
    (hBodyEval :
      Block.EvalWithGasOracle program oracle fuel body cursorAfterCond
        stateAfterCond (Outcome.halt kind bodyState) cursorFinal) :
    ARunResultWithGasOracle layout.asm oracle cursor target
      (fun result targetCursorFinal =>
        targetCursorFinal = cursorFinal ∧
          CompiledOutcomeRel layout.asm ctx segment.fallthroughPc
            (Outcome.halt kind bodyState) result tokens) := by
  let bodyCtx : CompileContext :=
    { ctx with
      breakLabel? := some endLabel
      continueLabel? := some postLabel }
  have hEnter :=
    for_enter_body_result_ctx_in_programLayout_withGasOracle
      (program := program) (layout := layout) (ctx := ctx)
      (cond := cond) (body := body) (bodySupply := bodySupply)
      (postCode := postCode) (loopLabel := loopLabel)
      (bodyLabel := bodyLabel) (postLabel := postLabel)
      (endLabel := endLabel) (source := source)
      (stateAfterCond := stateAfterCond)
      (bodyOutcome := Outcome.halt kind bodyState) (target := target)
      (tokens := tokens) (oracle := oracle) (cursor := cursor)
      (cursorAfterCond := cursorAfterCond) (cursorFinal := cursorFinal)
      hCondSafe hCondFrame hBody segment hProgramWF hCtxProcs hBodyCalls
      hResolve hPc hRel hCond hBodyEval
  exact
    ARunResultWithGasOracle.mono hEnter
      (by
        intro result targetCursorFinal hResult
        rcases hResult with ⟨hCursorFinal, hCompiled⟩
        cases result with
        | running target' =>
            cases hCompiled
        | halted halt =>
            exact
              ⟨hCursorFinal, by
                simpa [bodyCtx, CompiledOutcomeRel, Outcome.halt] using
                  hCompiled⟩)

theorem for_body_regular_enter_post_in_programLayout_withGasOracle
    {program : Program}
    {layout :
      _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.ProgramLayout
        program}
    {ctx : CompileContext} {cond : Code} {body : Block}
    {bodySupply : LabelSupply} {postCode : Assembly.Program}
    {loopLabel bodyLabel postLabel endLabel : Assembly.Label}
    {fuel : Nat}
    {source stateAfterCond bodyState : RunState}
    {target : EVMState} {tokens : List Word}
    {oracle : GasOracle} {cursor cursorAfterCond cursorAfterBody : Nat}
    (hCondSafe : Code.RunnerSafeWithGasOracle cond)
    (hCondFrame : Code.FrameSafeWithGasOracle cond)
    (hBody :
      BlockPreservesInProgramLayoutWithGasOracleAtFuel layout fuel
        { ctx with
          breakLabel? := some endLabel
          continueLabel? := some postLabel }
        bodySupply body)
    (segment :
      CodeSegment layout.asm
        (ForLoop.coreCode cond
          (Block.compileFromCtx body
            { ctx with
              breakLabel? := some endLabel
              continueLabel? := some postLabel }
            bodySupply).code
          postCode loopLabel bodyLabel postLabel endLabel))
    (hProgramWF : program.WF)
    (hCtxProcs : ctx.procs = program.procs)
    (hBodyCalls :
      CallsIncluded
        (Block.compileFromCtx body
          { ctx with
            breakLabel? := some endLabel
            continueLabel? := some postLabel }
          bodySupply).calls layout.sites)
    (hResolve : ContextLabelsResolve layout.asm ctx)
    (hPc : target.pc = segment.startPc)
    (hRel : Frame.StateRel source target tokens)
    (hCond :
      Code.runConditionStateWithGasOracle cond oracle cursor source =
        .ok (stateAfterCond, true, cursorAfterCond))
    (hBodyEval :
      Block.EvalWithGasOracle program oracle fuel body cursorAfterCond
        stateAfterCond (Outcome.regular bodyState) cursorAfterBody) :
    ARunResultWithGasOracle layout.asm oracle cursor target
      (fun result targetCursorAtPost =>
        match result with
        | .running targetAtPost =>
            targetCursorAtPost = cursorAfterBody ∧
              Frame.StateRel bodyState targetAtPost tokens ∧
                targetAtPost.pc =
                  Assembly.Program.pcAfter
                    (ForLoop.postPre segment.pre cond
                      (Block.compileFromCtx body
                        { ctx with
                          breakLabel? := some endLabel
                          continueLabel? := some postLabel }
                        bodySupply).code
                      loopLabel bodyLabel postLabel endLabel)
        | .halted _ => False) := by
  let pre := segment.pre
  let suffix := segment.post
  let bodyCtx : CompileContext :=
    { ctx with
      breakLabel? := some endLabel
      continueLabel? := some postLabel }
  let bodyCode := (Block.compileFromCtx body bodyCtx bodySupply).code
  let coreCode :=
    ForLoop.coreCode cond bodyCode postCode loopLabel bodyLabel postLabel
      endLabel
  let postLabelPre :=
    ForLoop.postLabelPre pre cond bodyCode loopLabel bodyLabel endLabel
  let postPre :=
    ForLoop.postPre pre cond bodyCode loopLabel bodyLabel postLabel endLabel
  have hLocalAsm : pre ++ coreCode ++ suffix = layout.asm := by
    simpa [pre, suffix, bodyCtx, bodyCode, coreCode] using segment.hAsm.symm
  have hExactLocal : ExactLabels (pre ++ coreCode ++ suffix) :=
    ExactLabels.cast_asm hLocalAsm.symm layout.exactLabels
  have hLayout :
      ForLoop.Layout pre suffix cond bodyCode postCode loopLabel bodyLabel
        postLabel endLabel :=
    ForLoop.Layout.of_fits_exact
      (pre := pre) (suffix := suffix) (cond := cond)
      (bodyCode := bodyCode) (postCode := postCode)
      (loopLabel := loopLabel) (bodyLabel := bodyLabel)
      (postLabel := postLabel) (endLabel := endLabel)
      (by simpa [bodyCtx, bodyCode, coreCode] using segment.hFits)
      (by simpa [bodyCtx, bodyCode, coreCode] using hExactLocal)
  have hEnter :=
    for_enter_body_result_ctx_in_programLayout_withGasOracle
      (program := program) (layout := layout) (ctx := ctx)
      (cond := cond) (body := body) (bodySupply := bodySupply)
      (postCode := postCode) (loopLabel := loopLabel)
      (bodyLabel := bodyLabel) (postLabel := postLabel)
      (endLabel := endLabel) (source := source)
      (stateAfterCond := stateAfterCond)
      (bodyOutcome := Outcome.regular bodyState) (target := target)
      (tokens := tokens) (oracle := oracle) (cursor := cursor)
      (cursorAfterCond := cursorAfterCond) (cursorFinal := cursorAfterBody)
      hCondSafe hCondFrame hBody segment hProgramWF hCtxProcs hBodyCalls
      hResolve hPc hRel hCond hBodyEval
  have hAtPostLabel :
      ARunResultWithGasOracle layout.asm oracle cursor target
        (fun result targetCursorAtPostLabel =>
          match result with
          | .running targetAtPostLabel =>
              targetCursorAtPostLabel = cursorAfterBody ∧
                Frame.StateRel bodyState targetAtPostLabel tokens ∧
                  targetAtPostLabel.pc =
                    Assembly.Program.pcAfter postLabelPre
          | .halted _ => False) := by
    exact
      ARunResultWithGasOracle.mono hEnter
        (by
          intro result targetCursorAtPostLabel hResult
          rcases hResult with ⟨hCursorAtPostLabel, hCompiled⟩
          cases result with
          | halted halt =>
              cases hCompiled
          | running targetAtPostLabel =>
              exact
                ⟨ hCursorAtPostLabel
                , by
                    simpa [bodyCtx, bodyCode, CompiledOutcomeRel,
                      Outcome.regular, postLabelPre, List.append_assoc]
                      using hCompiled
                ⟩)
  refine
    ARunResultWithGasOracle.bind_running
      (program := layout.asm) (oracle := oracle) (cursor := cursor)
      (state := target)
      (middle := fun targetAtPostLabel targetCursorAtPostLabel =>
        targetCursorAtPostLabel = cursorAfterBody ∧
          Frame.StateRel bodyState targetAtPostLabel tokens ∧
            targetAtPostLabel.pc = Assembly.Program.pcAfter postLabelPre)
      hAtPostLabel ?_
  intro targetAtPostLabel targetCursorAtPostLabel hAtPostLabel'
  rcases hAtPostLabel' with
    ⟨hTargetCursorAtPostLabel, hRelAtPostLabel, hPcAtPostLabel⟩
  subst targetCursorAtPostLabel
  have hPostLabelRun :=
    FrameStateRel.label_runResult_at_withGasOracle
      (label := postLabel) (pre := postLabelPre)
      (post :=
        postCode ++
          [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel] ++
          suffix)
      (oracle := oracle) (cursor := cursorAfterBody)
      hLayout.fitPostLabel hPcAtPostLabel hRelAtPostLabel
  have hPostAsm :
      postLabelPre ++ [Assembly.Instr.label postLabel] ++
        (postCode ++
          [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel] ++
          suffix) =
        layout.asm := by
    simpa [pre, suffix, bodyCtx, bodyCode, coreCode, postLabelPre,
      ForLoop.coreCode, ForLoop.afterLoopLabel, ForLoop.afterCondJumpi,
      ForLoop.bodyLabelPre, ForLoop.bodyPre, ForLoop.postLabelPre,
      List.append_assoc] using hLocalAsm
  exact
    ARunResultWithGasOracle.cast_program_mono hPostAsm hPostLabelRun
      (by
        intro result targetCursorAtPost hResult
        cases result with
        | halted halt =>
            cases hResult
        | running targetAtPost =>
            rcases hResult with ⟨hCursorAtPost, hRelAtPost, hPcAtPost⟩
            exact
              ⟨ hCursorAtPost
              , hRelAtPost
              , by
                  simpa [postPre, ForLoop.postPre, postLabelPre,
                    List.append_assoc] using hPcAtPost
              ⟩)

theorem for_body_cont_enter_post_in_programLayout_withGasOracle
    {program : Program}
    {layout :
      _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.ProgramLayout
        program}
    {ctx : CompileContext} {cond : Code} {body : Block}
    {bodySupply : LabelSupply} {postCode : Assembly.Program}
    {loopLabel bodyLabel postLabel endLabel : Assembly.Label}
    {fuel : Nat}
    {source stateAfterCond bodyState : RunState}
    {target : EVMState} {tokens : List Word}
    {oracle : GasOracle} {cursor cursorAfterCond cursorAfterBody : Nat}
    (hCondSafe : Code.RunnerSafeWithGasOracle cond)
    (hCondFrame : Code.FrameSafeWithGasOracle cond)
    (hBody :
      BlockPreservesInProgramLayoutWithGasOracleAtFuel layout fuel
        { ctx with
          breakLabel? := some endLabel
          continueLabel? := some postLabel }
        bodySupply body)
    (segment :
      CodeSegment layout.asm
        (ForLoop.coreCode cond
          (Block.compileFromCtx body
            { ctx with
              breakLabel? := some endLabel
              continueLabel? := some postLabel }
            bodySupply).code
          postCode loopLabel bodyLabel postLabel endLabel))
    (hProgramWF : program.WF)
    (hCtxProcs : ctx.procs = program.procs)
    (hBodyCalls :
      CallsIncluded
        (Block.compileFromCtx body
          { ctx with
            breakLabel? := some endLabel
            continueLabel? := some postLabel }
          bodySupply).calls layout.sites)
    (hResolve : ContextLabelsResolve layout.asm ctx)
    (hPc : target.pc = segment.startPc)
    (hRel : Frame.StateRel source target tokens)
    (hCond :
      Code.runConditionStateWithGasOracle cond oracle cursor source =
        .ok (stateAfterCond, true, cursorAfterCond))
    (hBodyEval :
      Block.EvalWithGasOracle program oracle fuel body cursorAfterCond
        stateAfterCond (Outcome.cont bodyState) cursorAfterBody) :
    ARunResultWithGasOracle layout.asm oracle cursor target
      (fun result targetCursorAtPost =>
        match result with
        | .running targetAtPost =>
            targetCursorAtPost = cursorAfterBody ∧
              Frame.StateRel bodyState targetAtPost tokens ∧
                targetAtPost.pc =
                  Assembly.Program.pcAfter
                    (ForLoop.postPre segment.pre cond
                      (Block.compileFromCtx body
                        { ctx with
                          breakLabel? := some endLabel
                          continueLabel? := some postLabel }
                        bodySupply).code
                      loopLabel bodyLabel postLabel endLabel)
        | .halted _ => False) := by
  let pre := segment.pre
  let suffix := segment.post
  let bodyCtx : CompileContext :=
    { ctx with
      breakLabel? := some endLabel
      continueLabel? := some postLabel }
  let bodyCode := (Block.compileFromCtx body bodyCtx bodySupply).code
  let coreCode :=
    ForLoop.coreCode cond bodyCode postCode loopLabel bodyLabel postLabel
      endLabel
  let postLabelPre :=
    ForLoop.postLabelPre pre cond bodyCode loopLabel bodyLabel endLabel
  let postPre :=
    ForLoop.postPre pre cond bodyCode loopLabel bodyLabel postLabel endLabel
  have hLocalAsm : pre ++ coreCode ++ suffix = layout.asm := by
    simpa [pre, suffix, bodyCtx, bodyCode, coreCode] using segment.hAsm.symm
  have hExactLocal : ExactLabels (pre ++ coreCode ++ suffix) :=
    ExactLabels.cast_asm hLocalAsm.symm layout.exactLabels
  have hLayout :
      ForLoop.Layout pre suffix cond bodyCode postCode loopLabel bodyLabel
        postLabel endLabel :=
    ForLoop.Layout.of_fits_exact
      (pre := pre) (suffix := suffix) (cond := cond)
      (bodyCode := bodyCode) (postCode := postCode)
      (loopLabel := loopLabel) (bodyLabel := bodyLabel)
      (postLabel := postLabel) (endLabel := endLabel)
      (by simpa [bodyCtx, bodyCode, coreCode] using segment.hFits)
      (by simpa [bodyCtx, bodyCode, coreCode] using hExactLocal)
  have hPostLabelPc :
      Assembly.Program.labelPc layout.asm postLabel =
        some (Assembly.Program.byteLength postLabelPre) := by
    simpa [bodyCtx, bodyCode, coreCode, postLabelPre, ← hLocalAsm]
      using hLayout.postLabelPc
  have hEnter :=
    for_enter_body_result_ctx_in_programLayout_withGasOracle
      (program := program) (layout := layout) (ctx := ctx)
      (cond := cond) (body := body) (bodySupply := bodySupply)
      (postCode := postCode) (loopLabel := loopLabel)
      (bodyLabel := bodyLabel) (postLabel := postLabel)
      (endLabel := endLabel) (source := source)
      (stateAfterCond := stateAfterCond)
      (bodyOutcome := Outcome.cont bodyState) (target := target)
      (tokens := tokens) (oracle := oracle) (cursor := cursor)
      (cursorAfterCond := cursorAfterCond) (cursorFinal := cursorAfterBody)
      hCondSafe hCondFrame hBody segment hProgramWF hCtxProcs hBodyCalls
      hResolve hPc hRel hCond hBodyEval
  have hAtPostLabel :
      ARunResultWithGasOracle layout.asm oracle cursor target
        (fun result targetCursorAtPostLabel =>
          match result with
          | .running targetAtPostLabel =>
              targetCursorAtPostLabel = cursorAfterBody ∧
                Frame.StateRel bodyState targetAtPostLabel tokens ∧
                  targetAtPostLabel.pc =
                    Assembly.Program.pcAfter postLabelPre
          | .halted _ => False) := by
    exact
      ARunResultWithGasOracle.mono hEnter
        (by
          intro result targetCursorAtPostLabel hResult
          rcases hResult with ⟨hCursorAtPostLabel, hCompiled⟩
          cases result with
          | halted halt =>
              cases hCompiled
          | running targetAtPostLabel =>
              rcases hCompiled with
                ⟨label, dest, hCont, hLabel, hRelPost, hPcPost⟩
              simp at hCont
              cases hCont
              have hDest :
                  dest = Assembly.Program.byteLength postLabelPre := by
                rw [hLabel] at hPostLabelPc
                cases hPostLabelPc
                rfl
              exact
                ⟨hCursorAtPostLabel, hRelPost, by
                  rw [hPcPost, hDest]
                  rfl⟩)
  refine
    ARunResultWithGasOracle.bind_running
      (program := layout.asm) (oracle := oracle) (cursor := cursor)
      (state := target)
      (middle := fun targetAtPostLabel targetCursorAtPostLabel =>
        targetCursorAtPostLabel = cursorAfterBody ∧
          Frame.StateRel bodyState targetAtPostLabel tokens ∧
            targetAtPostLabel.pc = Assembly.Program.pcAfter postLabelPre)
      hAtPostLabel ?_
  intro targetAtPostLabel targetCursorAtPostLabel hAtPostLabel'
  rcases hAtPostLabel' with
    ⟨hTargetCursorAtPostLabel, hRelAtPostLabel, hPcAtPostLabel⟩
  subst targetCursorAtPostLabel
  have hPostLabelRun :=
    FrameStateRel.label_runResult_at_withGasOracle
      (label := postLabel) (pre := postLabelPre)
      (post :=
        postCode ++
          [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel] ++
          suffix)
      (oracle := oracle) (cursor := cursorAfterBody)
      hLayout.fitPostLabel hPcAtPostLabel hRelAtPostLabel
  have hPostAsm :
      postLabelPre ++ [Assembly.Instr.label postLabel] ++
        (postCode ++
          [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel] ++
          suffix) =
        layout.asm := by
    simpa [pre, suffix, bodyCtx, bodyCode, coreCode, postLabelPre,
      ForLoop.coreCode, ForLoop.afterLoopLabel, ForLoop.afterCondJumpi,
      ForLoop.bodyLabelPre, ForLoop.bodyPre, ForLoop.postLabelPre,
      List.append_assoc] using hLocalAsm
  exact
    ARunResultWithGasOracle.cast_program_mono hPostAsm hPostLabelRun
      (by
        intro result targetCursorAtPost hResult
        cases result with
        | halted halt =>
            cases hResult
        | running targetAtPost =>
            rcases hResult with ⟨hCursorAtPost, hRelAtPost, hPcAtPost⟩
            exact
              ⟨ hCursorAtPost
              , hRelAtPost
              , by
                  simpa [postPre, ForLoop.postPre, postLabelPre,
                    List.append_assoc] using hPcAtPost
              ⟩)

theorem for_post_regular_jump_loop_in_programLayout_withGasOracle
    {program : Program}
    {layout :
      _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.ProgramLayout
        program}
    {ctx : CompileContext} {cond : Code} {post : Block}
    {postSupply : LabelSupply} {bodyCode : Assembly.Program}
    {loopLabel bodyLabel postLabel endLabel : Assembly.Label}
    {fuel : Nat}
    {bodyState postState : RunState}
    {target : EVMState} {tokens : List Word}
    {oracle : GasOracle} {cursor cursorAfterPost : Nat}
    (hPost :
      BlockPreservesInProgramLayoutWithGasOracleAtFuel layout fuel
        { ctx with breakLabel? := none, continueLabel? := none }
        postSupply post)
    (segment :
      CodeSegment layout.asm
        (ForLoop.coreCode cond bodyCode
          (Block.compileFromCtx post
            { ctx with breakLabel? := none, continueLabel? := none }
            postSupply).code
          loopLabel bodyLabel postLabel endLabel))
    (hProgramWF : program.WF)
    (hCtxProcs : ctx.procs = program.procs)
    (hPostCalls :
      CallsIncluded
        (Block.compileFromCtx post
          { ctx with breakLabel? := none, continueLabel? := none }
          postSupply).calls layout.sites)
    (hResolve : ContextLabelsResolve layout.asm ctx)
    (hPc :
      target.pc =
        Assembly.Program.pcAfter
          (ForLoop.postPre segment.pre cond bodyCode loopLabel bodyLabel
            postLabel endLabel))
    (hRel : Frame.StateRel bodyState target tokens)
    (hPostEval :
      Block.EvalWithGasOracle program oracle fuel post cursor bodyState
        (Outcome.regular postState) cursorAfterPost) :
    ARunResultWithGasOracle layout.asm oracle cursor target
      (fun result targetCursorAtLoop =>
        match result with
        | .running targetAtLoop =>
            targetCursorAtLoop = cursorAfterPost ∧
              Frame.StateRel postState targetAtLoop tokens ∧
                targetAtLoop.pc = Assembly.Program.pcAfter segment.pre
        | .halted _ => False) := by
  let pre := segment.pre
  let suffix := segment.post
  let postCtx : CompileContext :=
    { ctx with breakLabel? := none, continueLabel? := none }
  let postCode := (Block.compileFromCtx post postCtx postSupply).code
  let coreCode :=
    ForLoop.coreCode cond bodyCode postCode loopLabel bodyLabel postLabel
      endLabel
  let postPre :=
    ForLoop.postPre pre cond bodyCode loopLabel bodyLabel postLabel endLabel
  have hLocalAsm : pre ++ coreCode ++ suffix = layout.asm := by
    simpa [pre, suffix, postCtx, postCode, coreCode] using segment.hAsm.symm
  have hExactLocal : ExactLabels (pre ++ coreCode ++ suffix) :=
    ExactLabels.cast_asm hLocalAsm.symm layout.exactLabels
  have hLayout :
      ForLoop.Layout pre suffix cond bodyCode postCode loopLabel bodyLabel
        postLabel endLabel :=
    ForLoop.Layout.of_fits_exact
      (pre := pre) (suffix := suffix) (cond := cond)
      (bodyCode := bodyCode) (postCode := postCode)
      (loopLabel := loopLabel) (bodyLabel := bodyLabel)
      (postLabel := postLabel) (endLabel := endLabel)
      (by simpa [postCtx, postCode, coreCode] using segment.hFits)
      (by simpa [postCtx, postCode, coreCode] using hExactLocal)
  let postSeg : CodeSegment layout.asm postCode :=
    { pre := postPre
      post :=
        [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel] ++
          suffix
      hAsm := by
        simpa [pre, suffix, postCtx, postCode, coreCode, postPre,
          ForLoop.coreCode, ForLoop.afterLoopLabel,
          ForLoop.afterCondJumpi, ForLoop.bodyLabelPre, ForLoop.bodyPre,
          ForLoop.postLabelPre, ForLoop.postPre, List.append_assoc]
          using segment.hAsm
      hFits := by
        simpa [postCtx, postCode] using hLayout.fitPost }
  have hPostCtxResolve : ContextLabelsResolve layout.asm postCtx :=
    ContextLabelsResolve.without_break_continue
      (ctx := ctx) hResolve
  have hPostRun :=
    hPost (source := bodyState) (outcome := Outcome.regular postState)
      (target := target) (tokens := tokens) (oracle := oracle)
      (cursor := cursor) (cursorFinal := cursorAfterPost)
      hProgramWF
      (by simpa [postCtx] using hCtxProcs)
      (by simpa [postCtx, postCode] using hPostCalls)
      hPostCtxResolve postSeg
      (by simpa [postSeg, postPre, CodeSegment.startPc] using hPc)
      hRel hPostEval
  have hPostRegular :
      ARunResultWithGasOracle layout.asm oracle cursor target
        (fun result targetCursorAtBackJump =>
          match result with
          | .running targetAtBackJump =>
              targetCursorAtBackJump = cursorAfterPost ∧
                Frame.StateRel postState targetAtBackJump tokens ∧
                  targetAtBackJump.pc =
                    Assembly.Program.pcAfter (postPre ++ postCode)
          | .halted _ => False) := by
    exact
      ARunResultWithGasOracle.mono hPostRun
        (by
          intro result targetCursorAtBackJump hResult
          rcases hResult with ⟨hCursorAtBackJump, hCompiled⟩
          cases result with
          | halted halt =>
              cases hCompiled
          | running targetAtBackJump =>
              exact
                ⟨ hCursorAtBackJump
                , by
                    simpa [postSeg, postCtx, postCode, CompiledOutcomeRel,
                      Outcome.regular, CodeSegment.fallthroughPc,
                      List.append_assoc] using hCompiled
                ⟩)
  refine
    ARunResultWithGasOracle.bind_running
      (program := layout.asm) (oracle := oracle) (cursor := cursor)
      (state := target)
      (middle := fun targetAtBackJump targetCursorAtBackJump =>
        targetCursorAtBackJump = cursorAfterPost ∧
          Frame.StateRel postState targetAtBackJump tokens ∧
            targetAtBackJump.pc =
              Assembly.Program.pcAfter (postPre ++ postCode))
      hPostRegular ?_
  intro targetAtBackJump targetCursorAtBackJump hAtBackJump
  rcases hAtBackJump with
    ⟨hCursorAtBackJump, hRelAtBackJump, hPcAtBackJump⟩
  subst targetCursorAtBackJump
  have hLoopLabel :
      Assembly.Program.labelPc
        ((postPre ++ postCode) ++ [Assembly.Instr.jump loopLabel] ++
          ([Assembly.Instr.label endLabel] ++ suffix))
        loopLabel = some (Assembly.Program.byteLength pre) := by
    simpa [postCtx, postCode, coreCode, postPre, ForLoop.coreCode,
      ForLoop.afterLoopLabel, ForLoop.afterCondJumpi, ForLoop.bodyLabelPre,
      ForLoop.bodyPre, ForLoop.postLabelPre, ForLoop.postPre,
      List.append_assoc] using hLayout.loopLabelPc
  rcases FrameStateRel.jump_stepResult_at_withGasOracle
      (label := loopLabel) (dest := Assembly.Program.byteLength pre)
      (pre := postPre ++ postCode)
      (post := [Assembly.Instr.label endLabel] ++ suffix)
      (oracle := oracle) (cursor := cursorAfterPost)
      hLayout.fitBackJump hPcAtBackJump hRelAtBackJump hLoopLabel with
    ⟨targetAtLoop, hJump, hRelLoop, hPcLoop⟩
  have hBackAsm :
      (postPre ++ postCode) ++ [Assembly.Instr.jump loopLabel] ++
        ([Assembly.Instr.label endLabel] ++ suffix) =
        layout.asm := by
    simpa [pre, suffix, postCtx, postCode, coreCode, postPre,
      ForLoop.coreCode, ForLoop.afterLoopLabel, ForLoop.afterCondJumpi,
      ForLoop.bodyLabelPre, ForLoop.bodyPre, ForLoop.postLabelPre,
      ForLoop.postPre, List.append_assoc] using hLocalAsm
  have hJumpRun :
      ARunResultWithGasOracle
        ((postPre ++ postCode) ++ [Assembly.Instr.jump loopLabel] ++
          ([Assembly.Instr.label endLabel] ++ suffix))
        oracle cursorAfterPost targetAtBackJump
        (fun result targetCursorAtLoop =>
          match result with
          | .running targetAtLoop' =>
              targetCursorAtLoop = cursorAfterPost ∧
                Frame.StateRel postState targetAtLoop' tokens ∧
                  targetAtLoop'.pc = Assembly.Program.pcAfter pre
          | .halted _ => False) := by
    refine ⟨1, .running targetAtLoop, cursorAfterPost, ?_, ?_⟩
    · change
        Assembly.GasParametric.sourceRunNResultWithGasOracle
            ((postPre ++ postCode) ++ [Assembly.Instr.jump loopLabel] ++
              ([Assembly.Instr.label endLabel] ++ suffix))
            oracle 1 cursorAfterPost targetAtBackJump =
          .ok (.running targetAtLoop, cursorAfterPost)
      have hJump' :
          Assembly.GasParametric.sourceStepResultWithGasOracle
              ((postPre ++ postCode) ++ [Assembly.Instr.jump loopLabel] ++
                ([Assembly.Instr.label endLabel] ++ suffix))
              oracle cursorAfterPost targetAtBackJump =
            .ok (.running targetAtLoop, cursorAfterPost) := by
        simpa using hJump
      unfold Assembly.GasParametric.sourceRunNResultWithGasOracle
      rw [hJump']
      rfl
    · exact
        ⟨rfl, hRelLoop, by
          rw [hPcLoop]
          rfl⟩
  exact ARunResultWithGasOracle.cast_program hBackAsm hJumpRun

theorem for_post_leave_from_entry_in_programLayout_withGasOracle
    {program : Program}
    {layout :
      _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.ProgramLayout
        program}
    {ctx : CompileContext} {cond : Code} {post : Block}
    {postSupply : LabelSupply} {bodyCode : Assembly.Program}
    {loopLabel bodyLabel postLabel endLabel : Assembly.Label}
    {fuel : Nat}
    {bodyState postState : RunState}
    {target : EVMState} {tokens : List Word}
    {oracle : GasOracle} {cursor cursorFinal : Nat}
    (hPost :
      BlockPreservesInProgramLayoutWithGasOracleAtFuel layout fuel
        { ctx with breakLabel? := none, continueLabel? := none }
        postSupply post)
    (segment :
      CodeSegment layout.asm
        (ForLoop.coreCode cond bodyCode
          (Block.compileFromCtx post
            { ctx with breakLabel? := none, continueLabel? := none }
            postSupply).code
          loopLabel bodyLabel postLabel endLabel))
    (hProgramWF : program.WF)
    (hCtxProcs : ctx.procs = program.procs)
    (hPostCalls :
      CallsIncluded
        (Block.compileFromCtx post
          { ctx with breakLabel? := none, continueLabel? := none }
          postSupply).calls layout.sites)
    (hResolve : ContextLabelsResolve layout.asm ctx)
    (hPc :
      target.pc =
        Assembly.Program.pcAfter
          (ForLoop.postPre segment.pre cond bodyCode loopLabel bodyLabel
            postLabel endLabel))
    (hRel : Frame.StateRel bodyState target tokens)
    (hPostEval :
      Block.EvalWithGasOracle program oracle fuel post cursor bodyState
        (Outcome.leave postState) cursorFinal) :
    ARunResultWithGasOracle layout.asm oracle cursor target
      (fun result targetCursorFinal =>
        targetCursorFinal = cursorFinal ∧
          CompiledOutcomeRel layout.asm ctx segment.fallthroughPc
            (Outcome.leave postState) result tokens) := by
  let pre := segment.pre
  let suffix := segment.post
  let postCtx : CompileContext :=
    { ctx with breakLabel? := none, continueLabel? := none }
  let postCode := (Block.compileFromCtx post postCtx postSupply).code
  let postPre :=
    ForLoop.postPre pre cond bodyCode loopLabel bodyLabel postLabel endLabel
  let postSeg : CodeSegment layout.asm postCode :=
    { pre := postPre
      post :=
        [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel] ++
          suffix
      hAsm := by
        simpa [pre, suffix, postCtx, postCode, postPre, ForLoop.coreCode,
          ForLoop.afterLoopLabel, ForLoop.afterCondJumpi,
          ForLoop.bodyLabelPre, ForLoop.bodyPre, ForLoop.postLabelPre,
          ForLoop.postPre, List.append_assoc] using segment.hAsm
      hFits := by
        have hFits :
            AssemblyProgram.PCFitsFrom pre
              (ForLoop.coreCode cond bodyCode postCode loopLabel bodyLabel
                postLabel endLabel) := by
          simpa [postCtx, postCode] using segment.hFits
        have hPostFits :
            AssemblyProgram.PCFitsFrom postPre
              (postCode ++
                [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel]) := by
          simpa [postPre, ForLoop.coreCode, ForLoop.afterLoopLabel,
            ForLoop.afterCondJumpi, ForLoop.bodyLabelPre, ForLoop.bodyPre,
            ForLoop.postLabelPre, ForLoop.postPre, List.append_assoc] using
            AssemblyProgram.PCFitsFrom.right (pre := pre)
              (first :=
                [Assembly.Instr.label loopLabel] ++ cond.toAssembly ++
                  [ Assembly.Instr.jumpi bodyLabel
                  , Assembly.Instr.jump endLabel
                  , Assembly.Instr.label bodyLabel
                  ] ++ bodyCode ++ [Assembly.Instr.label postLabel])
              (second :=
                postCode ++
                  [ Assembly.Instr.jump loopLabel
                  , Assembly.Instr.label endLabel ])
              (by simpa [ForLoop.coreCode, List.append_assoc] using hFits)
        exact
          AssemblyProgram.PCFitsFrom.left (pre := postPre)
            (first := postCode)
            (second :=
              [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel])
            hPostFits }
  have hPostCtxResolve : ContextLabelsResolve layout.asm postCtx :=
    ContextLabelsResolve.without_break_continue
      (ctx := ctx) hResolve
  have hPostRun :=
    hPost (source := bodyState) (outcome := Outcome.leave postState)
      (target := target) (tokens := tokens) (oracle := oracle)
      (cursor := cursor) (cursorFinal := cursorFinal)
      hProgramWF
      (by simpa [postCtx] using hCtxProcs)
      (by simpa [postCtx, postCode] using hPostCalls)
      hPostCtxResolve postSeg
      (by simpa [postSeg, postPre, CodeSegment.startPc] using hPc)
      hRel hPostEval
  exact
    ARunResultWithGasOracle.mono hPostRun
      (by
        intro result targetCursorFinal hResult
        rcases hResult with ⟨hCursorFinal, hCompiled⟩
        cases result with
        | running target' =>
            exact
              ⟨hCursorFinal, by
                simpa [postCtx, CompiledOutcomeRel, Outcome.leave] using
                  hCompiled⟩
        | halted halt =>
            cases hCompiled)

theorem for_post_halt_from_entry_in_programLayout_withGasOracle
    {program : Program}
    {layout :
      _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.ProgramLayout
        program}
    {ctx : CompileContext} {cond : Code} {post : Block}
    {postSupply : LabelSupply} {bodyCode : Assembly.Program}
    {loopLabel bodyLabel postLabel endLabel : Assembly.Label}
    {fuel : Nat}
    {bodyState postState : RunState} {kind : Assembly.HaltKind}
    {target : EVMState} {tokens : List Word}
    {oracle : GasOracle} {cursor cursorFinal : Nat}
    (hPost :
      BlockPreservesInProgramLayoutWithGasOracleAtFuel layout fuel
        { ctx with breakLabel? := none, continueLabel? := none }
        postSupply post)
    (segment :
      CodeSegment layout.asm
        (ForLoop.coreCode cond bodyCode
          (Block.compileFromCtx post
            { ctx with breakLabel? := none, continueLabel? := none }
            postSupply).code
          loopLabel bodyLabel postLabel endLabel))
    (hProgramWF : program.WF)
    (hCtxProcs : ctx.procs = program.procs)
    (hPostCalls :
      CallsIncluded
        (Block.compileFromCtx post
          { ctx with breakLabel? := none, continueLabel? := none }
          postSupply).calls layout.sites)
    (hResolve : ContextLabelsResolve layout.asm ctx)
    (hPc :
      target.pc =
        Assembly.Program.pcAfter
          (ForLoop.postPre segment.pre cond bodyCode loopLabel bodyLabel
            postLabel endLabel))
    (hRel : Frame.StateRel bodyState target tokens)
    (hPostEval :
      Block.EvalWithGasOracle program oracle fuel post cursor bodyState
        (Outcome.halt kind postState) cursorFinal) :
    ARunResultWithGasOracle layout.asm oracle cursor target
      (fun result targetCursorFinal =>
        targetCursorFinal = cursorFinal ∧
          CompiledOutcomeRel layout.asm ctx segment.fallthroughPc
            (Outcome.halt kind postState) result tokens) := by
  let pre := segment.pre
  let suffix := segment.post
  let postCtx : CompileContext :=
    { ctx with breakLabel? := none, continueLabel? := none }
  let postCode := (Block.compileFromCtx post postCtx postSupply).code
  let postPre :=
    ForLoop.postPre pre cond bodyCode loopLabel bodyLabel postLabel endLabel
  let postSeg : CodeSegment layout.asm postCode :=
    { pre := postPre
      post :=
        [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel] ++
          suffix
      hAsm := by
        simpa [pre, suffix, postCtx, postCode, postPre, ForLoop.coreCode,
          ForLoop.afterLoopLabel, ForLoop.afterCondJumpi,
          ForLoop.bodyLabelPre, ForLoop.bodyPre, ForLoop.postLabelPre,
          ForLoop.postPre, List.append_assoc] using segment.hAsm
      hFits := by
        have hFits :
            AssemblyProgram.PCFitsFrom pre
              (ForLoop.coreCode cond bodyCode postCode loopLabel bodyLabel
                postLabel endLabel) := by
          simpa [postCtx, postCode] using segment.hFits
        have hPostFits :
            AssemblyProgram.PCFitsFrom postPre
              (postCode ++
                [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel]) := by
          simpa [postPre, ForLoop.coreCode, ForLoop.afterLoopLabel,
            ForLoop.afterCondJumpi, ForLoop.bodyLabelPre, ForLoop.bodyPre,
            ForLoop.postLabelPre, ForLoop.postPre, List.append_assoc] using
            AssemblyProgram.PCFitsFrom.right (pre := pre)
              (first :=
                [Assembly.Instr.label loopLabel] ++ cond.toAssembly ++
                  [ Assembly.Instr.jumpi bodyLabel
                  , Assembly.Instr.jump endLabel
                  , Assembly.Instr.label bodyLabel
                  ] ++ bodyCode ++ [Assembly.Instr.label postLabel])
              (second :=
                postCode ++
                  [ Assembly.Instr.jump loopLabel
                  , Assembly.Instr.label endLabel ])
              (by simpa [ForLoop.coreCode, List.append_assoc] using hFits)
        exact
          AssemblyProgram.PCFitsFrom.left (pre := postPre)
            (first := postCode)
            (second :=
              [Assembly.Instr.jump loopLabel, Assembly.Instr.label endLabel])
            hPostFits }
  have hPostCtxResolve : ContextLabelsResolve layout.asm postCtx :=
    ContextLabelsResolve.without_break_continue
      (ctx := ctx) hResolve
  have hPostRun :=
    hPost (source := bodyState) (outcome := Outcome.halt kind postState)
      (target := target) (tokens := tokens) (oracle := oracle)
      (cursor := cursor) (cursorFinal := cursorFinal)
      hProgramWF
      (by simpa [postCtx] using hCtxProcs)
      (by simpa [postCtx, postCode] using hPostCalls)
      hPostCtxResolve postSeg
      (by simpa [postSeg, postPre, CodeSegment.startPc] using hPc)
      hRel hPostEval
  exact
    ARunResultWithGasOracle.mono hPostRun
      (by
        intro result targetCursorFinal hResult
        rcases hResult with ⟨hCursorFinal, hCompiled⟩
        cases result with
        | running target' =>
            cases hCompiled
        | halted halt =>
            exact
              ⟨hCursorFinal, by
                simpa [postCtx, CompiledOutcomeRel, Outcome.halt] using
                  hCompiled⟩)

set_option maxHeartbeats 3000000 in
theorem for_eval_in_programLayout_withGasOracle {program : Program}
    {layout :
      _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.ProgramLayout
        program}
    {ctx : CompileContext} {cond : Code} {body post : Block}
    {bodySupply postSupply : LabelSupply}
    {loopLabel bodyLabel postLabel endLabel : Assembly.Label}
    {maxFuel : Nat}
    (hCondSafe : Code.RunnerSafeWithGasOracle cond)
    (hCondFrame : Code.FrameSafeWithGasOracle cond)
    (hBody :
      ∀ {bodyFuel : Nat}, bodyFuel < maxFuel →
        BlockPreservesInProgramLayoutWithGasOracleAtFuel layout bodyFuel
          { ctx with
            breakLabel? := some endLabel
            continueLabel? := some postLabel }
          bodySupply body)
    (hPost :
      ∀ {postFuel : Nat}, postFuel < maxFuel →
        BlockPreservesInProgramLayoutWithGasOracleAtFuel layout postFuel
          { ctx with breakLabel? := none, continueLabel? := none }
          postSupply post) :
    ∀ {bodyCode postCode : Assembly.Program}
      {fuel : Nat}
      {source : RunState} {outcome : Outcome}
      {target : EVMState} {tokens : List Word}
      {oracle : GasOracle} {cursor cursorFinal : Nat},
      bodyCode =
        (Block.compileFromCtx body
          { ctx with
            breakLabel? := some endLabel
            continueLabel? := some postLabel }
          bodySupply).code →
      postCode =
        (Block.compileFromCtx post
          { ctx with breakLabel? := none, continueLabel? := none }
          postSupply).code →
      fuel < maxFuel →
      (segment :
        CodeSegment layout.asm
          (ForLoop.coreCode cond bodyCode postCode loopLabel bodyLabel
            postLabel endLabel)) →
      program.WF →
      ctx.procs = program.procs →
      CallsIncluded
        (Block.compileFromCtx body
          { ctx with
            breakLabel? := some endLabel
            continueLabel? := some postLabel }
          bodySupply).calls layout.sites →
      CallsIncluded
        (Block.compileFromCtx post
          { ctx with breakLabel? := none, continueLabel? := none }
          postSupply).calls layout.sites →
      ContextLabelsResolve layout.asm ctx →
      target.pc = segment.startPc →
      Frame.StateRel source target tokens →
      For.EvalWithGasOracle program oracle fuel cond post body cursor source
        outcome cursorFinal →
      ARunResultWithGasOracle layout.asm oracle cursor target
        (fun result targetCursorFinal =>
          targetCursorFinal = cursorFinal ∧
            CompiledOutcomeRel layout.asm ctx segment.fallthroughPc outcome
              result tokens) := by
  intro bodyCode postCode fuel source outcome target tokens oracle cursor
    cursorFinal hBodyCode hPostCode hFuelLt segment hProgramWF hCtxProcs
    hBodyCalls hPostCalls hResolve hPc hRel hEval
  subst bodyCode
  subst postCode
  induction fuel generalizing source outcome target tokens oracle cursor
      cursorFinal segment with
  | zero =>
      cases hEval
  | succ fuel ih =>
      let bodyCtx : CompileContext :=
        { ctx with
          breakLabel? := some endLabel
          continueLabel? := some postLabel }
      let postCtx : CompileContext :=
        { ctx with breakLabel? := none, continueLabel? := none }
      let bodyCode := (Block.compileFromCtx body bodyCtx bodySupply).code
      let postCode := (Block.compileFromCtx post postCtx postSupply).code
      let coreSeg : CodeSegment layout.asm
          (ForLoop.coreCode cond bodyCode postCode loopLabel bodyLabel
            postLabel endLabel) :=
        segment
      cases hEval with
      | false hCond =>
          exact
            for_false_case_in_programLayout_withGasOracle
              (program := program) (layout := layout) (ctx := ctx)
              (cond := cond) (bodyCode := bodyCode) (postCode := postCode)
              (loopLabel := loopLabel) (bodyLabel := bodyLabel)
              (postLabel := postLabel) (endLabel := endLabel)
              (source := source) (stateAfterCond := _)
              (target := target) (tokens := tokens) (oracle := oracle)
              (cursor := cursor) (cursorAfterCond := cursorFinal)
              hCondSafe hCondFrame
              coreSeg
              hPc hRel hCond
      | body_brk hCond hBodyEval =>
          exact
            for_body_brk_case_in_programLayout_withGasOracle
              (program := program) (layout := layout) (ctx := ctx)
              (cond := cond) (body := body) (bodySupply := bodySupply)
              (postCode := postCode) (loopLabel := loopLabel)
              (bodyLabel := bodyLabel) (postLabel := postLabel)
              (endLabel := endLabel) (source := source)
              (stateAfterCond := _) (bodyState := _)
              (target := target) (tokens := tokens) (oracle := oracle)
              (cursor := cursor) (cursorAfterCond := _)
              (cursorFinal := cursorFinal)
              hCondSafe hCondFrame
              (hBody (by omega))
              coreSeg
              hProgramWF hCtxProcs
              hBodyCalls
              hResolve hPc hRel hCond hBodyEval
      | body_leave hCond hBodyEval =>
          exact
            for_body_leave_case_in_programLayout_withGasOracle
              (program := program) (layout := layout) (ctx := ctx)
              (cond := cond) (body := body) (bodySupply := bodySupply)
              (postCode := postCode) (loopLabel := loopLabel)
              (bodyLabel := bodyLabel) (postLabel := postLabel)
              (endLabel := endLabel) (source := source)
              (stateAfterCond := _) (bodyState := _)
              (target := target) (tokens := tokens) (oracle := oracle)
              (cursor := cursor) (cursorAfterCond := _)
              (cursorFinal := cursorFinal)
              hCondSafe hCondFrame
              (hBody (by omega))
              coreSeg
              hProgramWF hCtxProcs
              hBodyCalls
              hResolve hPc hRel hCond hBodyEval
      | body_halt hCond hBodyEval =>
          exact
            for_body_halt_case_in_programLayout_withGasOracle
              (program := program) (layout := layout) (ctx := ctx)
              (cond := cond) (body := body) (bodySupply := bodySupply)
              (postCode := postCode) (loopLabel := loopLabel)
              (bodyLabel := bodyLabel) (postLabel := postLabel)
              (endLabel := endLabel) (source := source)
              (stateAfterCond := _) (bodyState := _) (kind := _)
              (target := target) (tokens := tokens) (oracle := oracle)
              (cursor := cursor) (cursorAfterCond := _)
              (cursorFinal := cursorFinal)
              hCondSafe hCondFrame
              (hBody (by omega))
              coreSeg
              hProgramWF hCtxProcs
              hBodyCalls
              hResolve hPc hRel hCond hBodyEval
      | regular_post_regular hCond hBodyEval hPostEval hLoop =>
          rename_i cursorAfterCond cursorAfterBody cursorAfterPost
            stateAfterCond bodyState postState
          let postPre :=
            ForLoop.postPre segment.pre cond bodyCode loopLabel bodyLabel
              postLabel endLabel
          have hEnterPost :=
            for_body_regular_enter_post_in_programLayout_withGasOracle
              (program := program) (layout := layout) (ctx := ctx)
              (cond := cond) (body := body) (bodySupply := bodySupply)
              (postCode := postCode) (loopLabel := loopLabel)
              (bodyLabel := bodyLabel) (postLabel := postLabel)
              (endLabel := endLabel) (source := source)
              (stateAfterCond := stateAfterCond) (bodyState := bodyState)
              (target := target) (tokens := tokens) (oracle := oracle)
              (cursor := cursor) (cursorAfterCond := cursorAfterCond)
              (cursorAfterBody := cursorAfterBody)
              hCondSafe hCondFrame
              (hBody (by omega))
              coreSeg
              hProgramWF hCtxProcs
              hBodyCalls hResolve hPc hRel hCond hBodyEval
          refine
            ARunResultWithGasOracle.bind_running
              (program := layout.asm) (oracle := oracle) (cursor := cursor)
              (state := target)
              (middle := fun targetAtPost targetCursorAtPost =>
                targetCursorAtPost = cursorAfterBody ∧
                  Frame.StateRel bodyState targetAtPost tokens ∧
                    targetAtPost.pc = Assembly.Program.pcAfter postPre)
              ?_ ?_
          · simpa [bodyCtx, postCtx, bodyCode, postCode, postPre] using
              hEnterPost
          · intro targetAtPost targetCursorAtPost hAtPost
            rcases hAtPost with
              ⟨hCursorAtPost, hRelAtPost, hPcAtPost⟩
            subst targetCursorAtPost
            have hBack :=
              for_post_regular_jump_loop_in_programLayout_withGasOracle
                (program := program) (layout := layout) (ctx := ctx)
                (cond := cond) (post := post) (postSupply := postSupply)
                (bodyCode := bodyCode) (loopLabel := loopLabel)
                (bodyLabel := bodyLabel) (postLabel := postLabel)
                (endLabel := endLabel) (bodyState := bodyState)
                (postState := postState) (target := targetAtPost)
                (tokens := tokens) (oracle := oracle)
                (cursor := cursorAfterBody)
                (cursorAfterPost := cursorAfterPost)
                (hPost (by omega))
                coreSeg
                hProgramWF hCtxProcs
                hPostCalls
                hResolve hPcAtPost hRelAtPost hPostEval
            refine
              ARunResultWithGasOracle.bind_running
                (program := layout.asm) (oracle := oracle)
                (cursor := cursorAfterBody) (state := targetAtPost)
                (middle := fun targetAtLoop targetCursorAtLoop =>
                  targetCursorAtLoop = cursorAfterPost ∧
                    Frame.StateRel postState targetAtLoop tokens ∧
                      targetAtLoop.pc = Assembly.Program.pcAfter segment.pre)
                hBack ?_
            intro targetAtLoop targetCursorAtLoop hAtLoop
            rcases hAtLoop with
              ⟨hCursorAtLoop, hRelAtLoop, hPcAtLoop⟩
            subst targetCursorAtLoop
            simpa [bodyCtx, postCtx, bodyCode, postCode] using
              ih (by omega) hRelAtLoop hLoop coreSeg
                (by simpa [CodeSegment.startPc] using hPcAtLoop)
      | cont_post_regular hCond hBodyEval hPostEval hLoop =>
          rename_i cursorAfterCond cursorAfterBody cursorAfterPost
            stateAfterCond bodyState postState
          let postPre :=
            ForLoop.postPre segment.pre cond bodyCode loopLabel bodyLabel
              postLabel endLabel
          have hEnterPost :=
            for_body_cont_enter_post_in_programLayout_withGasOracle
              (program := program) (layout := layout) (ctx := ctx)
              (cond := cond) (body := body) (bodySupply := bodySupply)
              (postCode := postCode) (loopLabel := loopLabel)
              (bodyLabel := bodyLabel) (postLabel := postLabel)
              (endLabel := endLabel) (source := source)
              (stateAfterCond := stateAfterCond) (bodyState := bodyState)
              (target := target) (tokens := tokens) (oracle := oracle)
              (cursor := cursor) (cursorAfterCond := cursorAfterCond)
              (cursorAfterBody := cursorAfterBody)
              hCondSafe hCondFrame
              (hBody (by omega))
              coreSeg
              hProgramWF hCtxProcs
              hBodyCalls hResolve hPc hRel hCond hBodyEval
          refine
            ARunResultWithGasOracle.bind_running
              (program := layout.asm) (oracle := oracle) (cursor := cursor)
              (state := target)
              (middle := fun targetAtPost targetCursorAtPost =>
                targetCursorAtPost = cursorAfterBody ∧
                  Frame.StateRel bodyState targetAtPost tokens ∧
                    targetAtPost.pc = Assembly.Program.pcAfter postPre)
              ?_ ?_
          · simpa [bodyCtx, postCtx, bodyCode, postCode, postPre] using
              hEnterPost
          · intro targetAtPost targetCursorAtPost hAtPost
            rcases hAtPost with
              ⟨hCursorAtPost, hRelAtPost, hPcAtPost⟩
            subst targetCursorAtPost
            have hBack :=
              for_post_regular_jump_loop_in_programLayout_withGasOracle
                (program := program) (layout := layout) (ctx := ctx)
                (cond := cond) (post := post) (postSupply := postSupply)
                (bodyCode := bodyCode) (loopLabel := loopLabel)
                (bodyLabel := bodyLabel) (postLabel := postLabel)
                (endLabel := endLabel) (bodyState := bodyState)
                (postState := postState) (target := targetAtPost)
                (tokens := tokens) (oracle := oracle)
                (cursor := cursorAfterBody)
                (cursorAfterPost := cursorAfterPost)
                (hPost (by omega))
                coreSeg
                hProgramWF hCtxProcs
                hPostCalls
                hResolve hPcAtPost hRelAtPost hPostEval
            refine
              ARunResultWithGasOracle.bind_running
                (program := layout.asm) (oracle := oracle)
                (cursor := cursorAfterBody) (state := targetAtPost)
                (middle := fun targetAtLoop targetCursorAtLoop =>
                  targetCursorAtLoop = cursorAfterPost ∧
                    Frame.StateRel postState targetAtLoop tokens ∧
                      targetAtLoop.pc = Assembly.Program.pcAfter segment.pre)
                hBack ?_
            intro targetAtLoop targetCursorAtLoop hAtLoop
            rcases hAtLoop with
              ⟨hCursorAtLoop, hRelAtLoop, hPcAtLoop⟩
            subst targetCursorAtLoop
            simpa [bodyCtx, postCtx, bodyCode, postCode] using
              ih (by omega) hRelAtLoop hLoop coreSeg
                (by simpa [CodeSegment.startPc] using hPcAtLoop)
      | regular_post_leave hCond hBodyEval hPostEval =>
          rename_i cursorAfterCond cursorAfterBody stateAfterCond bodyState
            postState
          let postPre :=
            ForLoop.postPre segment.pre cond bodyCode loopLabel bodyLabel
              postLabel endLabel
          have hEnterPost :=
            for_body_regular_enter_post_in_programLayout_withGasOracle
              (program := program) (layout := layout) (ctx := ctx)
              (cond := cond) (body := body) (bodySupply := bodySupply)
              (postCode := postCode) (loopLabel := loopLabel)
              (bodyLabel := bodyLabel) (postLabel := postLabel)
              (endLabel := endLabel) (source := source)
              (stateAfterCond := stateAfterCond) (bodyState := bodyState)
              (target := target) (tokens := tokens) (oracle := oracle)
              (cursor := cursor) (cursorAfterCond := cursorAfterCond)
              (cursorAfterBody := cursorAfterBody)
              hCondSafe hCondFrame
              (hBody (by omega))
              coreSeg
              hProgramWF hCtxProcs
              hBodyCalls hResolve hPc hRel hCond hBodyEval
          refine
            ARunResultWithGasOracle.bind_running
              (program := layout.asm) (oracle := oracle) (cursor := cursor)
              (state := target)
              (middle := fun targetAtPost targetCursorAtPost =>
                targetCursorAtPost = cursorAfterBody ∧
                  Frame.StateRel bodyState targetAtPost tokens ∧
                    targetAtPost.pc = Assembly.Program.pcAfter postPre)
              ?_ ?_
          · simpa [bodyCtx, postCtx, bodyCode, postCode, postPre] using
              hEnterPost
          · intro targetAtPost targetCursorAtPost hAtPost
            rcases hAtPost with
              ⟨hCursorAtPost, hRelAtPost, hPcAtPost⟩
            subst targetCursorAtPost
            simpa [bodyCtx, postCtx, bodyCode, postCode] using
              for_post_leave_from_entry_in_programLayout_withGasOracle
                (program := program) (layout := layout) (ctx := ctx)
                (cond := cond) (post := post) (postSupply := postSupply)
                (bodyCode := bodyCode) (loopLabel := loopLabel)
                (bodyLabel := bodyLabel) (postLabel := postLabel)
                (endLabel := endLabel) (bodyState := bodyState)
                (postState := postState) (target := targetAtPost)
                (tokens := tokens) (oracle := oracle)
                (cursor := cursorAfterBody) (cursorFinal := cursorFinal)
                (hPost (by omega))
                coreSeg
                hProgramWF hCtxProcs
                hPostCalls hResolve hPcAtPost hRelAtPost hPostEval
      | cont_post_leave hCond hBodyEval hPostEval =>
          rename_i cursorAfterCond cursorAfterBody stateAfterCond bodyState
            postState
          let postPre :=
            ForLoop.postPre segment.pre cond bodyCode loopLabel bodyLabel
              postLabel endLabel
          have hEnterPost :=
            for_body_cont_enter_post_in_programLayout_withGasOracle
              (program := program) (layout := layout) (ctx := ctx)
              (cond := cond) (body := body) (bodySupply := bodySupply)
              (postCode := postCode) (loopLabel := loopLabel)
              (bodyLabel := bodyLabel) (postLabel := postLabel)
              (endLabel := endLabel) (source := source)
              (stateAfterCond := stateAfterCond) (bodyState := bodyState)
              (target := target) (tokens := tokens) (oracle := oracle)
              (cursor := cursor) (cursorAfterCond := cursorAfterCond)
              (cursorAfterBody := cursorAfterBody)
              hCondSafe hCondFrame
              (hBody (by omega))
              coreSeg
              hProgramWF hCtxProcs
              hBodyCalls hResolve hPc hRel hCond hBodyEval
          refine
            ARunResultWithGasOracle.bind_running
              (program := layout.asm) (oracle := oracle) (cursor := cursor)
              (state := target)
              (middle := fun targetAtPost targetCursorAtPost =>
                targetCursorAtPost = cursorAfterBody ∧
                  Frame.StateRel bodyState targetAtPost tokens ∧
                    targetAtPost.pc = Assembly.Program.pcAfter postPre)
              ?_ ?_
          · simpa [bodyCtx, postCtx, bodyCode, postCode, postPre] using
              hEnterPost
          · intro targetAtPost targetCursorAtPost hAtPost
            rcases hAtPost with
              ⟨hCursorAtPost, hRelAtPost, hPcAtPost⟩
            subst targetCursorAtPost
            simpa [bodyCtx, postCtx, bodyCode, postCode] using
              for_post_leave_from_entry_in_programLayout_withGasOracle
                (program := program) (layout := layout) (ctx := ctx)
                (cond := cond) (post := post) (postSupply := postSupply)
                (bodyCode := bodyCode) (loopLabel := loopLabel)
                (bodyLabel := bodyLabel) (postLabel := postLabel)
                (endLabel := endLabel) (bodyState := bodyState)
                (postState := postState) (target := targetAtPost)
                (tokens := tokens) (oracle := oracle)
                (cursor := cursorAfterBody) (cursorFinal := cursorFinal)
                (hPost (by omega))
                coreSeg
                hProgramWF hCtxProcs
                hPostCalls hResolve hPcAtPost hRelAtPost hPostEval
      | regular_post_halt hCond hBodyEval hPostEval =>
          rename_i cursorAfterCond cursorAfterBody stateAfterCond bodyState
            postState kind
          let postPre :=
            ForLoop.postPre segment.pre cond bodyCode loopLabel bodyLabel
              postLabel endLabel
          have hEnterPost :=
            for_body_regular_enter_post_in_programLayout_withGasOracle
              (program := program) (layout := layout) (ctx := ctx)
              (cond := cond) (body := body) (bodySupply := bodySupply)
              (postCode := postCode) (loopLabel := loopLabel)
              (bodyLabel := bodyLabel) (postLabel := postLabel)
              (endLabel := endLabel) (source := source)
              (stateAfterCond := stateAfterCond) (bodyState := bodyState)
              (target := target) (tokens := tokens) (oracle := oracle)
              (cursor := cursor) (cursorAfterCond := cursorAfterCond)
              (cursorAfterBody := cursorAfterBody)
              hCondSafe hCondFrame
              (hBody (by omega))
              coreSeg
              hProgramWF hCtxProcs
              hBodyCalls hResolve hPc hRel hCond hBodyEval
          refine
            ARunResultWithGasOracle.bind_running
              (program := layout.asm) (oracle := oracle) (cursor := cursor)
              (state := target)
              (middle := fun targetAtPost targetCursorAtPost =>
                targetCursorAtPost = cursorAfterBody ∧
                  Frame.StateRel bodyState targetAtPost tokens ∧
                    targetAtPost.pc = Assembly.Program.pcAfter postPre)
              ?_ ?_
          · simpa [bodyCtx, postCtx, bodyCode, postCode, postPre] using
              hEnterPost
          · intro targetAtPost targetCursorAtPost hAtPost
            rcases hAtPost with
              ⟨hCursorAtPost, hRelAtPost, hPcAtPost⟩
            subst targetCursorAtPost
            simpa [bodyCtx, postCtx, bodyCode, postCode] using
              for_post_halt_from_entry_in_programLayout_withGasOracle
                (program := program) (layout := layout) (ctx := ctx)
                (cond := cond) (post := post) (postSupply := postSupply)
                (bodyCode := bodyCode) (loopLabel := loopLabel)
                (bodyLabel := bodyLabel) (postLabel := postLabel)
                (endLabel := endLabel) (bodyState := bodyState)
                (postState := postState) (kind := kind)
                (target := targetAtPost) (tokens := tokens)
                (oracle := oracle)
                (cursor := cursorAfterBody) (cursorFinal := cursorFinal)
                (hPost (by omega))
                coreSeg
                hProgramWF hCtxProcs
                hPostCalls hResolve hPcAtPost hRelAtPost hPostEval
      | cont_post_halt hCond hBodyEval hPostEval =>
          rename_i cursorAfterCond cursorAfterBody stateAfterCond bodyState
            postState kind
          let postPre :=
            ForLoop.postPre segment.pre cond bodyCode loopLabel bodyLabel
              postLabel endLabel
          have hEnterPost :=
            for_body_cont_enter_post_in_programLayout_withGasOracle
              (program := program) (layout := layout) (ctx := ctx)
              (cond := cond) (body := body) (bodySupply := bodySupply)
              (postCode := postCode) (loopLabel := loopLabel)
              (bodyLabel := bodyLabel) (postLabel := postLabel)
              (endLabel := endLabel) (source := source)
              (stateAfterCond := stateAfterCond) (bodyState := bodyState)
              (target := target) (tokens := tokens) (oracle := oracle)
              (cursor := cursor) (cursorAfterCond := cursorAfterCond)
              (cursorAfterBody := cursorAfterBody)
              hCondSafe hCondFrame
              (hBody (by omega))
              coreSeg
              hProgramWF hCtxProcs
              hBodyCalls hResolve hPc hRel hCond hBodyEval
          refine
            ARunResultWithGasOracle.bind_running
              (program := layout.asm) (oracle := oracle) (cursor := cursor)
              (state := target)
              (middle := fun targetAtPost targetCursorAtPost =>
                targetCursorAtPost = cursorAfterBody ∧
                  Frame.StateRel bodyState targetAtPost tokens ∧
                    targetAtPost.pc = Assembly.Program.pcAfter postPre)
              ?_ ?_
          · simpa [bodyCtx, postCtx, bodyCode, postCode, postPre] using
              hEnterPost
          · intro targetAtPost targetCursorAtPost hAtPost
            rcases hAtPost with
              ⟨hCursorAtPost, hRelAtPost, hPcAtPost⟩
            subst targetCursorAtPost
            simpa [bodyCtx, postCtx, bodyCode, postCode] using
              for_post_halt_from_entry_in_programLayout_withGasOracle
                (program := program) (layout := layout) (ctx := ctx)
                (cond := cond) (post := post) (postSupply := postSupply)
                (bodyCode := bodyCode) (loopLabel := loopLabel)
                (bodyLabel := bodyLabel) (postLabel := postLabel)
                (endLabel := endLabel) (bodyState := bodyState)
                (postState := postState) (kind := kind)
                (target := targetAtPost) (tokens := tokens)
                (oracle := oracle)
                (cursor := cursorAfterBody) (cursorFinal := cursorFinal)
                (hPost (by omega))
                coreSeg
                hProgramWF hCtxProcs
                hPostCalls hResolve hPcAtPost hRelAtPost hPostEval

set_option maxHeartbeats 1200000 in
theorem preserves_for_in_programLayout_upTo_withGasOracle {program : Program}
    {layout :
      _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.ProgramLayout
        program}
    {maxFuel : Nat}
    {ctx : CompileContext} {supply : LabelSupply}
    {init post body : Block} {cond : Code}
    (hCondSafe : Code.RunnerSafeWithGasOracle cond)
    (hCondFrame : Code.FrameSafeWithGasOracle cond)
    (hInit :
      BlockPreservesInProgramLayoutWithGasOracleUpTo layout maxFuel
        { ctx with breakLabel? := none, continueLabel? := none }
        (LabelSupply.next supply) init)
    (hBody :
      BlockPreservesInProgramLayoutWithGasOracleUpTo layout maxFuel
        { ctx with
          breakLabel? := some (LabelSupply.label supply 3)
          continueLabel? := some (LabelSupply.label supply 2) }
        (Block.compileFromCtx init
          { ctx with breakLabel? := none, continueLabel? := none }
          (LabelSupply.next supply)).next
        body)
    (hPost :
      BlockPreservesInProgramLayoutWithGasOracleUpTo layout maxFuel
        { ctx with breakLabel? := none, continueLabel? := none }
        (Block.compileFromCtx body
          { ctx with
            breakLabel? := some (LabelSupply.label supply 3)
            continueLabel? := some (LabelSupply.label supply 2) }
          (Block.compileFromCtx init
            { ctx with breakLabel? := none, continueLabel? := none }
            (LabelSupply.next supply)).next).next
        post) :
    StmtPreservesInProgramLayoutWithGasOracleUpTo layout maxFuel ctx supply
      (.for_ init cond post body) := by
  intro fuel source outcome target tokens oracle cursor cursorFinal hLt
    hProgramWF hCtxProcs hCalls hResolve segment hPc hRel hEval
  let loopLabel := LabelSupply.label supply 0
  let bodyLabel := LabelSupply.label supply 1
  let postLabel := LabelSupply.label supply 2
  let endLabel := LabelSupply.label supply 3
  let loopOuterCtx : CompileContext :=
    { ctx with breakLabel? := none, continueLabel? := none }
  let compiledInit :=
    Block.compileFromCtx init loopOuterCtx (LabelSupply.next supply)
  let bodyCtx : CompileContext :=
    { ctx with
      breakLabel? := some endLabel
      continueLabel? := some postLabel }
  let compiledBody := Block.compileFromCtx body bodyCtx compiledInit.next
  let compiledPost := Block.compileFromCtx post loopOuterCtx compiledBody.next
  let coreCode :=
    ForLoop.coreCode cond compiledBody.code compiledPost.code loopLabel
      bodyLabel postLabel endLabel
  have hCodeEq :
      (Stmt.compileFromCtxCore (.for_ init cond post body) ctx supply).code =
        compiledInit.code ++ coreCode := by
    simp [Stmt.compileFromCtxCore, loopLabel, bodyLabel, postLabel, endLabel,
      loopOuterCtx, bodyCtx, compiledInit, compiledBody, compiledPost,
      coreCode, ForLoop.coreCode, List.append_assoc]
  let appendSeg : CodeSegment layout.asm (compiledInit.code ++ coreCode) :=
    CodeSegment.cast_code hCodeEq segment
  let initSeg : CodeSegment layout.asm compiledInit.code :=
    CodeSegment.left appendSeg
  let coreSeg : CodeSegment layout.asm coreCode :=
    CodeSegment.right appendSeg
  have hInitCalls :
      CallsIncluded compiledInit.calls layout.sites := by
    simpa [loopOuterCtx, compiledInit] using
      _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.for_calls_included_init
        (ctx := ctx) (supply := supply) (init := init) (post := post)
        (body := body) (cond := cond) hCalls
  have hBodyCalls :
      CallsIncluded compiledBody.calls layout.sites := by
    simpa [loopOuterCtx, bodyCtx, compiledInit, compiledBody] using
      _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.for_calls_included_body
        (ctx := ctx) (supply := supply) (init := init) (post := post)
        (body := body) (cond := cond) hCalls
  have hPostCalls :
      CallsIncluded compiledPost.calls layout.sites := by
    simpa [loopOuterCtx, bodyCtx, compiledInit, compiledBody, compiledPost]
      using
        _root_.EvmCompiler.Structured.Preservation.ProcedurePreservation.for_calls_included_post
          (ctx := ctx) (supply := supply) (init := init) (post := post)
          (body := body) (cond := cond) hCalls
  have hLoopOuterResolve :
      ContextLabelsResolve layout.asm loopOuterCtx :=
    ContextLabelsResolve.without_break_continue
      (ctx := ctx) hResolve
  have hInitPc : target.pc = initSeg.startPc := by
    simpa [initSeg, appendSeg, CodeSegment.startPc, CodeSegment.left,
      CodeSegment.cast_code] using hPc
  have hCoreFallthrough :
      coreSeg.fallthroughPc = segment.fallthroughPc := by
    simp [coreSeg, appendSeg, CodeSegment.fallthroughPc, CodeSegment.right,
      CodeSegment.cast_code, hCodeEq, List.append_assoc]
  cases hEval with
  | for_init_regular hInitEval hLoopEval =>
      rename_i cursorAfterInit initState
      have hInitRun :=
        hInit (source := source) (outcome := Outcome.regular initState)
          (target := target) (tokens := tokens) (oracle := oracle)
          (cursor := cursor) (cursorFinal := cursorAfterInit)
          (by omega) hProgramWF
          (by simpa [loopOuterCtx] using hCtxProcs)
          hInitCalls hLoopOuterResolve initSeg
          hInitPc hRel hInitEval
      have hInitRegular :
          ARunResultWithGasOracle layout.asm oracle cursor target
            (fun result targetCursorAfterInit =>
              match result with
              | .running targetAfterInit =>
                  targetCursorAfterInit = cursorAfterInit ∧
                    Frame.StateRel initState targetAfterInit tokens ∧
                      targetAfterInit.pc = coreSeg.startPc
              | .halted _ => False) := by
        exact
          ARunResultWithGasOracle.mono hInitRun
            (by
              intro result targetCursorAfterInit hResult
              rcases hResult with ⟨hCursorAfterInit, hCompiled⟩
              cases result with
              | halted halt =>
                  cases hCompiled
              | running targetAfterInit =>
                  rcases hCompiled with ⟨hRelInit, hPcInit⟩
                  exact
                    ⟨hCursorAfterInit, hRelInit, by
                      simpa [initSeg, coreSeg, appendSeg,
                        CodeSegment.startPc, CodeSegment.fallthroughPc,
                        CodeSegment.left, CodeSegment.right,
                        CodeSegment.cast_code, hCodeEq, List.append_assoc]
                        using hPcInit⟩)
      refine
        ARunResultWithGasOracle.bind_running
          (program := layout.asm) (oracle := oracle) (cursor := cursor)
          (state := target)
          (middle := fun targetAfterInit targetCursorAfterInit =>
            targetCursorAfterInit = cursorAfterInit ∧
              Frame.StateRel initState targetAfterInit tokens ∧
                targetAfterInit.pc = coreSeg.startPc)
          hInitRegular ?_
      intro targetAfterInit targetCursorAfterInit hAfterInit
      rcases hAfterInit with
        ⟨hTargetCursorAfterInit, hRelAfterInit, hPcAfterInit⟩
      subst targetCursorAfterInit
      have hLoopRun :=
        for_eval_in_programLayout_withGasOracle
          (program := program) (layout := layout) (ctx := ctx)
          (cond := cond) (body := body) (post := post)
          (bodySupply := compiledInit.next) (postSupply := compiledBody.next)
          (loopLabel := loopLabel) (bodyLabel := bodyLabel)
          (postLabel := postLabel) (endLabel := endLabel)
          (maxFuel := maxFuel)
          hCondSafe hCondFrame
          (fun {_bodyFuel} hBodyFuelLt =>
            blockPreservesInProgramLayoutWithGasOracleAtFuel_of_upTo
              hBodyFuelLt hBody)
          (fun {_postFuel} hPostFuelLt =>
            blockPreservesInProgramLayoutWithGasOracleAtFuel_of_upTo
              hPostFuelLt hPost)
          (bodyCode := compiledBody.code) (postCode := compiledPost.code)
          (source := initState) (outcome := outcome)
          (target := targetAfterInit) (tokens := tokens) (oracle := oracle)
          (cursor := cursorAfterInit) (cursorFinal := cursorFinal)
          rfl rfl
          (by omega)
          (by simpa [coreCode] using coreSeg)
          hProgramWF hCtxProcs
          hBodyCalls
          hPostCalls
          hResolve hPcAfterInit hRelAfterInit hLoopEval
      exact
        ARunResultWithGasOracle.mono hLoopRun
          (by
            intro result targetCursorFinal hResult
            simpa [hCoreFallthrough] using hResult)
  | for_init_leave hInitEval =>
      rename_i outState
      have hInitRun :=
        hInit (source := source) (outcome := Outcome.leave outState)
          (target := target) (tokens := tokens) (oracle := oracle)
          (cursor := cursor) (cursorFinal := cursorFinal)
          (by omega) hProgramWF
          (by simpa [loopOuterCtx] using hCtxProcs)
          hInitCalls hLoopOuterResolve initSeg
          hInitPc hRel hInitEval
      exact
        ARunResultWithGasOracle.mono hInitRun
          (by
            intro result targetCursorFinal hResult
            rcases hResult with ⟨hCursorFinal, hCompiled⟩
            cases result with
            | running target' =>
                exact
                  ⟨hCursorFinal, by
                    simpa [loopOuterCtx, CompiledOutcomeRel, Outcome.leave]
                      using hCompiled⟩
            | halted halt =>
                cases hCompiled)
  | for_init_halt hInitEval =>
      rename_i outState kind
      have hInitRun :=
        hInit (source := source) (outcome := Outcome.halt kind outState)
          (target := target) (tokens := tokens) (oracle := oracle)
          (cursor := cursor) (cursorFinal := cursorFinal)
          (by omega) hProgramWF
          (by simpa [loopOuterCtx] using hCtxProcs)
          hInitCalls hLoopOuterResolve initSeg
          hInitPc hRel hInitEval
      exact
        ARunResultWithGasOracle.mono hInitRun
          (by
            intro result targetCursorFinal hResult
            rcases hResult with ⟨hCursorFinal, hCompiled⟩
            cases result with
            | running target' =>
                cases hCompiled
            | halted halt =>
                exact
                  ⟨hCursorFinal, by
                    simpa [loopOuterCtx, CompiledOutcomeRel, Outcome.halt]
                      using hCompiled⟩)

end ProcedureLayoutPreservation

namespace StmtPreservation

theorem code_withGasOracle {program : Program} {ctx : CompileContext}
    {supply : LabelSupply} {code : Code}
    (hSafe : Code.RunnerSafeWithGasOracle code)
    (hFrame : Code.FrameSafeWithGasOracle code) :
    StmtPreservesWithGasOracle program ctx supply (.code code) := by
  intro pre post fuel source outcome target tokens oracle cursor cursorFinal
    hFits _hResolve _hExact hPc hRel hEval
  cases hEval with
  | code hRun =>
      have hCodeFits : Code.PCFitsFrom pre code :=
        Code.PCFitsFrom.of_assembly (by
          simpa [Stmt.compileFromCtxCore] using hFits)
      have hRunCode :=
        FrameStateRel.source_run_code_ctx_result_withGasOracle
          (source := source) (target := target) (tokens := tokens)
          (code := code) (pre := pre) (post := post)
          hSafe hFrame hCodeFits hPc hRel hRun
      exact
        ARunResultWithGasOracle.mono
          (by simpa [Stmt.compileFromCtxCore] using hRunCode)
          (by
            intro result targetCursorFinal hResult
            cases result with
            | halted halt =>
                cases hResult
            | running target' =>
                rcases hResult with ⟨hCursor, hRel', hPc'⟩
                exact
                  ⟨ hCursor
                  , by
                      simpa [Stmt.compileFromCtxCore] using
                        And.intro hRel' hPc'
                  ⟩)

theorem if_withGasOracle {program : Program} {ctx : CompileContext}
    {supply : LabelSupply} {cond : Code} {body : Block}
    (hCondSafe : Code.RunnerSafeWithGasOracle cond)
    (hCondFrame : Code.FrameSafeWithGasOracle cond)
    (hBody :
      BlockPreservesWithGasOracle program ctx (LabelSupply.next supply) body) :
    StmtPreservesWithGasOracle program ctx supply (.if_ cond body) := by
  intro pre post fuel source outcome target tokens oracle cursor cursorFinal
    hFits hResolve hExact hPc hRel hEval
  let bodyLabel := LabelSupply.label supply 0
  let endLabel := LabelSupply.label supply 1
  let compiledBody := Block.compileFromCtx body ctx (LabelSupply.next supply)
  let preAfterJumpi : Assembly.Program :=
    pre ++ cond.toAssembly ++ [Assembly.Instr.jumpi bodyLabel]
  let preBodyLabel : Assembly.Program :=
    pre ++ cond.toAssembly ++
      [Assembly.Instr.jumpi bodyLabel, Assembly.Instr.jump endLabel]
  let preBody : Assembly.Program :=
    pre ++ cond.toAssembly ++
      [ Assembly.Instr.jumpi bodyLabel
      , Assembly.Instr.jump endLabel
      , Assembly.Instr.label bodyLabel
      ]
  let preEndLabel : Assembly.Program :=
    pre ++ cond.toAssembly ++
      [ Assembly.Instr.jumpi bodyLabel
      , Assembly.Instr.jump endLabel
      , Assembly.Instr.label bodyLabel
      ] ++
      compiledBody.code
  have hFitsIf :
      AssemblyProgram.PCFitsFrom pre
        (cond.toAssembly ++
          [ Assembly.Instr.jumpi bodyLabel
          , Assembly.Instr.jump endLabel
          , Assembly.Instr.label bodyLabel
          ] ++
          compiledBody.code ++ [Assembly.Instr.label endLabel]) := by
    simpa [Stmt.compileFromCtxCore, bodyLabel, endLabel, compiledBody]
      using hFits
  have hCondAsmFits :
      AssemblyProgram.PCFitsFrom pre cond.toAssembly :=
    AssemblyProgram.PCFitsFrom.left (pre := pre)
      (first := cond.toAssembly)
      (second :=
        [ Assembly.Instr.jumpi bodyLabel
        , Assembly.Instr.jump endLabel
        , Assembly.Instr.label bodyLabel
        ] ++ compiledBody.code ++ [Assembly.Instr.label endLabel])
      (by simpa [List.append_assoc] using hFitsIf)
  have hCondFits : Code.PCFitsFrom pre cond :=
    Code.PCFitsFrom.of_assembly hCondAsmFits
  have hJumpEndFit : PCFits preAfterJumpi := by
    have hPrefix :
        AssemblyProgram.PCFitsFrom pre
          (cond.toAssembly ++ [Assembly.Instr.jumpi bodyLabel]) :=
      AssemblyProgram.PCFitsFrom.left (pre := pre)
        (first := cond.toAssembly ++ [Assembly.Instr.jumpi bodyLabel])
        (second :=
          [Assembly.Instr.jump endLabel, Assembly.Instr.label bodyLabel] ++
            compiledBody.code ++ [Assembly.Instr.label endLabel])
        (by simpa [List.append_assoc] using hFitsIf)
    simpa [preAfterJumpi, List.append_assoc] using
      AssemblyProgram.PCFitsFrom.end hPrefix
  have hBodyLabelFit : PCFits preBodyLabel := by
    have hPrefix :
        AssemblyProgram.PCFitsFrom pre
          (cond.toAssembly ++
            [Assembly.Instr.jumpi bodyLabel, Assembly.Instr.jump endLabel]) :=
      AssemblyProgram.PCFitsFrom.left (pre := pre)
        (first :=
          cond.toAssembly ++
            [Assembly.Instr.jumpi bodyLabel, Assembly.Instr.jump endLabel])
        (second :=
          [Assembly.Instr.label bodyLabel] ++ compiledBody.code ++
            [Assembly.Instr.label endLabel])
        (by simpa [List.append_assoc] using hFitsIf)
    simpa [preBodyLabel, List.append_assoc] using
      AssemblyProgram.PCFitsFrom.end hPrefix
  have hEndLabelFit : PCFits preEndLabel := by
    have hPrefix :
        AssemblyProgram.PCFitsFrom pre
          (cond.toAssembly ++
            [ Assembly.Instr.jumpi bodyLabel
            , Assembly.Instr.jump endLabel
            , Assembly.Instr.label bodyLabel
            ] ++ compiledBody.code) :=
      AssemblyProgram.PCFitsFrom.left (pre := pre)
        (first :=
          cond.toAssembly ++
            [ Assembly.Instr.jumpi bodyLabel
            , Assembly.Instr.jump endLabel
            , Assembly.Instr.label bodyLabel
            ] ++ compiledBody.code)
        (second := [Assembly.Instr.label endLabel])
        (by simpa [List.append_assoc] using hFitsIf)
    simpa [preEndLabel, List.append_assoc] using
      AssemblyProgram.PCFitsFrom.end hPrefix
  have hBodyFits :
      AssemblyProgram.PCFitsFrom preBody compiledBody.code := by
    have hAfterBodyLabel :
        AssemblyProgram.PCFitsFrom preBody
          (compiledBody.code ++ [Assembly.Instr.label endLabel]) := by
      simpa [preBody, List.append_assoc] using
        AssemblyProgram.PCFitsFrom.right (pre := pre)
          (first :=
            cond.toAssembly ++
              [ Assembly.Instr.jumpi bodyLabel
              , Assembly.Instr.jump endLabel
              , Assembly.Instr.label bodyLabel
              ])
          (second := compiledBody.code ++ [Assembly.Instr.label endLabel])
          (by simpa [List.append_assoc] using hFitsIf)
    exact
      AssemblyProgram.PCFitsFrom.left (pre := preBody)
        (first := compiledBody.code)
        (second := [Assembly.Instr.label endLabel]) hAfterBodyLabel
  have hExactIf :
      ExactLabels
        (pre ++ cond.toAssembly ++
          [ Assembly.Instr.jumpi bodyLabel
          , Assembly.Instr.jump endLabel
          , Assembly.Instr.label bodyLabel
          ] ++
          compiledBody.code ++ [Assembly.Instr.label endLabel] ++ post) := by
    simpa [Stmt.compileFromCtxCore, bodyLabel, endLabel, compiledBody,
      List.append_assoc] using hExact
  have hBodyLabel :
      Assembly.Program.labelPc
          (pre ++ cond.toAssembly ++
            [Assembly.Instr.jumpi bodyLabel] ++
            ([Assembly.Instr.jump endLabel, Assembly.Instr.label bodyLabel] ++
              compiledBody.code ++ [Assembly.Instr.label endLabel] ++ post))
          bodyLabel =
        some (Assembly.Program.byteLength preBodyLabel) := by
    have hHere :=
      hExactIf.labelPc_at preBodyLabel bodyLabel
        (compiledBody.code ++ [Assembly.Instr.label endLabel] ++ post)
        (by simp [preBodyLabel, List.append_assoc])
    simpa [preBodyLabel, List.append_assoc] using hHere
  have hEndLabel :
      Assembly.Program.labelPc
          (preAfterJumpi ++ [Assembly.Instr.jump endLabel] ++
            ([Assembly.Instr.label bodyLabel] ++ compiledBody.code) ++
            [Assembly.Instr.label endLabel] ++ post)
          endLabel =
        some (Assembly.Program.byteLength preEndLabel) := by
    have hHere :=
      hExactIf.labelPc_at preEndLabel endLabel post
        (by simp [preEndLabel, List.append_assoc])
    simpa [preAfterJumpi, preEndLabel, List.append_assoc] using hHere
  have hBodyResolve :
      ContextLabelsResolve (preBody ++ compiledBody.code ++
        ([Assembly.Instr.label endLabel] ++ post)) ctx := by
    simpa [Stmt.compileFromCtxCore, bodyLabel, endLabel, compiledBody,
      preBody, List.append_assoc] using hResolve
  have hBodyExact :
      ExactLabels (preBody ++ compiledBody.code ++
        ([Assembly.Instr.label endLabel] ++ post)) := by
    simpa [Stmt.compileFromCtxCore, bodyLabel, endLabel, compiledBody,
      preBody, List.append_assoc] using hExact
  cases hEval with
  | if_false hCondRun =>
      rename_i stateAfterCond
      have hCondJump :=
        FrameStateRel.runCondition_jumpi_result_ctx_withGasOracle
          (cond := cond) (label := bodyLabel)
          (dest := Assembly.Program.byteLength preBodyLabel)
          (pre := pre)
          (post :=
            [Assembly.Instr.jump endLabel, Assembly.Instr.label bodyLabel] ++
              compiledBody.code ++ [Assembly.Instr.label endLabel] ++ post)
          (oracle := oracle) (cursor := cursor)
          hCondSafe hCondFrame hCondFits hPc hRel hBodyLabel hCondRun
      have hCondFalse :
          ARunResultWithGasOracle
            (pre ++
              (Stmt.compileFromCtxCore (.if_ cond body) ctx supply).code ++
                post)
            oracle cursor target
            (fun result targetCursorAfterCond =>
              match result with
              | .running targetAfterCond =>
                  targetCursorAfterCond = cursorFinal ∧
                    Frame.StateRel stateAfterCond targetAfterCond tokens ∧
                      targetAfterCond.pc =
                        Assembly.Program.pcAfter preAfterJumpi
              | .halted _ => False) := by
        exact ARunResultWithGasOracle.mono
          (by
            simpa [Stmt.compileFromCtxCore, bodyLabel, endLabel, compiledBody,
              preAfterJumpi, List.append_assoc] using hCondJump)
          (by
            intro result targetCursorAfterCond hResult
            cases result with
            | halted halt =>
                cases hResult
            | running targetAfterCond =>
                simpa [preAfterJumpi] using hResult)
      refine
        ARunResultWithGasOracle.bind_running
          (program :=
            pre ++
              (Stmt.compileFromCtxCore (.if_ cond body) ctx supply).code ++
                post)
          (middle := fun targetAfterCond targetCursorAfterCond =>
            targetCursorAfterCond = cursorFinal ∧
              Frame.StateRel stateAfterCond targetAfterCond tokens ∧
                targetAfterCond.pc = Assembly.Program.pcAfter preAfterJumpi)
          hCondFalse ?_
      intro targetAfterCond targetCursorAfterCond hAfterCond
      rcases hAfterCond with
        ⟨hTargetCursorAfterCond, hRelAfterCond, hPcAfterCond⟩
      subst targetCursorAfterCond
      have hJumpEnd :=
        FrameStateRel.jump_then_label_runResult_at_withGasOracle
          (label := endLabel) (pre := preAfterJumpi)
          (between := [Assembly.Instr.label bodyLabel] ++ compiledBody.code)
          (post := post) (oracle := oracle) (cursor := cursorFinal)
          hJumpEndFit
          (by simpa [preAfterJumpi, preEndLabel, List.append_assoc]
            using hEndLabelFit)
          hPcAfterCond hRelAfterCond
          (by simpa [preAfterJumpi, preEndLabel, List.append_assoc]
            using hEndLabel)
      exact ARunResultWithGasOracle.mono
        (by
          simpa [Stmt.compileFromCtxCore, bodyLabel, endLabel, compiledBody,
            preAfterJumpi, preEndLabel, List.append_assoc] using hJumpEnd)
        (by
          intro result targetCursorFinal hResult
          cases result with
          | halted halt =>
              cases hResult
          | running targetFinal =>
              rcases hResult with ⟨hCursor, hTargetRel, hTargetPc⟩
              exact
                ⟨ hCursor
                , by
                    simpa [Stmt.compileFromCtxCore, bodyLabel, endLabel,
                      compiledBody, preAfterJumpi, preEndLabel,
                      CompiledOutcomeRel, Outcome.regular, List.append_assoc]
                      using And.intro hTargetRel hTargetPc
                ⟩)
  | if_true hCondRun hBodyEval =>
      rename_i cursorAfterCond stateAfterCond
      have hCondJump :=
        FrameStateRel.runCondition_jumpi_result_ctx_withGasOracle
          (cond := cond) (label := bodyLabel)
          (dest := Assembly.Program.byteLength preBodyLabel)
          (pre := pre)
          (post :=
            [Assembly.Instr.jump endLabel, Assembly.Instr.label bodyLabel] ++
              compiledBody.code ++ [Assembly.Instr.label endLabel] ++ post)
          (oracle := oracle) (cursor := cursor)
          hCondSafe hCondFrame hCondFits hPc hRel hBodyLabel hCondRun
      have hCondTrue :
          ARunResultWithGasOracle
            (pre ++
              (Stmt.compileFromCtxCore (.if_ cond body) ctx supply).code ++
                post)
            oracle cursor target
            (fun result targetCursorAfterCond =>
              match result with
              | .running targetAfterCond =>
                  targetCursorAfterCond = cursorAfterCond ∧
                    Frame.StateRel stateAfterCond targetAfterCond tokens ∧
                      targetAfterCond.pc =
                        Assembly.Program.pcAfter preBodyLabel
              | .halted _ => False) := by
        exact ARunResultWithGasOracle.mono
          (by
            simpa [Stmt.compileFromCtxCore, bodyLabel, endLabel, compiledBody,
              preBodyLabel, List.append_assoc] using hCondJump)
          (by
            intro result targetCursorAfterCond hResult
            cases result with
            | halted halt =>
                cases hResult
            | running targetAfterCond =>
                simpa [preBodyLabel] using hResult)
      refine
        ARunResultWithGasOracle.bind_running
          (program :=
            pre ++
              (Stmt.compileFromCtxCore (.if_ cond body) ctx supply).code ++
                post)
          (middle := fun targetAfterCond targetCursorAfterCond =>
            targetCursorAfterCond = cursorAfterCond ∧
              Frame.StateRel stateAfterCond targetAfterCond tokens ∧
                targetAfterCond.pc = Assembly.Program.pcAfter preBodyLabel)
          hCondTrue ?_
      intro targetAfterCond targetCursorAfterCond hAfterCond
      rcases hAfterCond with
        ⟨hTargetCursorAfterCond, hRelAfterCond, hPcAfterCond⟩
      subst targetCursorAfterCond
      have hBodyLabelRun :=
        FrameStateRel.label_runResult_at_withGasOracle
          (label := bodyLabel) (pre := preBodyLabel)
          (post := compiledBody.code ++ [Assembly.Instr.label endLabel] ++ post)
          (oracle := oracle) (cursor := cursorAfterCond)
          hBodyLabelFit hPcAfterCond hRelAfterCond
      refine
        ARunResultWithGasOracle.bind_running
          (program :=
            pre ++
              (Stmt.compileFromCtxCore (.if_ cond body) ctx supply).code ++
                post)
          (middle := fun targetAtBody targetCursorAtBody =>
            targetCursorAtBody = cursorAfterCond ∧
              Frame.StateRel stateAfterCond targetAtBody tokens ∧
                targetAtBody.pc = Assembly.Program.pcAfter preBody)
          ?_ ?_
      · exact ARunResultWithGasOracle.mono
          (by
            simpa [Stmt.compileFromCtxCore, bodyLabel, endLabel, compiledBody,
              preBodyLabel, preBody, List.append_assoc] using hBodyLabelRun)
          (by
            intro result targetCursorAtBody hResult
            cases result with
            | halted halt =>
                cases hResult
            | running targetAtBody =>
                simpa [preBody] using hResult)
      · intro targetAtBody targetCursorAtBody hAtBody
        rcases hAtBody with ⟨hCursorAtBody, hRelAtBody, hPcAtBody⟩
        subst targetCursorAtBody
        have hBodyRun :=
          hBody (pre := preBody)
            (post := [Assembly.Instr.label endLabel] ++ post)
            (source := stateAfterCond) (outcome := outcome)
            (target := targetAtBody) (tokens := tokens)
            (oracle := oracle) (cursor := cursorAfterCond)
            (cursorFinal := cursorFinal)
            hBodyFits hBodyResolve hBodyExact hPcAtBody hRelAtBody hBodyEval
        cases outcome with
        | mk outState outMode =>
            cases outMode with
            | regular =>
                have hBodyRegular :
                    ARunResultWithGasOracle
                      (preBody ++ compiledBody.code ++
                        ([Assembly.Instr.label endLabel] ++ post))
                      oracle cursorAfterCond targetAtBody
                      (fun result targetCursorBeforeEnd =>
                        match result with
                        | .running targetBeforeEnd =>
                            targetCursorBeforeEnd = cursorFinal ∧
                              Frame.StateRel outState targetBeforeEnd tokens ∧
                                targetBeforeEnd.pc =
                                  Assembly.Program.pcAfter
                                    (preBody ++ compiledBody.code)
                        | .halted _ => False) := by
                  exact ARunResultWithGasOracle.mono hBodyRun (by
                    intro result targetCursorBeforeEnd hResult
                    cases result with
                    | halted halt =>
                        cases hResult.2
                    | running targetBeforeEnd =>
                        rcases hResult with ⟨hCursorEnd, hCompiled⟩
                        exact
                          ⟨ hCursorEnd
                          , by
                              simpa [CompiledOutcomeRel, Outcome.regular,
                                preEndLabel, List.append_assoc]
                                using hCompiled
                          ⟩)
                refine
                  ARunResultWithGasOracle.bind_running
                    (program :=
                      pre ++
                        (Stmt.compileFromCtxCore (.if_ cond body) ctx supply).code ++
                          post)
                    (middle := fun targetBeforeEnd targetCursorBeforeEnd =>
                      targetCursorBeforeEnd = cursorFinal ∧
                        Frame.StateRel outState targetBeforeEnd tokens ∧
                          targetBeforeEnd.pc =
                            Assembly.Program.pcAfter
                              (preBody ++ compiledBody.code))
                    ?_ ?_
                · simpa [Stmt.compileFromCtxCore, bodyLabel, endLabel,
                    compiledBody, preBody, List.append_assoc]
                    using hBodyRegular
                · intro targetBeforeEnd targetCursorBeforeEnd hBeforeEnd
                  rcases hBeforeEnd with
                    ⟨hCursorBeforeEnd, hRelBeforeEnd, hPcBeforeEnd⟩
                  subst targetCursorBeforeEnd
                  have hEndRun :=
                    FrameStateRel.label_runResult_at_withGasOracle
                      (label := endLabel) (pre := preEndLabel) (post := post)
                      (oracle := oracle) (cursor := cursorFinal)
                      hEndLabelFit
                      (by
                        simpa [preEndLabel, preBody, List.append_assoc]
                          using hPcBeforeEnd)
                      hRelBeforeEnd
                  exact ARunResultWithGasOracle.mono
                    (by
                      simpa [Stmt.compileFromCtxCore, bodyLabel, endLabel,
                        compiledBody, preEndLabel, List.append_assoc]
                        using hEndRun)
                    (by
                      intro result targetCursorFinal hResult
                      cases result with
                      | halted halt =>
                          cases hResult
                      | running targetFinal =>
                          rcases hResult with ⟨hCursor, hTargetRel, hTargetPc⟩
                          exact
                            ⟨ hCursor
                            , by
                                simpa [Stmt.compileFromCtxCore, bodyLabel,
                                  endLabel, compiledBody, preEndLabel,
                                  CompiledOutcomeRel, Outcome.regular,
                                  List.append_assoc]
                                  using And.intro hTargetRel hTargetPc
                            ⟩)
            | brk =>
                exact ARunResultWithGasOracle.mono
                  (by
                    simpa [Stmt.compileFromCtxCore, bodyLabel, endLabel,
                      compiledBody, preBody, List.append_assoc] using hBodyRun)
                  (by
                    intro result targetCursor hResult
                    rcases hResult with ⟨hCursor, hCompiled⟩
                    cases result with
                    | halted halt =>
                        cases hCompiled
                    | running target' =>
                        rcases hCompiled with
                          ⟨label, dest, hCtxBrk, hLabelPc, hTargetRel,
                            hTargetPc⟩
                        exact
                          ⟨ hCursor
                          , label, dest, hCtxBrk
                          , by
                              simpa [Stmt.compileFromCtxCore, bodyLabel,
                                endLabel, compiledBody, preBody,
                                List.append_assoc] using hLabelPc
                          , hTargetRel, hTargetPc
                          ⟩)
            | cont =>
                exact ARunResultWithGasOracle.mono
                  (by
                    simpa [Stmt.compileFromCtxCore, bodyLabel, endLabel,
                      compiledBody, preBody, List.append_assoc] using hBodyRun)
                  (by
                    intro result targetCursor hResult
                    rcases hResult with ⟨hCursor, hCompiled⟩
                    cases result with
                    | halted halt =>
                        cases hCompiled
                    | running target' =>
                        rcases hCompiled with
                          ⟨label, dest, hCtxCont, hLabelPc, hTargetRel,
                            hTargetPc⟩
                        exact
                          ⟨ hCursor
                          , label, dest, hCtxCont
                          , by
                              simpa [Stmt.compileFromCtxCore, bodyLabel,
                                endLabel, compiledBody, preBody,
                                List.append_assoc] using hLabelPc
                          , hTargetRel, hTargetPc
                          ⟩)
            | leave =>
                exact ARunResultWithGasOracle.mono
                  (by
                    simpa [Stmt.compileFromCtxCore, bodyLabel, endLabel,
                      compiledBody, preBody, List.append_assoc] using hBodyRun)
                  (by
                    intro result targetCursor hResult
                    rcases hResult with ⟨hCursor, hCompiled⟩
                    cases result with
                    | halted halt =>
                        cases hCompiled
                    | running target' =>
                        rcases hCompiled with
                          ⟨label, dest, hCtxLeave, hLabelPc, hTargetRel,
                            hTargetPc⟩
                        exact
                          ⟨ hCursor
                          , label, dest, hCtxLeave
                          , by
                              simpa [Stmt.compileFromCtxCore, bodyLabel,
                                endLabel, compiledBody, preBody,
                                List.append_assoc] using hLabelPc
                          , hTargetRel, hTargetPc
                          ⟩)
            | halt kind =>
                exact ARunResultWithGasOracle.mono
                  (by
                    simpa [Stmt.compileFromCtxCore, bodyLabel, endLabel,
                      compiledBody, preBody, List.append_assoc] using hBodyRun)
                  (by
                    intro result targetCursor hResult
                    rcases hResult with ⟨hCursor, hCompiled⟩
                    cases result with
                    | running target' =>
                        cases hCompiled
                    | halted halt =>
                        rcases hCompiled with
                          ⟨hKind, haltedTokens, hTargetRel⟩
                        exact ⟨hCursor, hKind, haltedTokens, hTargetRel⟩)

theorem switch_withGasOracle {program : Program} {ctx : CompileContext}
    {supply : LabelSupply} {scrutinee : Code}
    {cases : List (Word × Block)} {defaultBody : Option Block}
    (hScrutineeSafe : Code.RunnerSafeWithGasOracle scrutinee)
    (hScrutineeFrame : Code.FrameSafeWithGasOracle scrutinee)
    (hCases :
      SwitchPreservation.CasesPreserves program ctx
        (LabelSupply.label supply 0) supply (LabelSupply.next supply) 0 cases)
    (hDefault :
      SwitchPreservation.DefaultPreserves program ctx
        (SwitchCases.compileFromCtx cases ctx (LabelSupply.label supply 0)
          supply (LabelSupply.next supply) 0).next
        defaultBody) :
    StmtPreservesWithGasOracle program ctx supply
      (.switch scrutinee cases defaultBody) := by
  intro pre post fuel source outcome target tokens oracle cursor cursorFinal
    hFits hResolve hExact hPc hRel hEval
  let endLabel := LabelSupply.label supply 0
  let defaultLabel := LabelSupply.label supply 1
  let compiledCases :=
    SwitchCases.compileFromCtx cases ctx endLabel supply
      (LabelSupply.next supply) 0
  let compiledDefault :=
    SwitchDefault.compileFromCtx defaultBody ctx endLabel defaultLabel
      compiledCases.next
  let preTests : Assembly.Program := pre ++ scrutinee.toAssembly
  have hFitsSwitch :
      AssemblyProgram.PCFitsFrom pre
        (scrutinee.toAssembly ++
          Stmt.switchTests supply 0 cases ++
          [Assembly.Instr.jump defaultLabel] ++
          compiledCases.code ++ compiledDefault.code ++
          [Assembly.Instr.label endLabel]) := by
    simpa [Stmt.compileFromCtxCore, endLabel, defaultLabel, compiledCases,
      compiledDefault, List.append_assoc] using hFits
  have hScrutineeFitsAsm :
      AssemblyProgram.PCFitsFrom pre scrutinee.toAssembly :=
    AssemblyProgram.PCFitsFrom.left (pre := pre)
      (first := scrutinee.toAssembly)
      (second :=
        Stmt.switchTests supply 0 cases ++
          [Assembly.Instr.jump defaultLabel] ++
          compiledCases.code ++ compiledDefault.code ++
          [Assembly.Instr.label endLabel])
      (by simpa [List.append_assoc] using hFitsSwitch)
  have hScrutineeFits : Code.PCFitsFrom pre scrutinee :=
    Code.PCFitsFrom.of_assembly hScrutineeFitsAsm
  have hAfterScrutineeFits :
      AssemblyProgram.PCFitsFrom preTests
        (Stmt.switchTests supply 0 cases ++
          [Assembly.Instr.jump defaultLabel] ++
          compiledCases.code ++ compiledDefault.code ++
          [Assembly.Instr.label endLabel]) := by
    simpa [preTests, List.append_assoc] using
      AssemblyProgram.PCFitsFrom.right (pre := pre)
        (first := scrutinee.toAssembly)
        (second :=
          Stmt.switchTests supply 0 cases ++
            [Assembly.Instr.jump defaultLabel] ++
            compiledCases.code ++ compiledDefault.code ++
            [Assembly.Instr.label endLabel])
        (by simpa [List.append_assoc] using hFitsSwitch)
  have hAfterScrutineeResolve :
      ContextLabelsResolve
        (preTests ++
          (Stmt.switchTests supply 0 cases ++
            [Assembly.Instr.jump defaultLabel] ++
            compiledCases.code ++ compiledDefault.code ++
            [Assembly.Instr.label endLabel]) ++ post)
        ctx := by
    simpa [Stmt.compileFromCtxCore, endLabel, defaultLabel, compiledCases,
      compiledDefault, preTests, List.append_assoc] using hResolve
  have hAfterScrutineeExact :
      ExactLabels
        (preTests ++
          (Stmt.switchTests supply 0 cases ++
            [Assembly.Instr.jump defaultLabel] ++
            compiledCases.code ++ compiledDefault.code ++
            [Assembly.Instr.label endLabel]) ++ post) := by
    simpa [Stmt.compileFromCtxCore, endLabel, defaultLabel, compiledCases,
      compiledDefault, preTests, List.append_assoc] using hExact
  cases hEval with
  | switch_none hScrutinee hPop hSelect =>
      exact
        SwitchPreservation.switch_none_result_ctx_withGasOracle
          (ctx := ctx) (supply := supply) (scrutinee := scrutinee)
          (cases := cases) (defaultBody := defaultBody)
          (source := source) (stateAfterScrutinee := _)
          (target := target) (tokens := tokens)
          (stack := _) (value := _) (pre := pre) (post := post)
          (oracle := oracle) (cursor := cursor)
          (cursorAfterScrutinee := cursorFinal)
          hScrutineeSafe hScrutineeFrame hFits hExact hPc hRel
          hScrutinee hPop hSelect
  | switch_some hScrutinee hPop hStateAfterPop hSelect hBodyEval =>
      rename_i cursorAfterScrutinee stateAfterScrutinee stateAfterPop stack value body
      subst stateAfterPop
      have hScrutineeRun :
          ARunResultWithGasOracle
            (pre ++
              (Stmt.compileFromCtxCore
                (.switch scrutinee cases defaultBody) ctx supply).code ++ post)
            oracle cursor target
            (fun result targetCursorAfterScrutinee =>
              match result with
              | .running targetAfterScrutinee =>
                  targetCursorAfterScrutinee = cursorAfterScrutinee ∧
                    Frame.StateRel stateAfterScrutinee targetAfterScrutinee
                      tokens ∧
                      targetAfterScrutinee.pc =
                        Assembly.Program.pcAfter preTests
              | .halted _ => False) := by
        have hRun :=
          FrameStateRel.source_run_code_ctx_result_withGasOracle
            (source := source) (final := stateAfterScrutinee)
            (target := target) (tokens := tokens) (code := scrutinee)
            (pre := pre)
            (post :=
              Stmt.switchTests supply 0 cases ++
                [Assembly.Instr.jump defaultLabel] ++
                compiledCases.code ++ compiledDefault.code ++
                [Assembly.Instr.label endLabel] ++ post)
            hScrutineeSafe hScrutineeFrame hScrutineeFits hPc hRel
            hScrutinee
        simpa [Stmt.compileFromCtxCore, endLabel, defaultLabel, compiledCases,
          compiledDefault, preTests, List.append_assoc] using hRun
      refine
        ARunResultWithGasOracle.bind_running
          (program :=
            pre ++
              (Stmt.compileFromCtxCore
                (.switch scrutinee cases defaultBody) ctx supply).code ++ post)
          (middle := fun targetAfterScrutinee targetCursorAfterScrutinee =>
            targetCursorAfterScrutinee = cursorAfterScrutinee ∧
              Frame.StateRel stateAfterScrutinee targetAfterScrutinee tokens ∧
                targetAfterScrutinee.pc = Assembly.Program.pcAfter preTests)
          hScrutineeRun ?_
      intro targetAfterScrutinee targetCursorAfterScrutinee hAfterScrutinee
      rcases hAfterScrutinee with
        ⟨hTargetCursorAfterScrutinee, hRelAfterScrutinee,
          hPcAfterScrutinee⟩
      subst targetCursorAfterScrutinee
      have hSelected :=
        SwitchPreservation.selected_cases_result_ctx_withGasOracle
          (program := program) (ctx := ctx) (base := supply)
          (supply := LabelSupply.next supply) (idx := 0)
          (cases := cases) (defaultBody := defaultBody)
          (selected := body)
          (pre := preTests) (casePrefix := []) (post := post)
          (defaultLabel := defaultLabel) (endLabel := endLabel)
          (source := stateAfterScrutinee)
          (outcome := outcome) (target := targetAfterScrutinee)
          (tokens := tokens) (stack := stack) (value := value)
          (oracle := oracle) (cursor := cursorAfterScrutinee)
          (cursorFinal := cursorFinal)
          (by simpa [endLabel] using hCases)
          (by simpa [endLabel, compiledCases] using hDefault)
          (by
            simpa [compiledCases, compiledDefault, List.append_assoc]
              using hAfterScrutineeFits)
          (by
            simpa [compiledCases, compiledDefault, List.append_assoc]
              using hAfterScrutineeResolve)
          (by
            simpa [compiledCases, compiledDefault, List.append_assoc]
              using hAfterScrutineeExact)
          hPcAfterScrutinee hRelAfterScrutinee hPop hSelect hBodyEval
      exact
        ARunResultWithGasOracle.mono
          (by
            simpa [Stmt.compileFromCtxCore, endLabel, defaultLabel,
              compiledCases, compiledDefault, preTests, List.append_assoc]
              using hSelected)
          (by
            intro result targetCursorFinal hResult
            simpa [Stmt.compileFromCtxCore, endLabel, defaultLabel,
              compiledCases, compiledDefault, preTests, List.append_assoc]
              using hResult)

theorem for_withGasOracle {program : Program} {ctx : CompileContext}
    {supply : LabelSupply} {init post body : Block} {cond : Code}
    (hCondSafe : Code.RunnerSafeWithGasOracle cond)
    (hCondFrame : Code.FrameSafeWithGasOracle cond)
    (hInit :
      BlockPreservesWithGasOracle program
        { ctx with breakLabel? := none, continueLabel? := none }
        (LabelSupply.next supply) init)
    (hBody :
      BlockPreservesWithGasOracle program
        { ctx with
          breakLabel? := some (LabelSupply.label supply 3)
          continueLabel? := some (LabelSupply.label supply 2) }
        (Block.compileFromCtx init
          { ctx with breakLabel? := none, continueLabel? := none }
          (LabelSupply.next supply)).next
        body)
    (hPost :
      BlockPreservesWithGasOracle program
        { ctx with breakLabel? := none, continueLabel? := none }
        (Block.compileFromCtx body
          { ctx with
            breakLabel? := some (LabelSupply.label supply 3)
            continueLabel? := some (LabelSupply.label supply 2) }
          (Block.compileFromCtx init
            { ctx with breakLabel? := none, continueLabel? := none }
            (LabelSupply.next supply)).next).next
        post) :
    StmtPreservesWithGasOracle program ctx supply (.for_ init cond post body) := by
  intro pre suffix fuel source outcome target tokens oracle cursor cursorFinal
    hFits hResolve hExact hPc hRel hEval
  let loopLabel := LabelSupply.label supply 0
  let bodyLabel := LabelSupply.label supply 1
  let postLabel := LabelSupply.label supply 2
  let endLabel := LabelSupply.label supply 3
  let loopOuterCtx : CompileContext :=
    { ctx with breakLabel? := none, continueLabel? := none }
  let compiledInit :=
    Block.compileFromCtx init loopOuterCtx (LabelSupply.next supply)
  let bodyCtx : CompileContext :=
    { ctx with
      breakLabel? := some endLabel
      continueLabel? := some postLabel }
  let compiledBody := Block.compileFromCtx body bodyCtx compiledInit.next
  let compiledPost := Block.compileFromCtx post loopOuterCtx compiledBody.next
  let coreCode :=
    ForLoop.coreCode cond compiledBody.code compiledPost.code loopLabel
      bodyLabel postLabel endLabel
  let preAfterInit := pre ++ compiledInit.code
  have hForFits :
      AssemblyProgram.PCFitsFrom pre (compiledInit.code ++ coreCode) := by
    simpa [Stmt.compileFromCtxCore, loopLabel, bodyLabel, postLabel, endLabel,
      loopOuterCtx, bodyCtx, compiledInit, compiledBody, compiledPost, coreCode,
      ForLoop.coreCode, List.append_assoc] using hFits
  have hInitFits :
      AssemblyProgram.PCFitsFrom pre compiledInit.code :=
    AssemblyProgram.PCFitsFrom.left (pre := pre) (first := compiledInit.code)
      (second := coreCode) hForFits
  have hCoreFits :
      AssemblyProgram.PCFitsFrom preAfterInit coreCode := by
    simpa [preAfterInit] using
      AssemblyProgram.PCFitsFrom.right (pre := pre)
        (first := compiledInit.code) (second := coreCode) hForFits
  have hLoopExact :
      ExactLabels (preAfterInit ++ coreCode ++ suffix) := by
    simpa [Stmt.compileFromCtxCore, loopLabel, bodyLabel, postLabel, endLabel,
      loopOuterCtx, bodyCtx, compiledInit, compiledBody, compiledPost, coreCode,
      preAfterInit, ForLoop.coreCode, List.append_assoc] using hExact
  have hLayout :
      ForLoop.Layout preAfterInit suffix cond compiledBody.code
        compiledPost.code loopLabel bodyLabel postLabel endLabel :=
    ForLoop.Layout.of_fits_exact
      (pre := preAfterInit) (suffix := suffix) (cond := cond)
      (bodyCode := compiledBody.code) (postCode := compiledPost.code)
      (loopLabel := loopLabel) (bodyLabel := bodyLabel)
      (postLabel := postLabel) (endLabel := endLabel)
      (by simpa [coreCode] using hCoreFits)
      (by simpa [coreCode] using hLoopExact)
  have hOuterResolveFull :
      ContextLabelsResolve
        (pre ++ compiledInit.code ++ coreCode ++ suffix)
        loopOuterCtx :=
    ContextLabelsResolve.without_break_continue
      (ctx := ctx)
      (by
        simpa [Stmt.compileFromCtxCore, loopLabel, bodyLabel, postLabel,
          endLabel, loopOuterCtx, bodyCtx, compiledInit, compiledBody,
          compiledPost, coreCode, ForLoop.coreCode, List.append_assoc]
          using hResolve)
  have hInitResolve :
      ContextLabelsResolve (pre ++ compiledInit.code ++ (coreCode ++ suffix))
        loopOuterCtx := by
    simpa [List.append_assoc] using hOuterResolveFull
  have hInitExact :
      ExactLabels (pre ++ compiledInit.code ++ (coreCode ++ suffix)) := by
    simpa [Stmt.compileFromCtxCore, loopLabel, bodyLabel, postLabel, endLabel,
      loopOuterCtx, bodyCtx, compiledInit, compiledBody, compiledPost, coreCode,
      ForLoop.coreCode, List.append_assoc] using hExact
  have hCoreResolve :
      ContextLabelsResolve (preAfterInit ++ coreCode ++ suffix) ctx := by
    simpa [Stmt.compileFromCtxCore, loopLabel, bodyLabel, postLabel, endLabel,
      loopOuterCtx, bodyCtx, compiledInit, compiledBody, compiledPost, coreCode,
      preAfterInit, ForLoop.coreCode, List.append_assoc] using hResolve
  cases hEval with
  | for_init_regular hInitEval hLoopEval =>
      rename_i cursorAfterInit initState
      have hInitRun :=
        hInit (pre := pre) (post := coreCode ++ suffix)
          (source := source)
          (outcome := Outcome.regular initState) (target := target)
          (tokens := tokens) (oracle := oracle) (cursor := cursor)
          (cursorFinal := cursorAfterInit)
          hInitFits hInitResolve hInitExact hPc hRel hInitEval
      have hInitRegular :
          ARunResultWithGasOracle
            (pre ++ compiledInit.code ++ (coreCode ++ suffix))
            oracle cursor target
            (fun result targetCursorAfterInit =>
              match result with
              | .running targetAfterInit =>
                  targetCursorAfterInit = cursorAfterInit ∧
                    Frame.StateRel initState targetAfterInit tokens ∧
                      targetAfterInit.pc =
                        Assembly.Program.pcAfter preAfterInit
              | .halted _ => False) := by
        exact ARunResultWithGasOracle.mono hInitRun (by
          intro result targetCursorAfterInit hResult
          rcases hResult with ⟨hCursorAfterInit, hCompiled⟩
          cases result with
          | halted halt =>
              cases hCompiled
          | running targetAfterInit =>
              exact
                ⟨ hCursorAfterInit
                , by
                    simpa [loopOuterCtx, compiledInit, preAfterInit,
                      CompiledOutcomeRel, Outcome.regular, List.append_assoc]
                      using hCompiled
                ⟩)
      refine
        ARunResultWithGasOracle.bind_running
          (program :=
            pre ++
              (Stmt.compileFromCtxCore (.for_ init cond post body) ctx supply).code ++
                suffix)
          (middle := fun targetAfterInit targetCursorAfterInit =>
            targetCursorAfterInit = cursorAfterInit ∧
              Frame.StateRel initState targetAfterInit tokens ∧
                targetAfterInit.pc = Assembly.Program.pcAfter preAfterInit)
          ?_ ?_
      · simpa [Stmt.compileFromCtxCore, loopLabel, bodyLabel, postLabel,
          endLabel, loopOuterCtx, bodyCtx, compiledInit, compiledBody,
          compiledPost, coreCode, ForLoop.coreCode, List.append_assoc]
          using hInitRegular
      · intro targetAfterInit targetCursorAfterInit hAfterInit
        rcases hAfterInit with
          ⟨hTargetCursorAfterInit, hRelAfterInit, hPcAfterInit⟩
        subst targetCursorAfterInit
        have hLoopRun :=
          ForLoopPreservation.preserves_eval_withGasOracle
            (program := program) (ctx := ctx) (cond := cond)
            (body := body) (post := post)
            (bodySupply := compiledInit.next) (postSupply := compiledBody.next)
            (loopLabel := loopLabel) (bodyLabel := bodyLabel)
            (postLabel := postLabel) (endLabel := endLabel)
            hCondSafe hCondFrame
            (by
              change BlockPreservesWithGasOracle program bodyCtx
                compiledInit.next body
              exact hBody)
            (by
              change BlockPreservesWithGasOracle program loopOuterCtx
                compiledBody.next post
              exact hPost)
            hLayout
            (by simpa [coreCode] using hCoreResolve)
            (by simpa [coreCode] using hLoopExact)
            hPcAfterInit hRelAfterInit hLoopEval
        simpa [Stmt.compileFromCtxCore, loopLabel, bodyLabel, postLabel,
          endLabel, loopOuterCtx, bodyCtx, compiledInit, compiledBody,
          compiledPost, coreCode, preAfterInit, ForLoop.coreCode,
          List.append_assoc] using hLoopRun
  | for_init_leave hInitEval =>
      rename_i outState
      have hInitRun :=
        hInit (pre := pre) (post := coreCode ++ suffix)
          (source := source)
          (outcome := Outcome.leave outState) (target := target)
          (tokens := tokens) (oracle := oracle) (cursor := cursor)
          (cursorFinal := cursorFinal)
          hInitFits hInitResolve hInitExact hPc hRel hInitEval
      exact ARunResultWithGasOracle.mono
        (by
          simpa [Stmt.compileFromCtxCore, loopLabel, bodyLabel, postLabel,
            endLabel, loopOuterCtx, bodyCtx, compiledInit, compiledBody,
            compiledPost, coreCode, ForLoop.coreCode, List.append_assoc]
            using hInitRun)
        (by
          intro result targetCursorFinal hResult
          rcases hResult with ⟨hCursorFinal, hCompiled⟩
          cases result with
          | halted halt =>
              cases hCompiled
          | running target' =>
              exact
                ⟨ hCursorFinal
                , by
                    simpa [Stmt.compileFromCtxCore, loopLabel, bodyLabel,
                      postLabel, endLabel, loopOuterCtx, bodyCtx, compiledInit,
                      compiledBody, compiledPost, coreCode, CompiledOutcomeRel,
                      Outcome.leave, List.append_assoc] using hCompiled
                ⟩)
  | for_init_halt hInitEval =>
      rename_i outState kind
      have hInitRun :=
        hInit (pre := pre) (post := coreCode ++ suffix)
          (source := source)
          (outcome := Outcome.halt kind outState) (target := target)
          (tokens := tokens) (oracle := oracle) (cursor := cursor)
          (cursorFinal := cursorFinal)
          hInitFits hInitResolve hInitExact hPc hRel hInitEval
      exact ARunResultWithGasOracle.mono
        (by
          simpa [Stmt.compileFromCtxCore, loopLabel, bodyLabel, postLabel,
            endLabel, loopOuterCtx, bodyCtx, compiledInit, compiledBody,
            compiledPost, coreCode, ForLoop.coreCode, List.append_assoc]
            using hInitRun)
        (by
          intro result targetCursorFinal hResult
          rcases hResult with ⟨hCursorFinal, hCompiled⟩
          cases result with
          | running target' =>
              cases hCompiled
          | halted halt =>
              exact
                ⟨ hCursorFinal
                , by
                    simpa [Stmt.compileFromCtxCore, loopLabel, bodyLabel,
                      postLabel, endLabel, loopOuterCtx, bodyCtx, compiledInit,
                      compiledBody, compiledPost, coreCode, CompiledOutcomeRel,
                      Outcome.halt, List.append_assoc] using hCompiled
                ⟩)

theorem brk_withGasOracle {program : Program} {ctx : CompileContext}
    {supply : LabelSupply} {label : Assembly.Label}
    (hCtx : ctx.breakLabel? = some label) :
    StmtPreservesWithGasOracle program ctx supply .brk := by
  intro pre post fuel source outcome target tokens oracle cursor cursorFinal
    hFits hResolve _hExact hPc hRel hEval
  cases hEval
  rcases hResolve.brk label hCtx with ⟨dest, hLabel⟩
  rcases
    FrameStateRel.jump_stepResult_at_withGasOracle
      (label := label) (dest := dest) (pre := pre) (post := post)
      (oracle := oracle) (cursor := cursor)
      (AssemblyProgram.PCFitsFrom.start hFits) hPc hRel
      (by
        simpa [Stmt.compileFromCtxCore, Stmt.jumpOrInvalid, hCtx]
          using hLabel) with
    ⟨target', hStep, hTargetRel, hTargetPc⟩
  refine ⟨1, .running target', cursor, ?_, ?_⟩
  · change
      Assembly.GasParametric.sourceRunNResultWithGasOracle
          (pre ++ (Stmt.compileFromCtxCore .brk ctx supply).code ++ post)
          oracle 1 cursor target =
        .ok (.running target', cursor)
    have hStep' :
        Assembly.GasParametric.sourceStepResultWithGasOracle
            (pre ++ Assembly.Instr.jump label :: post) oracle cursor target =
          .ok (.running target', cursor) := by
      simpa using hStep
    simp [Stmt.compileFromCtxCore, Stmt.jumpOrInvalid, hCtx,
      Assembly.GasParametric.sourceRunNResultWithGasOracle, hStep',
      Bind.bind, Except.bind]
  · exact
      ⟨ rfl
      , label, dest, hCtx
      , by
          simpa [Stmt.compileFromCtxCore, Stmt.jumpOrInvalid, hCtx] using
            hLabel
      , hTargetRel, hTargetPc
      ⟩

theorem cont_withGasOracle {program : Program} {ctx : CompileContext}
    {supply : LabelSupply} {label : Assembly.Label}
    (hCtx : ctx.continueLabel? = some label) :
    StmtPreservesWithGasOracle program ctx supply .cont := by
  intro pre post fuel source outcome target tokens oracle cursor cursorFinal
    hFits hResolve _hExact hPc hRel hEval
  cases hEval
  rcases hResolve.cont label hCtx with ⟨dest, hLabel⟩
  rcases
    FrameStateRel.jump_stepResult_at_withGasOracle
      (label := label) (dest := dest) (pre := pre) (post := post)
      (oracle := oracle) (cursor := cursor)
      (AssemblyProgram.PCFitsFrom.start hFits) hPc hRel
      (by
        simpa [Stmt.compileFromCtxCore, Stmt.jumpOrInvalid, hCtx]
          using hLabel) with
    ⟨target', hStep, hTargetRel, hTargetPc⟩
  refine ⟨1, .running target', cursor, ?_, ?_⟩
  · change
      Assembly.GasParametric.sourceRunNResultWithGasOracle
          (pre ++ (Stmt.compileFromCtxCore .cont ctx supply).code ++ post)
          oracle 1 cursor target =
        .ok (.running target', cursor)
    have hStep' :
        Assembly.GasParametric.sourceStepResultWithGasOracle
            (pre ++ Assembly.Instr.jump label :: post) oracle cursor target =
          .ok (.running target', cursor) := by
      simpa using hStep
    simp [Stmt.compileFromCtxCore, Stmt.jumpOrInvalid, hCtx,
      Assembly.GasParametric.sourceRunNResultWithGasOracle, hStep',
      Bind.bind, Except.bind]
  · exact
      ⟨ rfl
      , label, dest, hCtx
      , by
          simpa [Stmt.compileFromCtxCore, Stmt.jumpOrInvalid, hCtx] using
            hLabel
      , hTargetRel, hTargetPc
      ⟩

theorem leave_withGasOracle {program : Program} {ctx : CompileContext}
    {supply : LabelSupply} {label : Assembly.Label}
    (hCtx : ctx.leaveLabel? = some label) :
    StmtPreservesWithGasOracle program ctx supply .leave := by
  intro pre post fuel source outcome target tokens oracle cursor cursorFinal
    hFits hResolve _hExact hPc hRel hEval
  cases hEval with
  | leave hReturns =>
      rcases hResolve.leave label hCtx with ⟨dest, hLabel⟩
      rcases
        FrameStateRel.jump_stepResult_at_withGasOracle
          (label := label) (dest := dest) (pre := pre) (post := post)
          (oracle := oracle) (cursor := cursor)
          (AssemblyProgram.PCFitsFrom.start hFits) hPc hRel
          (by
            simpa [Stmt.compileFromCtxCore, Stmt.jumpOrInvalid, hCtx]
              using hLabel) with
        ⟨target', hStep, hTargetRel, hTargetPc⟩
      refine ⟨1, .running target', cursor, ?_, ?_⟩
      · change
          Assembly.GasParametric.sourceRunNResultWithGasOracle
              (pre ++
                (Stmt.compileFromCtxCore .leave ctx supply).code ++ post)
              oracle 1 cursor target =
            .ok (.running target', cursor)
        have hStep' :
            Assembly.GasParametric.sourceStepResultWithGasOracle
                (pre ++ Assembly.Instr.jump label :: post) oracle cursor
                target =
              .ok (.running target', cursor) := by
          simpa using hStep
        simp [Stmt.compileFromCtxCore, Stmt.jumpOrInvalid, hCtx,
          Assembly.GasParametric.sourceRunNResultWithGasOracle, hStep',
          Bind.bind, Except.bind]
      · exact
          ⟨ rfl
          , label, dest, hCtx
          , by
              simpa [Stmt.compileFromCtxCore, Stmt.jumpOrInvalid, hCtx]
                using hLabel
          , hTargetRel, hTargetPc
          ⟩

theorem terminal_withGasOracle {program : Program} {ctx : CompileContext}
    {supply : LabelSupply} {kind : Assembly.HaltKind}
    (hSafe : Terminal.RelSafeWithGasOracle kind) :
    StmtPreservesWithGasOracle program ctx supply (.terminal kind) := by
  intro pre post fuel source outcome target tokens oracle cursor cursorFinal
    hFits _hResolve _hExact hPc hRel hEval
  cases hEval with
  | terminal hStep =>
      rcases
        FrameStateRel.terminal_stepResult_at_withGasOracle
          (kind := kind) (pre := pre) (post := post)
          (oracle := oracle) (cursor := cursor)
          hSafe (AssemblyProgram.PCFitsFrom.start hFits) hPc hRel hStep with
        ⟨targetFinal, hTargetStep, hTargetRel⟩
      refine
        ⟨ 1
        , .halted
            { kind := kind
              state := targetFinal
              output := kind.output targetFinal }
        , cursorFinal
        , ?_
        , ?_
        ⟩
      · change
          Assembly.GasParametric.sourceRunNResultWithGasOracle
              (pre ++
                (Stmt.compileFromCtxCore (.terminal kind) ctx supply).code ++
                  post)
              oracle 1 cursor target =
            .ok
              (.halted
                { kind := kind
                  state := targetFinal
                  output := kind.output targetFinal },
                cursorFinal)
        have hStep' :
            Assembly.GasParametric.sourceStepResultWithGasOracle
                (pre ++ Assembly.Instr.prim kind.toPrimOp :: post) oracle
                cursor target =
              .ok
                (.halted
                  { kind := kind
                    state := targetFinal
                    output := kind.output targetFinal },
                  cursorFinal) := by
          simpa using hTargetStep
        simp [Stmt.compileFromCtxCore,
          Assembly.GasParametric.sourceRunNResultWithGasOracle, hStep',
          Bind.bind, Except.bind]
      · exact ⟨rfl, rfl, tokens, hTargetRel⟩

end StmtPreservation

namespace BlockPreservation

theorem nil_withGasOracle {program : Program} {ctx : CompileContext}
    {supply : LabelSupply} :
    BlockPreservesWithGasOracle program ctx supply { stmts := [] } := by
  intro pre post fuel source outcome target tokens oracle cursor cursorFinal
    _hFits _hResolve _hExact hPc hRel hEval
  cases hEval
  exact
    ARunResultWithGasOracle.pure
      (by
        exact
          ⟨ rfl
          , by
              simpa [Block.compileFromCtx, CompiledOutcomeRel,
                Outcome.regular] using And.intro hRel hPc
          ⟩)

theorem cons_withGasOracle {program : Program} {ctx : CompileContext}
    {supply : LabelSupply} {stmt : Stmt} {rest : List Stmt}
    (hStmt : StmtPreservesWithGasOracle program ctx supply stmt)
    (hRest :
      BlockPreservesWithGasOracle program ctx
        (Stmt.compileFromCtxCore stmt ctx supply).next { stmts := rest }) :
    BlockPreservesWithGasOracle program ctx supply { stmts := stmt :: rest } := by
  intro pre post fuel source outcome target tokens oracle cursor cursorFinal
    hFits hResolve hExact hPc hRel hEval
  let compiledStmt := Stmt.compileFromCtxCore stmt ctx supply
  let compiledRest :=
    Block.compileFromCtx { stmts := rest } ctx compiledStmt.next
  have hFits' :
      AssemblyProgram.PCFitsFrom pre
        (compiledStmt.code ++ compiledRest.code) := by
    simpa [Block.compileFromCtx, CompileResult.append,
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
  have hStmtResolve :
      ContextLabelsResolve
        (pre ++ compiledStmt.code ++ (compiledRest.code ++ post)) ctx := by
    simpa [Block.compileFromCtx, CompileResult.append,
      compiledStmt, compiledRest, List.append_assoc] using hResolve
  have hRestResolve :
      ContextLabelsResolve
        ((pre ++ compiledStmt.code) ++ compiledRest.code ++ post) ctx := by
    simpa [Block.compileFromCtx, CompileResult.append,
      compiledStmt, compiledRest, List.append_assoc] using hResolve
  have hStmtExact :
      ExactLabels
        (pre ++ compiledStmt.code ++ (compiledRest.code ++ post)) := by
    simpa [Block.compileFromCtx, CompileResult.append,
      compiledStmt, compiledRest, List.append_assoc] using hExact
  have hRestExact :
      ExactLabels
        ((pre ++ compiledStmt.code) ++ compiledRest.code ++ post) := by
    simpa [Block.compileFromCtx, CompileResult.append,
      compiledStmt, compiledRest, List.append_assoc] using hExact
  cases hEval with
  | cons_regular hStmtEval hRestEval =>
      rename_i innerFuel cursorMid mid
      have hStmtRun :=
        hStmt (pre := pre) (post := compiledRest.code ++ post)
          (fuel := innerFuel) (source := source)
          (outcome := Outcome.regular mid) (target := target)
          (tokens := tokens) (oracle := oracle) (cursor := cursor)
          (cursorFinal := cursorMid)
          hStmtFits hStmtResolve hStmtExact hPc hRel hStmtEval
      have hStmtRunRegular :
          ARunResultWithGasOracle
            (pre ++ compiledStmt.code ++ (compiledRest.code ++ post))
            oracle cursor target
            (fun result targetCursorMid =>
              match result with
              | .running targetMid =>
                  targetCursorMid = cursorMid ∧
                    Frame.StateRel mid targetMid tokens ∧
                      targetMid.pc =
                        Assembly.Program.pcAfter (pre ++ compiledStmt.code)
              | .halted _ => False) := by
        exact ARunResultWithGasOracle.mono hStmtRun (by
          intro result targetCursorMid hResult
          cases result with
          | halted halt =>
              cases hResult.2
          | running targetMid =>
              rcases hResult with ⟨hCursorMid, hCompiled⟩
              exact
                ⟨ hCursorMid
                , by
                    simpa [CompiledOutcomeRel, Outcome.regular] using
                      hCompiled
                ⟩)
      refine
        ARunResultWithGasOracle.bind_running
          (program := pre ++
            (Block.compileFromCtx { stmts := stmt :: rest } ctx supply).code ++
              post)
          (middle := fun targetMid targetCursorMid =>
            targetCursorMid = cursorMid ∧
              Frame.StateRel mid targetMid tokens ∧
                targetMid.pc =
                  Assembly.Program.pcAfter (pre ++ compiledStmt.code))
          ?_ ?_
      · simpa [Block.compileFromCtx, CompileResult.append,
          compiledStmt, compiledRest, List.append_assoc] using hStmtRunRegular
      · intro targetMid targetCursorMid hMid
        rcases hMid with ⟨hCursorMid, hRelMid, hPcMid⟩
        subst targetCursorMid
        have hRestRun :=
          hRest (pre := pre ++ compiledStmt.code) (post := post)
            (fuel := innerFuel) (source := mid) (outcome := outcome)
            (target := targetMid) (tokens := tokens) (oracle := oracle)
            (cursor := cursorMid) (cursorFinal := cursorFinal)
            hRestFits hRestResolve hRestExact hPcMid hRelMid hRestEval
        exact
          ARunResultWithGasOracle.mono
            (by
              simpa [Block.compileFromCtx, CompileResult.append,
                compiledStmt, compiledRest, List.append_assoc] using hRestRun)
            (by
              intro result targetCursorFinal hResult
              simpa [Block.compileFromCtx, CompileResult.append,
                compiledStmt, compiledRest, List.append_assoc] using hResult)
  | cons_brk hStmtEval =>
      rename_i innerFuel outState
      have hStmtRun :=
        hStmt (pre := pre) (post := compiledRest.code ++ post)
          (fuel := innerFuel) (source := source)
          (outcome := Outcome.brk outState) (target := target)
          (tokens := tokens) (oracle := oracle) (cursor := cursor)
          (cursorFinal := cursorFinal)
          hStmtFits hStmtResolve hStmtExact hPc hRel hStmtEval
      refine ARunResultWithGasOracle.mono (by
        simpa [Block.compileFromCtx, CompileResult.append,
          compiledStmt, compiledRest, List.append_assoc] using hStmtRun) ?_
      intro result targetCursor hResult
      rcases hResult with ⟨hCursor, hCompiled⟩
      cases result with
      | halted halt =>
          cases hCompiled
      | running target' =>
          rcases hCompiled with
            ⟨label, dest, hCtxBrk, hLabelPc, hTargetRel, hTargetPc⟩
          exact
            ⟨ hCursor
            , label, dest, hCtxBrk
            , by
                simpa [Block.compileFromCtx, CompileResult.append,
                  compiledStmt, compiledRest, List.append_assoc] using hLabelPc
            , hTargetRel, hTargetPc
            ⟩
  | cons_cont hStmtEval =>
      rename_i innerFuel outState
      have hStmtRun :=
        hStmt (pre := pre) (post := compiledRest.code ++ post)
          (fuel := innerFuel) (source := source)
          (outcome := Outcome.cont outState) (target := target)
          (tokens := tokens) (oracle := oracle) (cursor := cursor)
          (cursorFinal := cursorFinal)
          hStmtFits hStmtResolve hStmtExact hPc hRel hStmtEval
      refine ARunResultWithGasOracle.mono (by
        simpa [Block.compileFromCtx, CompileResult.append,
          compiledStmt, compiledRest, List.append_assoc] using hStmtRun) ?_
      intro result targetCursor hResult
      rcases hResult with ⟨hCursor, hCompiled⟩
      cases result with
      | halted halt =>
          cases hCompiled
      | running target' =>
          rcases hCompiled with
            ⟨label, dest, hCtxCont, hLabelPc, hTargetRel, hTargetPc⟩
          exact
            ⟨ hCursor
            , label, dest, hCtxCont
            , by
                simpa [Block.compileFromCtx, CompileResult.append,
                  compiledStmt, compiledRest, List.append_assoc] using hLabelPc
            , hTargetRel, hTargetPc
            ⟩
  | cons_leave hStmtEval =>
      rename_i innerFuel outState
      have hStmtRun :=
        hStmt (pre := pre) (post := compiledRest.code ++ post)
          (fuel := innerFuel) (source := source)
          (outcome := Outcome.leave outState) (target := target)
          (tokens := tokens) (oracle := oracle) (cursor := cursor)
          (cursorFinal := cursorFinal)
          hStmtFits hStmtResolve hStmtExact hPc hRel hStmtEval
      refine ARunResultWithGasOracle.mono (by
        simpa [Block.compileFromCtx, CompileResult.append,
          compiledStmt, compiledRest, List.append_assoc] using hStmtRun) ?_
      intro result targetCursor hResult
      rcases hResult with ⟨hCursor, hCompiled⟩
      cases result with
      | halted halt =>
          cases hCompiled
      | running target' =>
          rcases hCompiled with
            ⟨label, dest, hCtxLeave, hLabelPc, hTargetRel, hTargetPc⟩
          exact
            ⟨ hCursor
            , label, dest, hCtxLeave
            , by
                simpa [Block.compileFromCtx, CompileResult.append,
                  compiledStmt, compiledRest, List.append_assoc] using hLabelPc
            , hTargetRel, hTargetPc
            ⟩
  | cons_halt hStmtEval =>
      rename_i innerFuel outState kind
      have hStmtRun :=
        hStmt (pre := pre) (post := compiledRest.code ++ post)
          (fuel := innerFuel) (source := source)
          (outcome := Outcome.halt kind outState) (target := target)
          (tokens := tokens) (oracle := oracle) (cursor := cursor)
          (cursorFinal := cursorFinal)
          hStmtFits hStmtResolve hStmtExact hPc hRel hStmtEval
      refine ARunResultWithGasOracle.mono (by
        simpa [Block.compileFromCtx, CompileResult.append,
          compiledStmt, compiledRest, List.append_assoc] using hStmtRun) ?_
      intro result targetCursor hResult
      rcases hResult with ⟨hCursor, hCompiled⟩
      cases result with
      | running target' =>
          cases hCompiled
      | halted halt =>
          rcases hCompiled with ⟨hKind, haltedTokens, hTargetRel⟩
          exact ⟨hCursor, hKind, haltedTokens, hTargetRel⟩

end BlockPreservation

namespace CompilerPreservationProgramLayoutUpToWithGasOracle

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 2000 in
mutual
  theorem block {program : Program}
      {layout : ProcedurePreservation.ProgramLayout program}
      {maxFuel : Nat}
      (hCall : ProcedureLayoutPreservation.CallObligationUpToWithGasOracle
        layout maxFuel)
      {ctx : CompileContext} {supply : LabelSupply} {block : Block}
      {canBreak canContinue canLeave : Bool}
      (hWF : Block.WF canBreak canContinue canLeave block)
      (hRunner : Block.RunnerSafe block)
      (hFrame : Block.FrameSafeWithGasOracle block)
      (hTerminal : Block.TerminalSafe block)
      (hCtx : ControlContextSupports canBreak canContinue canLeave ctx) :
      ProcedureLayoutPreservation.BlockPreservesInProgramLayoutWithGasOracleUpTo
        layout maxFuel ctx supply block := by
    cases hWF with
    | nil =>
        exact
          ProcedureLayoutPreservation.block_preserves_upTo_of_preserves_withGasOracle
            (ProcedureLayoutPreservation.preserves_nil_in_programLayout_withGasOracle
              layout)
    | cons hStmtWF hRestWF =>
        rename_i headStmt rest
        cases hRunner with
        | cons hStmtRunner hRestRunner =>
        cases hFrame with
        | cons hStmtFrame hRestFrame =>
        cases hTerminal with
        | cons hStmtTerminal hRestTerminal =>
            exact
              ProcedureLayoutPreservation.preserves_cons_in_programLayout_upTo_withGasOracle
                (layout := layout)
                (stmt (program := program) (layout := layout)
                  (maxFuel := maxFuel) hCall (ctx := ctx) (supply := supply)
                  hStmtWF hStmtRunner hStmtFrame hStmtTerminal hCtx)
                (block (program := program) (layout := layout)
                  (maxFuel := maxFuel) hCall (ctx := ctx)
                  (supply := (Stmt.compileFromCtxCore headStmt ctx supply).next)
                  hRestWF hRestRunner hRestFrame hRestTerminal hCtx)
  termination_by sizeOf block
  decreasing_by
    all_goals
      simp_wf
      subst_vars
      simp
      all_goals omega

  theorem stmt {program : Program}
      {layout : ProcedurePreservation.ProgramLayout program}
      {maxFuel : Nat}
      (hCall : ProcedureLayoutPreservation.CallObligationUpToWithGasOracle
        layout maxFuel)
      {ctx : CompileContext} {supply : LabelSupply} {stmt : Stmt}
      {canBreak canContinue canLeave : Bool}
      (hWF : Stmt.WF canBreak canContinue canLeave stmt)
      (hRunner : Stmt.RunnerSafe stmt)
      (hFrame : Stmt.FrameSafeWithGasOracle stmt)
      (hTerminal : Stmt.TerminalSafe stmt)
      (hCtx : ControlContextSupports canBreak canContinue canLeave ctx) :
      ProcedureLayoutPreservation.StmtPreservesInProgramLayoutWithGasOracleUpTo
        layout maxFuel ctx supply stmt := by
    cases hWF with
    | code =>
        cases hRunner with
        | code hCodeRunner =>
        cases hFrame with
        | code hCodeFrame =>
            exact
              ProcedureLayoutPreservation.stmt_preserves_upTo_of_preserves_withGasOracle
                (ProcedureLayoutPreservation.stmt_preserves_in_programLayout_of_local_withGasOracle
                  (StmtPreservation.code_withGasOracle
                    (Code.runnerSafeWithGasOracle_of_runnerSafe
                      hCodeRunner)
                    hCodeFrame))
    | if_ hBodyWF =>
        cases hRunner with
        | if_ hCondRunner hBodyRunner =>
        cases hFrame with
        | if_ hCondFrame hBodyFrame =>
        cases hTerminal with
        | if_ hBodyTerminal =>
            exact
              ProcedureLayoutPreservation.preserves_if_in_programLayout_upTo_withGasOracle
                (Code.runnerSafeWithGasOracle_of_runnerSafe hCondRunner)
                hCondFrame
                (block (program := program) (layout := layout)
                  (maxFuel := maxFuel) hCall (ctx := ctx)
                  (supply := LabelSupply.next supply)
                  hBodyWF hBodyRunner hBodyFrame hBodyTerminal hCtx)
    | switch hCasesWF hDefaultWF =>
        rename_i scrutinee cases defaultBody
        cases hRunner with
        | switch hScrutineeRunner hCasesRunner hDefaultRunner =>
        cases hFrame with
        | switch hScrutineeFrame hCasesFrame hDefaultFrame =>
        cases hTerminal with
        | switch hCasesTerminal hDefaultTerminal =>
            have hCasesPreserves :
                ProcedureLayoutPreservation.SwitchCasesPreservesInProgramLayoutWithGasOracleUpTo
                  layout maxFuel ctx (LabelSupply.label supply 0) supply
                  (LabelSupply.next supply) 0 cases :=
              ProcedureLayoutPreservation.switchCasesPreservesInProgramLayoutWithGasOracleUpTo_of_all
                (layout := layout) (maxFuel := maxFuel) (ctx := ctx)
                (endLabel := LabelSupply.label supply 0)
                (base := supply) (supply := LabelSupply.next supply)
                (cases := cases) (idx := 0)
                (hAll := by
                  intro bodySupply value body hMem
                  exact
                    block (program := program) (layout := layout)
                      (maxFuel := maxFuel) hCall
                      (ctx := ctx) (supply := bodySupply)
                      (hCasesWF value body hMem)
                      (hCasesRunner value body hMem)
                      (hCasesFrame value body hMem)
                      (hCasesTerminal value body hMem)
                      hCtx)
            have hDefaultPreserves :
                ProcedureLayoutPreservation.SwitchDefaultPreservesInProgramLayoutWithGasOracleUpTo
                  layout maxFuel ctx
                  (SwitchCases.compileFromCtx cases ctx
                    (LabelSupply.label supply 0) supply
                    (LabelSupply.next supply) 0).next defaultBody := by
              cases hDefault : defaultBody with
              | none =>
                  trivial
              | some defaultBody =>
                  exact
                    block (program := program) (layout := layout)
                      (maxFuel := maxFuel) hCall
                      (ctx := ctx)
                      (supply :=
                        (SwitchCases.compileFromCtx cases ctx
                          (LabelSupply.label supply 0) supply
                          (LabelSupply.next supply) 0).next)
                      (hDefaultWF defaultBody hDefault)
                      (hDefaultRunner defaultBody hDefault)
                      (hDefaultFrame defaultBody hDefault)
                      (hDefaultTerminal defaultBody hDefault)
                      hCtx
            exact
              (ProcedureLayoutPreservation.preserves_switch_in_programLayout_upTo_withGasOracle
                (Code.runnerSafeWithGasOracle_of_runnerSafe hScrutineeRunner)
                hScrutineeFrame hCasesPreserves hDefaultPreserves :
                ProcedureLayoutPreservation.StmtPreservesInProgramLayoutWithGasOracleUpTo
                  layout maxFuel ctx supply
                  (.switch scrutinee cases defaultBody))
    | for_ hInitWF hPostWF hBodyWF =>
        rename_i init post body cond
        cases hRunner with
        | for_ hInitRunner hCondRunner hPostRunner hBodyRunner =>
        cases hFrame with
        | for_ hInitFrame hCondFrame hPostFrame hBodyFrame =>
        cases hTerminal with
        | for_ hInitTerminal hPostTerminal hBodyTerminal =>
            let loopOuterCtx : CompileContext :=
              { ctx with breakLabel? := none, continueLabel? := none }
            let bodyCtx : CompileContext :=
              { ctx with
                breakLabel? := some (LabelSupply.label supply 3)
                continueLabel? := some (LabelSupply.label supply 2) }
            exact
              (ProcedureLayoutPreservation.preserves_for_in_programLayout_upTo_withGasOracle
                (layout := layout) (maxFuel := maxFuel) (ctx := ctx)
                (supply := supply)
                (init := init) (cond := cond) (post := post) (body := body)
                (Code.runnerSafeWithGasOracle_of_runnerSafe hCondRunner)
                hCondFrame
                (block (program := program) (layout := layout)
                  (maxFuel := maxFuel) hCall
                  (ctx := loopOuterCtx) (supply := LabelSupply.next supply)
                  hInitWF hInitRunner hInitFrame hInitTerminal
                  (ControlContextSupports.loopOuter hCtx))
                (block (program := program) (layout := layout)
                  (maxFuel := maxFuel) hCall
                  (ctx := bodyCtx)
                  (supply :=
                    (Block.compileFromCtx init loopOuterCtx
                      (LabelSupply.next supply)).next)
                  hBodyWF hBodyRunner hBodyFrame hBodyTerminal
                  (ControlContextSupports.loopBody hCtx))
                (block (program := program) (layout := layout)
                  (maxFuel := maxFuel) hCall
                  (ctx := loopOuterCtx)
                  (supply :=
                    (Block.compileFromCtx body bodyCtx
                      (Block.compileFromCtx init loopOuterCtx
                        (LabelSupply.next supply)).next).next)
                  hPostWF hPostRunner hPostFrame hPostTerminal
                  (ControlContextSupports.loopOuter hCtx)) :
                ProcedureLayoutPreservation.StmtPreservesInProgramLayoutWithGasOracleUpTo
                  layout maxFuel ctx supply (.for_ init cond post body))
    | brk hAllowed =>
        rcases hCtx.brk hAllowed with ⟨label, hLabel⟩
        exact
          ProcedureLayoutPreservation.stmt_preserves_upTo_of_preserves_withGasOracle
            (ProcedureLayoutPreservation.stmt_preserves_in_programLayout_of_local_withGasOracle
              (StmtPreservation.brk_withGasOracle hLabel))
    | cont hAllowed =>
        rcases hCtx.cont hAllowed with ⟨label, hLabel⟩
        exact
          ProcedureLayoutPreservation.stmt_preserves_upTo_of_preserves_withGasOracle
            (ProcedureLayoutPreservation.stmt_preserves_in_programLayout_of_local_withGasOracle
              (StmtPreservation.cont_withGasOracle hLabel))
    | leave hAllowed =>
        rcases hCtx.leave hAllowed with ⟨label, hLabel⟩
        exact
          ProcedureLayoutPreservation.stmt_preserves_upTo_of_preserves_withGasOracle
            (ProcedureLayoutPreservation.stmt_preserves_in_programLayout_of_local_withGasOracle
              (StmtPreservation.leave_withGasOracle hLabel))
    | call =>
        exact hCall.preserves
    | terminal =>
        cases hTerminal with
        | terminal hSafe =>
            exact
              ProcedureLayoutPreservation.stmt_preserves_upTo_of_preserves_withGasOracle
                (ProcedureLayoutPreservation.stmt_preserves_in_programLayout_of_local_withGasOracle
                  (StmtPreservation.terminal_withGasOracle
                    (Terminal.relSafeWithGasOracle_of_relSafe hSafe)))
  termination_by sizeOf stmt
  decreasing_by
    all_goals
      simp_wf
      subst_vars
      first
      | simp
        all_goals omega
      | exact
          lt_trans (by simp)
            (lt_trans (list_sizeOf_lt_sizeOf_of_mem hMem) (by simp; omega))
end

end CompilerPreservationProgramLayoutUpToWithGasOracle

theorem callObligationForAllFuel_of_acceptedWithGasOracle {program : Program}
    (layout : ProcedurePreservation.ProgramLayout program)
    (hAccepted : Program.AcceptedWithGasOracle program) :
    ProcedureLayoutPreservation.CallObligationForAllFuelWithGasOracle layout := by
  intro maxFuel
  induction maxFuel with
  | zero =>
      exact
        ProcedureLayoutPreservation.callObligationUpTo_zero_withGasOracle
          layout
  | succ smaller ih =>
      exact
        ProcedureLayoutPreservation.callObligationUpTo_succ_of_procBodies_withGasOracle
          (layout := layout)
          (maxFuel := smaller)
          (by
            intro name proc hLookup
            have hProcWF : Proc.WF proc :=
              Program.procWF_of_lookup? hAccepted.accepted.wf hLookup
            have hProcRunner : Proc.RunnerSafe proc :=
              Program.procRunnerSafe_of_lookup? hAccepted.accepted.runner
                hLookup
            have hProcFrame : Proc.FrameSafeWithGasOracle proc :=
              Program.procFrameSafeWithGasOracle_of_lookup?
                hAccepted.oracleFrame hLookup
            have hProcTerminal : Proc.TerminalSafe proc :=
              Program.procTerminalSafe_of_lookup? hAccepted.accepted.terminal
                hLookup
            exact
              (CompilerPreservationProgramLayoutUpToWithGasOracle.block
                (program := program) (layout := layout)
                (maxFuel := smaller) (hCall := ih)
                (ctx := ProcedureCall.bodyCtx program proc)
                (supply := (layout.procLayout hLookup).bodySupply)
                (block := proc.body)
                (canBreak := false) (canContinue := false)
                (canLeave := true)
                hProcWF.2.2 hProcRunner hProcFrame hProcTerminal
                (by
                  refine ⟨?_, ?_, ?_⟩
                  · intro hFalse
                    cases hFalse
                  · intro hFalse
                    cases hFalse
                  · intro _hTrue
                    exact
                      ⟨ProcLabel.exit proc.name, by
                        simp [ProcedureCall.bodyCtx]⟩) :
                ProcedureLayoutPreservation.BlockPreservesInProgramLayoutWithGasOracleUpTo
                  layout smaller (ProcedureCall.bodyCtx program proc)
                  (layout.procLayout hLookup).bodySupply proc.body))

namespace CompilerPreservationProgramLayoutWithGasOracle

theorem main_block {program : Program}
    (layout : ProcedurePreservation.ProgramLayout program)
    (hCall :
      ProcedureLayoutPreservation.CallObligationForAllFuelWithGasOracle layout)
    (hWF : program.WF)
    (hRunner : Program.RunnerSafe program)
    (hFrame : Program.FrameSafeWithGasOracle program)
    (hTerminal : Program.TerminalSafe program) :
    ProcedureLayoutPreservation.BlockPreservesInProgramLayoutWithGasOracle
      layout (CompiledProgram.mainCtx program) 0 program.body := by
  intro fuel source outcome target tokens oracle cursor cursorFinal hProgramWF
    hCtxProcs hCalls hResolve segment hPc hRel hEval
  have hMainUpTo :
      ProcedureLayoutPreservation.BlockPreservesInProgramLayoutWithGasOracleUpTo
        layout (fuel + 1) (CompiledProgram.mainCtx program) 0
        program.body :=
    CompilerPreservationProgramLayoutUpToWithGasOracle.block
      (program := program) (layout := layout) (maxFuel := fuel + 1)
      (hCall := hCall (fuel + 1))
      (ctx := CompiledProgram.mainCtx program) (supply := 0)
      (block := program.body)
      (canBreak := false) (canContinue := false) (canLeave := false)
      hWF.2.2.2.2 hRunner.2 hFrame.2 hTerminal.2
      (by
        refine ⟨?_, ?_, ?_⟩
        · intro hFalse
          cases hFalse
        · intro hFalse
          cases hFalse
        · intro hFalse
          cases hFalse)
  exact
    hMainUpTo
      (fuel := fuel) (source := source) (outcome := outcome)
      (target := target) (tokens := tokens) (oracle := oracle)
      (cursor := cursor) (cursorFinal := cursorFinal)
      (by omega) hProgramWF hCtxProcs hCalls hResolve segment hPc hRel hEval

end CompilerPreservationProgramLayoutWithGasOracle

theorem compile_preserves_with_programLayout_withGasOracle
    {program : Program} {sourceFuel : Nat} {initial : EVMState}
    {oracle : GasOracle} {cursor cursorFinal : Nat}
    {sourceOutcome : Outcome}
    (layout : ProcedurePreservation.ProgramLayout program)
    (evidence : ProcedurePreservation.ProgramLayout.MainEvidence layout)
    (hAccepted : Program.AcceptedWithGasOracle program)
    (hInitialPc : initial.pc = evidence.mainSegment.startPc)
    (hSource :
      program.runWithGasOracle sourceFuel oracle cursor initial =
        .ok (sourceOutcome, cursorFinal)) :
    ∃ targetFuel targetOutcome,
      Assembly.GasParametric.sourceRunNResultWithGasOracle program.compile
          oracle targetFuel cursor initial =
        .ok (targetOutcome, cursorFinal) ∧
      WholeProgramOutcomeRel sourceOutcome targetOutcome := by
  have hEval := Program.evalWithGasOracle_of_run hSource
  have hCall :
      ProcedureLayoutPreservation.CallObligationForAllFuelWithGasOracle
        layout :=
    callObligationForAllFuel_of_acceptedWithGasOracle layout hAccepted
  have hMainPreserves :
      ProcedureLayoutPreservation.BlockPreservesInProgramLayoutWithGasOracle
        layout (CompiledProgram.mainCtx program) 0 program.body :=
    CompilerPreservationProgramLayoutWithGasOracle.main_block layout hCall
      hAccepted.accepted.wf hAccepted.accepted.runner hAccepted.oracleFrame
      hAccepted.accepted.terminal
  have hRun :=
    hMainPreserves
      (fuel := sourceFuel) (source := Program.initialState initial)
      (outcome := sourceOutcome) (target := initial) (tokens := [])
      (oracle := oracle) (cursor := cursor) (cursorFinal := cursorFinal)
      hAccepted.accepted.wf rfl evidence.mainCalls
      (ContextLabelsResolve.mainCtx program layout.asm)
      evidence.mainSegment hInitialPc (Frame.stateRel_initial initial)
      (by simpa [Program.initialState] using hEval)
  rcases hRun with ⟨targetFuel, targetOutcome, targetCursorFinal, hRunEq,
    hOutcome⟩
  rcases hOutcome with ⟨hCursorFinal, hCompiled⟩
  subst targetCursorFinal
  have hWhole :=
    Program.wholeProgramSourceOutcome_of_evalWithGasOracle
      hAccepted.accepted.wf hEval
  refine ⟨targetFuel, targetOutcome, ?_, ?_⟩
  · rw [← evidence.asm_eq]
    exact hRunEq
  · exact WholeProgramOutcomeRel.of_compiled_main hWhole hCompiled

theorem compile_preserves_with_bounds_withGasOracle
    {program : Program} {sourceFuel : Nat} {initial : EVMState}
    {oracle : GasOracle} {cursor cursorFinal : Nat}
    {sourceOutcome : Outcome}
    (bounds : ProcedurePreservation.CompilationBounds program)
    (hAccepted : Program.AcceptedWithGasOracle program)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hSource :
      program.runWithGasOracle sourceFuel oracle cursor initial =
        .ok (sourceOutcome, cursorFinal)) :
    ∃ targetFuel targetOutcome,
      Assembly.GasParametric.sourceRunNResultWithGasOracle program.compile
          oracle targetFuel cursor initial =
        .ok (targetOutcome, cursorFinal) ∧
      WholeProgramOutcomeRel sourceOutcome targetOutcome :=
  compile_preserves_with_programLayout_withGasOracle
    (layout := ProcedurePreservation.ProgramLayout.ofCompilationBounds bounds)
    (evidence :=
      ProcedurePreservation.ProgramLayout.mainEvidenceOfCompilationBounds
        bounds)
    hAccepted
    (by simpa using hInitialPc)
    hSource

theorem compile_preserves_of_checked_bounds_withGasOracle
    {program : Program} {sourceFuel : Nat} {initial : EVMState}
    {oracle : GasOracle} {cursor cursorFinal : Nat}
    {sourceOutcome : Outcome}
    (hChecked :
      ProcedurePreservation.compilationBoundsChecked program = true)
    (hAccepted : Program.AcceptedWithGasOracle program)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hSource :
      program.runWithGasOracle sourceFuel oracle cursor initial =
        .ok (sourceOutcome, cursorFinal)) :
    ∃ targetFuel targetOutcome,
      Assembly.GasParametric.sourceRunNResultWithGasOracle program.compile
          oracle targetFuel cursor initial =
        .ok (targetOutcome, cursorFinal) ∧
      WholeProgramOutcomeRel sourceOutcome targetOutcome :=
  compile_preserves_with_bounds_withGasOracle
    (ProcedurePreservation.bounds_of_checked hChecked)
    hAccepted hInitialPc hSource

noncomputable def compilerCheckedWithGasOracle
    (program : Program) : Bool :=
  Program.acceptedWithGasOracle program &&
    ProcedurePreservation.compilationBoundsChecked program

noncomputable def compileCheckedWithGasOracle?
    (program : Program) : Option Assembly.Program :=
  if compilerCheckedWithGasOracle program then
    some program.compile
  else
    none

theorem compileCheckedWithGasOracle?_eq_some
    {program : Program} {asm : Assembly.Program}
    (hCompile : compileCheckedWithGasOracle? program = some asm) :
    asm = program.compile ∧ Program.AcceptedWithGasOracle program ∧
      ProcedurePreservation.CompilationBounds program := by
  unfold compileCheckedWithGasOracle? at hCompile
  cases hChecked : compilerCheckedWithGasOracle program <;>
    simp [hChecked] at hCompile
  cases hCompile
  cases hAcceptedChecked : Program.acceptedWithGasOracle program <;>
    cases hBoundsChecked :
        ProcedurePreservation.compilationBoundsChecked program <;>
      simp [compilerCheckedWithGasOracle, hAcceptedChecked,
        hBoundsChecked] at hChecked
  exact
    ⟨ rfl
    , Program.acceptedWithGasOracle_of_check hAcceptedChecked
    , ProcedurePreservation.bounds_of_checked hBoundsChecked
    ⟩

theorem compile_preserves_withGasOracle
    {program : Program} {asm : Assembly.Program}
    {sourceFuel : Nat} {initial : EVMState}
    {oracle : GasOracle} {cursor cursorFinal : Nat}
    {sourceOutcome : Outcome}
    (hCompile : compileCheckedWithGasOracle? program = some asm)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hSource :
      program.runWithGasOracle sourceFuel oracle cursor initial =
        .ok (sourceOutcome, cursorFinal)) :
    ∃ targetFuel targetOutcome,
      Assembly.GasParametric.sourceRunNResultWithGasOracle asm oracle
          targetFuel cursor initial =
        .ok (targetOutcome, cursorFinal) ∧
      WholeProgramOutcomeRel sourceOutcome targetOutcome := by
  rcases compileCheckedWithGasOracle?_eq_some hCompile with
    ⟨hAsm, hAccepted, hBounds⟩
  subst asm
  exact
    compile_preserves_with_bounds_withGasOracle hBounds hAccepted hInitialPc
      hSource

end GasParametric

end Preservation
end Structured
end EvmCompiler
