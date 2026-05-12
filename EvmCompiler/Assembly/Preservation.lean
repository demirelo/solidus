import EvmCompiler.Assembly.Semantics

namespace EvmCompiler
namespace Assembly

namespace Preservation

theorem run_push_jump (dest : Nat) (state : EVMState) :
    Target.runList
        [TargetInstr.push32 (EvmYul.UInt256.ofNat dest), TargetInstr.jump]
        state =
      .ok (Source.jumpPc dest state) := by
  rfl

theorem run_push_jumpi (dest : Nat) (state : EVMState) :
    Target.runList
        [TargetInstr.push32 (EvmYul.UInt256.ofNat dest), TargetInstr.jumpi]
        state =
      match state.stack.pop with
      | some (stack, cond) =>
          .ok
            { state with
              pc :=
                if cond != EvmYul.UInt256.ofNat 0 then
                  EvmYul.UInt256.ofNat dest
                else
                  Source.jumpiFallthroughPc state
              stack := stack
            }
      | none =>
          .error .StackUnderflow := by
  cases state with
  | mk shared pc stack execLength =>
  cases stack with
  | nil => rfl
  | cons _ _ => rfl

theorem runList_single (instr : TargetInstr) (state : EVMState) :
    Target.runList [instr] state = Target.stepInstr instr state := by
  cases h : Target.stepInstr instr state with
  | error e =>
      unfold Target.runList
      rw [h]
      rfl
  | ok state' =>
      unfold Target.runList
      rw [h]
      rfl

theorem stepAt_emit_sound {program : Program} {pc : Nat} {instr : Instr}
    {located : List LocatedTarget} {state sourceState : EVMState}
    (hEmit : emitInstr? program pc instr = some located)
    (hStep : Source.stepAt program pc instr state = .ok sourceState) :
    Target.runList (located.map LocatedTarget.instr) state = .ok sourceState := by
  cases instr with
  | label name =>
      simp [emitInstr?, Source.stepAt] at hEmit hStep
      subst located
      simpa [runList_single] using hStep
  | prim op =>
      simp [emitInstr?, Source.stepAt] at hEmit hStep
      subst located
      simpa [runList_single] using hStep
  | push value =>
      simp [emitInstr?, Source.stepAt] at hEmit hStep
      subst located
      simpa [runList_single] using hStep
  | jump target =>
      cases hDest : Program.labelPc program target with
      | none =>
          simp [emitInstr?, hDest] at hEmit
      | some dest =>
          simp [emitInstr?, hDest, Source.stepAt, Source.jumpPc] at hEmit hStep
          subst located
          change
            Target.runList
                [TargetInstr.push32 (EvmYul.UInt256.ofNat dest), TargetInstr.jump]
                state =
              .ok sourceState
          rw [run_push_jump dest state]
          exact hStep
  | jumpi target =>
      cases hDest : Program.labelPc program target with
      | none =>
          simp [emitInstr?, hDest] at hEmit
      | some dest =>
          simp [emitInstr?, hDest, Source.stepAt] at hEmit hStep
          subst located
          change
            Target.runList
                [TargetInstr.push32 (EvmYul.UInt256.ofNat dest), TargetInstr.jumpi]
                state =
              .ok sourceState
          rw [run_push_jumpi dest state]
          exact hStep

theorem stepAt_emit_projected_sound {program : Program} {pc : Nat} {instr : Instr}
    {located : List LocatedTarget} {state sourceState : EVMState}
    (hEmit : emitInstr? program pc instr = some located)
    (hStep : Source.stepAt program pc instr state = .ok sourceState) :
    ∃ targetState,
      Target.runList (located.map LocatedTarget.instr) state = .ok targetState ∧
        eraseGas targetState = eraseGas sourceState := by
  refine ⟨sourceState, ?_, rfl⟩
  exact stepAt_emit_sound hEmit hStep

theorem source_step_current_emit_sound {program : Program} {state sourceState : EVMState}
    {code : List TargetInstr}
    (hEmit : emitCurrent? program state = some code)
    (hStep : Source.step program state = .ok sourceState) :
    Target.runList code state = .ok sourceState := by
  unfold emitCurrent? at hEmit
  unfold Source.step at hStep
  cases hAt : Program.instrAtPc program state.pc.toNat with
  | none =>
      simp [hAt] at hEmit
  | some current =>
      cases current with
      | mk pc instr =>
          simp [hAt] at hEmit hStep
          cases hEmitInstr : emitInstr? program pc instr with
          | none =>
              simp [hEmitInstr] at hEmit
          | some located =>
              simp [hEmitInstr] at hEmit
              subst code
              exact stepAt_emit_sound hEmitInstr hStep

theorem source_step_current_projected_sound {program : Program}
    {state sourceState : EVMState} {code : List TargetInstr}
    (hEmit : emitCurrent? program state = some code)
    (hStep : Source.step program state = .ok sourceState) :
    ∃ targetState,
      Target.runList code state = .ok targetState ∧
        eraseGas targetState = eraseGas sourceState := by
  refine ⟨sourceState, ?_, rfl⟩
  exact source_step_current_emit_sound hEmit hStep

end Preservation

end Assembly
end EvmCompiler
