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

theorem assemble_emits_code {program : Program} {target : TargetProgram}
    (hAsm : assemble? program = some target) :
    ∃ code, emit? program = some code ∧ target.code = code := by
  unfold assemble? at hAsm
  cases hEmit : emit? program with
  | none =>
      simp [hEmit] at hAsm
  | some code =>
      simp [hEmit] at hAsm
      cases hAsm
      exact ⟨code, rfl, rfl⟩

theorem emitFrom_block_for_instrAtPc {full suffix : Program}
    {base query pc : Nat} {instr : Instr} {code : List LocatedTarget}
    (hEmit : emitFrom? full suffix base = some code)
    (hAt : Program.instrAtPcFrom suffix base query = some (pc, instr)) :
    ∃ before emitted after,
      code = before ++ emitted ++ after ∧
        emitInstr? full pc instr = some emitted := by
  induction suffix generalizing base code with
  | nil =>
      simp [Program.instrAtPcFrom] at hAt
  | cons head rest ih =>
      unfold emitFrom? at hEmit
      cases hHere : emitInstr? full base head with
      | none =>
          simp [hHere] at hEmit
      | some here =>
          cases hThere : emitFrom? full rest (base + head.byteSize) with
          | none =>
              simp [hHere, hThere] at hEmit
          | some there =>
              simp [hHere, hThere] at hEmit
              cases hEmit
              by_cases hQuery : query = base
              · unfold Program.instrAtPcFrom at hAt
                simp [hQuery] at hAt
                have hPair : (base, head) = (pc, instr) := by
                  simpa using hAt
                cases hPair
                exact ⟨[], here, there, rfl, hHere⟩
              · unfold Program.instrAtPcFrom at hAt
                simp [hQuery] at hAt
                obtain ⟨before, emitted, after, hDecomp, hEmitInstr⟩ :=
                  ih hThere hAt
                exact
                  ⟨here ++ before, emitted, after,
                    by simp [hDecomp, List.append_assoc], hEmitInstr⟩

theorem emit_block_for_instrAtPc {program : Program}
    {query pc : Nat} {instr : Instr} {code : List LocatedTarget}
    (hEmit : emit? program = some code)
    (hAt : Program.instrAtPc program query = some (pc, instr)) :
    ∃ before emitted after,
      code = before ++ emitted ++ after ∧
        emitInstr? program pc instr = some emitted := by
  exact emitFrom_block_for_instrAtPc (full := program) (suffix := program)
    (base := 0) (query := query) hEmit hAt

theorem assemble_covers_current_pc {program : Program} {target : TargetProgram}
    {query pc : Nat} {instr : Instr}
    (hAsm : assemble? program = some target)
    (hAt : Program.instrAtPc program query = some (pc, instr)) :
    ∃ before emitted after,
      target.code = before ++ emitted ++ after ∧
        emitInstr? program pc instr = some emitted := by
  obtain ⟨code, hEmit, hTargetCode⟩ := assemble_emits_code hAsm
  obtain ⟨before, emitted, after, hDecomp, hEmitInstr⟩ :=
    emit_block_for_instrAtPc hEmit hAt
  exact ⟨before, emitted, after, hTargetCode.trans hDecomp, hEmitInstr⟩

theorem assemble_source_step_current_projected_sound {program : Program}
    {target : TargetProgram} {state sourceState : EVMState}
    (hAsm : assemble? program = some target)
    (hStep : Source.step program state = .ok sourceState) :
    ∃ pc instr emitted before after targetState,
      Program.instrAtPc program state.pc.toNat = some (pc, instr) ∧
        emitInstr? program pc instr = some emitted ∧
        target.code = before ++ emitted ++ after ∧
        Target.runList (emitted.map LocatedTarget.instr) state = .ok targetState ∧
        eraseGas targetState = eraseGas sourceState := by
  unfold Source.step at hStep
  cases hAt : Program.instrAtPc program state.pc.toNat with
  | none =>
      simp [hAt] at hStep
  | some current =>
      cases current with
      | mk pc instr =>
          simp [hAt] at hStep
          obtain ⟨before, emitted, after, hTargetBlock, hEmitInstr⟩ :=
            assemble_covers_current_pc hAsm hAt
          obtain ⟨targetState, hRun, hErase⟩ :=
            stepAt_emit_projected_sound hEmitInstr hStep
          exact
            ⟨pc, instr, emitted, before, after, targetState,
              rfl, hEmitInstr, hTargetBlock, hRun, hErase⟩

end Preservation

end Assembly
end EvmCompiler
