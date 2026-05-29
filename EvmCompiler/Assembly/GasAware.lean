import EvmCompiler.Assembly.TopLevel

namespace EvmCompiler
namespace Assembly

namespace GasAware

def installCodeAndGas (target : TargetProgram) (gas : Nat)
    (state : EVMState) : EVMState :=
  { state with
    gasAvailable := EvmYul.UInt256.ofNat gas
    executionEnv := { state.executionEnv with code := Bytecode.encodeTarget target }
  }

theorem installCodeAndGas_gasAvailable_toNat {target : TargetProgram}
    {gas : Nat} {state : EVMState}
    (hGasFits : gas < EvmYul.UInt256.size) :
    (installCodeAndGas target gas state).gasAvailable.toNat = gas := by
  simp [installCodeAndGas,
    Bytecode.uint256_ofNat_toNat_of_lt_size hGasFits]

theorem installCodeAndGas_idempotent (target : TargetProgram) (gas : Nat)
    (state : EVMState) :
    installCodeAndGas target gas (installCodeAndGas target gas state) =
      installCodeAndGas target gas state := by
  simp [installCodeAndGas]

theorem uint256_sub_toNat_of_le {left right : Word}
    (hLe : right.toNat ≤ left.toNat) :
    (left - right).toNat = left.toNat - right.toNat := by
  change (EvmYul.UInt256.sub left right).toNat =
    left.toNat - right.toNat
  unfold EvmYul.UInt256.toNat EvmYul.UInt256.sub
  exact Fin.sub_val_of_le hLe

def validJumps (target : TargetProgram) : Array EvmYul.UInt256 :=
  EvmYul.EVM.D_J (Bytecode.encodeTarget target) (EvmYul.UInt256.ofNat 0)

def targetInstrUsesCallCreate : TargetInstr → Bool
  | .prim op => op.isCallCreate
  | .push32 _ | .jump | .jumpi | .jumpdest => false

theorem instr_usesCallCreate_false_of_instrAtPcFrom
    {program : Program} {base query pc : Nat} {instr : Instr}
    (hNoCallCreate : Program.usesCallCreate program = false)
    (hAt : Program.instrAtPcFrom program base query = some (pc, instr)) :
    Instr.usesCallCreate instr = false := by
  induction program generalizing base with
  | nil =>
      simp [Program.instrAtPcFrom] at hAt
  | cons head rest ih =>
      have hSplit :
          Instr.usesCallCreate head = false ∧
            Program.usesCallCreate rest = false := by
        simpa [Program.usesCallCreate] using hNoCallCreate
      by_cases hQuery : query = base
      · simp [Program.instrAtPcFrom, hQuery] at hAt
        have hPair : (base, head) = (pc, instr) := by
          simpa using hAt
        cases hPair
        exact hSplit.1
      · simp [Program.instrAtPcFrom, hQuery] at hAt
        exact ih hSplit.2 hAt

theorem instr_usesCallCreate_false_of_instrAtPc
    {program : Program} {query pc : Nat} {instr : Instr}
    (hNoCallCreate : Program.usesCallCreate program = false)
    (hAt : Program.instrAtPc program query = some (pc, instr)) :
    Instr.usesCallCreate instr = false :=
  instr_usesCallCreate_false_of_instrAtPcFrom hNoCallCreate hAt

theorem targetInstr_usesCallCreate_false_of_emitInstr_mem
    {program : Program} {pc : Nat} {instr : Instr}
    {emitted : List LocatedTarget} {located : LocatedTarget}
    (hNoInstr : Instr.usesCallCreate instr = false)
    (hEmit : emitInstr? program pc instr = some emitted)
    (hMem : located ∈ emitted) :
    targetInstrUsesCallCreate located.instr = false := by
  cases instr with
  | label name =>
      simp [emitInstr?] at hEmit
      subst emitted
      simp [targetInstrUsesCallCreate] at hMem ⊢
      cases hMem
      rfl
  | prim op =>
      simp [emitInstr?, Instr.usesCallCreate] at hEmit hNoInstr
      subst emitted
      simp [targetInstrUsesCallCreate] at hMem ⊢
      cases hMem
      simpa [PrimOp.isCallCreate] using hNoInstr
  | push value =>
      simp [emitInstr?] at hEmit
      subst emitted
      simp [targetInstrUsesCallCreate] at hMem ⊢
      cases hMem
      rfl
  | jump target =>
      cases hDest : Program.labelPc program target with
      | none =>
          simp [emitInstr?, hDest] at hEmit
      | some dest =>
          simp [emitInstr?, hDest] at hEmit
          subst emitted
          simp [targetInstrUsesCallCreate] at hMem ⊢
          rcases hMem with rfl | hMem
          · rfl
          · rcases hMem with rfl | hFalse
            · rfl
  | jumpi target =>
      cases hDest : Program.labelPc program target with
      | none =>
          simp [emitInstr?, hDest] at hEmit
      | some dest =>
          simp [emitInstr?, hDest] at hEmit
          subst emitted
          simp [targetInstrUsesCallCreate] at hMem ⊢
          rcases hMem with rfl | hMem
          · rfl
          · rcases hMem with rfl | hFalse
            · rfl

theorem targetInstr_usesCallCreate_false_of_program_noCall_emit_mem
    {program : Program} {query pc : Nat} {instr : Instr}
    {emitted : List LocatedTarget} {located : LocatedTarget}
    (hNoCallCreate : Program.usesCallCreate program = false)
    (hAt : Program.instrAtPc program query = some (pc, instr))
    (hEmit : emitInstr? program pc instr = some emitted)
    (hMem : located ∈ emitted) :
    targetInstrUsesCallCreate located.instr = false :=
  targetInstr_usesCallCreate_false_of_emitInstr_mem
    (instr_usesCallCreate_false_of_instrAtPc hNoCallCreate hAt)
    hEmit hMem

theorem EVM_step_targetInstr_eq_of_no_call_create {fuel gasCost : Nat}
    {state : EVMState} {instr : TargetInstr}
    (hNoCallCreate : targetInstrUsesCallCreate instr = false) :
    EvmYul.EVM.step fuel.succ gasCost
        (some (instr.op, instr.arg)) state =
      EvmYul.step instr.op instr.arg
        { state with
          gasAvailable := state.gasAvailable - EvmYul.UInt256.ofNat gasCost,
          execLength := state.execLength + 1 } := by
  cases instr with
  | push32 value => rfl
  | jump => rfl
  | jumpi => rfl
  | jumpdest => rfl
  | prim op =>
      cases op <;>
        simp [targetInstrUsesCallCreate, PrimOp.isCallCreate] at hNoCallCreate
      all_goals rfl

theorem EvmYul_step_eq_continuingStep_run {op : PrimOp} {step : PrimStep}
    (hStep : op.continuingStep? = some step)
    (hNotReturndatacopy : step ≠ PrimStep.returndatacopy)
    (hNotPop : step ≠ PrimStep.pop)
    (hNotMload : step ≠ PrimStep.mload)
    (hNotLog0 : step ≠ PrimStep.log0)
    (hNotLog1 : step ≠ PrimStep.log1)
    (hNotLog2 : step ≠ PrimStep.log2)
    (hNotLog3 : step ≠ PrimStep.log3)
    (hNotLog4 : step ≠ PrimStep.log4)
    (state : EVMState) :
    EvmYul.step op.toEVM none state = step.run state := by
  cases op <;> simp [PrimOp.continuingStep?] at hStep
  all_goals cases hStep
  case returndatacopy.refl => exact False.elim (hNotReturndatacopy rfl)
  case pop.refl => exact False.elim (hNotPop rfl)
  case mload.refl => exact False.elim (hNotMload rfl)
  case log0.refl => exact False.elim (hNotLog0 rfl)
  case log1.refl => exact False.elim (hNotLog1 rfl)
  case log2.refl => exact False.elim (hNotLog2 rfl)
  case log3.refl => exact False.elim (hNotLog3 rfl)
  case log4.refl => exact False.elim (hNotLog4 rfl)
  all_goals rfl

theorem EvmYul_step_pop_eq_PrimStep_run (state : EVMState) :
    EvmYul.step (τ := .EVM) EvmYul.Operation.POP none state =
      PrimStep.pop.run state := by
  cases state with
  | mk shared pc stack execLength =>
      cases stack <;> rfl

theorem EvmYul_step_mload_eq_PrimStep_run (state : EVMState) :
    EvmYul.step (τ := .EVM) EvmYul.Operation.MLOAD none state =
      PrimStep.mload.run state := by
  cases state with
  | mk shared pc stack execLength =>
      cases stack <;> rfl

theorem EvmYul_step_returndatacopy_eq_PrimStep_run (state : EVMState) :
    EvmYul.step (τ := .EVM) EvmYul.Operation.RETURNDATACOPY none state =
      PrimStep.returndatacopy.run state := by
  cases state with
  | mk shared pc stack execLength =>
      cases stack with
      | nil => rfl
      | cons first rest =>
          cases rest with
          | nil => rfl
          | cons second rest =>
              cases rest with
              | nil => rfl
              | cons third rest => rfl

theorem EvmYul_step_log0_eq_PrimStep_run (state : EVMState) :
    EvmYul.step (τ := .EVM) EvmYul.Operation.LOG0 none state =
      PrimStep.log0.run state := by
  cases state with
  | mk shared pc stack execLength =>
      cases stack with
      | nil => rfl
      | cons first rest =>
          cases rest with
          | nil => rfl
          | cons second rest => rfl

theorem EvmYul_step_log1_eq_PrimStep_run (state : EVMState) :
    EvmYul.step (τ := .EVM) EvmYul.Operation.LOG1 none state =
      PrimStep.log1.run state := by
  cases state with
  | mk shared pc stack execLength =>
      cases stack with
      | nil => rfl
      | cons first rest =>
          cases rest with
          | nil => rfl
          | cons second rest =>
              cases rest with
              | nil => rfl
              | cons third rest => rfl

theorem EvmYul_step_log2_eq_PrimStep_run (state : EVMState) :
    EvmYul.step (τ := .EVM) EvmYul.Operation.LOG2 none state =
      PrimStep.log2.run state := by
  cases state with
  | mk shared pc stack execLength =>
      cases stack with
      | nil => rfl
      | cons first rest =>
          cases rest with
          | nil => rfl
          | cons second rest =>
              cases rest with
              | nil => rfl
              | cons third rest =>
                  cases rest with
                  | nil => rfl
                  | cons fourth rest => rfl

theorem EvmYul_step_log3_eq_PrimStep_run (state : EVMState) :
    EvmYul.step (τ := .EVM) EvmYul.Operation.LOG3 none state =
      PrimStep.log3.run state := by
  cases state with
  | mk shared pc stack execLength =>
      cases stack with
      | nil => rfl
      | cons first rest =>
          cases rest with
          | nil => rfl
          | cons second rest =>
              cases rest with
              | nil => rfl
              | cons third rest =>
                  cases rest with
                  | nil => rfl
                  | cons fourth rest =>
                      cases rest with
                      | nil => rfl
                      | cons fifth rest => rfl

theorem EvmYul_step_log4_eq_PrimStep_run (state : EVMState) :
    EvmYul.step (τ := .EVM) EvmYul.Operation.LOG4 none state =
      PrimStep.log4.run state := by
  cases state with
  | mk shared pc stack execLength =>
      cases stack with
      | nil => rfl
      | cons first rest =>
          cases rest with
          | nil => rfl
          | cons second rest =>
              cases rest with
              | nil => rfl
              | cons third rest =>
                  cases rest with
                  | nil => rfl
                  | cons fourth rest =>
                      cases rest with
                      | nil => rfl
                      | cons fifth rest =>
                          cases rest with
                          | nil => rfl
                          | cons sixth rest => rfl

theorem EvmYul_step_eq_continuingStep_run_exact
    {op : PrimOp} {step : PrimStep}
    (hStep : op.continuingStep? = some step) (state : EVMState) :
    EvmYul.step op.toEVM none state = step.run state := by
  cases step with
  | bin f =>
      exact EvmYul_step_eq_continuingStep_run hStep
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h) state
  | un f =>
      exact EvmYul_step_eq_continuingStep_run hStep
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h) state
  | tri f =>
      exact EvmYul_step_eq_continuingStep_run hStep
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h) state
  | executionEnv f =>
      exact EvmYul_step_eq_continuingStep_run hStep
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h) state
  | unaryExecutionEnv f =>
      exact EvmYul_step_eq_continuingStep_run hStep
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h) state
  | machineState f =>
      exact EvmYul_step_eq_continuingStep_run hStep
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h) state
  | binaryMachineState f =>
      exact EvmYul_step_eq_continuingStep_run hStep
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h) state
  | binaryMachineStateWithResult f =>
      exact EvmYul_step_eq_continuingStep_run hStep
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h) state
  | ternaryMachineState f =>
      exact EvmYul_step_eq_continuingStep_run hStep
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h) state
  | state f =>
      exact EvmYul_step_eq_continuingStep_run hStep
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h) state
  | unaryState f =>
      exact EvmYul_step_eq_continuingStep_run hStep
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h) state
  | binaryState f =>
      exact EvmYul_step_eq_continuingStep_run hStep
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h) state
  | ternaryCopy f =>
      exact EvmYul_step_eq_continuingStep_run hStep
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h) state
  | quaternaryCopy f =>
      exact EvmYul_step_eq_continuingStep_run hStep
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h) state
  | pop =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      exact EvmYul_step_pop_eq_PrimStep_run state
  | mload =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      exact EvmYul_step_mload_eq_PrimStep_run state
  | returndatacopy =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      exact EvmYul_step_returndatacopy_eq_PrimStep_run state
  | dup n =>
      exact EvmYul_step_eq_continuingStep_run hStep
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h) state
  | swap n =>
      exact EvmYul_step_eq_continuingStep_run hStep
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h) state
  | log0 =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      exact EvmYul_step_log0_eq_PrimStep_run state
  | log1 =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      exact EvmYul_step_log1_eq_PrimStep_run state
  | log2 =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      exact EvmYul_step_log2_eq_PrimStep_run state
  | log3 =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      exact EvmYul_step_log3_eq_PrimStep_run state
  | log4 =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      exact EvmYul_step_log4_eq_PrimStep_run state
  | invalid =>
      exact EvmYul_step_eq_continuingStep_run hStep
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h) state

theorem mem_target_of_mem_emitted
    {target : TargetProgram} {located : LocatedTarget}
    {before emitted after : List LocatedTarget}
    (hTargetBlock : target.code = before ++ emitted ++ after)
    (hMem : located ∈ emitted) :
    located ∈ target.code := by
  rw [hTargetBlock]
  simp [hMem]

theorem decode_installed_of_mem
    {target : TargetProgram} {state : EVMState} {gas : Nat}
    {located : LocatedTarget}
    (hEncoding :
      Bytecode.EncodingCorrect target (Bytecode.encodeTarget target))
    (hMem : located ∈ target.code) :
    EvmYul.EVM.decode
        (installCodeAndGas target gas state).executionEnv.code
        (EvmYul.UInt256.ofNat located.pc) =
      some (located.instr.op, located.instr.arg) := by
  simpa [installCodeAndGas, Bytecode.decodeAt] using
    hEncoding.decodes located hMem

theorem decode_installed_of_mem_emitted
    {target : TargetProgram} {state : EVMState} {gas : Nat}
    {located : LocatedTarget} {before emitted after : List LocatedTarget}
    (hEncoding :
      Bytecode.EncodingCorrect target (Bytecode.encodeTarget target))
    (hTargetBlock : target.code = before ++ emitted ++ after)
    (hMem : located ∈ emitted) :
    EvmYul.EVM.decode
        (installCodeAndGas target gas state).executionEnv.code
        (EvmYul.UInt256.ofNat located.pc) =
      some (located.instr.op, located.instr.arg) := by
  exact decode_installed_of_mem hEncoding
    (mem_target_of_mem_emitted hTargetBlock hMem)

theorem program_instrAtPcFrom_eq_query
    {program : Program} {base query pc : Nat} {instr : Instr}
    (hAt : Program.instrAtPcFrom program base query = some (pc, instr)) :
    pc = query := by
  induction program generalizing base with
  | nil =>
      simp [Program.instrAtPcFrom] at hAt
  | cons head rest ih =>
      by_cases hEq : query = base
      · simp [Program.instrAtPcFrom, hEq] at hAt
        exact hAt.1.symm.trans hEq.symm
      · simp [Program.instrAtPcFrom, hEq] at hAt
        exact ih hAt

theorem program_instrAtPc_eq_query
    {program : Program} {query pc : Nat} {instr : Instr}
    (hAt : Program.instrAtPc program query = some (pc, instr)) :
    pc = query :=
  program_instrAtPcFrom_eq_query hAt

theorem uint256_eq_of_toNat_eq_ofNat_toNat
    {pc : Word} {n : Nat}
    (hPc : pc.toNat = n)
    (hNoWrap : (EvmYul.UInt256.ofNat n).toNat = n) :
    pc = EvmYul.UInt256.ofNat n := by
  cases pc with
  | mk pcVal =>
      unfold EvmYul.UInt256.toNat at hPc hNoWrap
      unfold EvmYul.UInt256.ofNat at hNoWrap ⊢
      simp only at hPc hNoWrap ⊢
      apply congrArg EvmYul.UInt256.mk
      exact Fin.ext (hPc.trans hNoWrap.symm)

theorem state_pc_eq_of_instrAt_of_noWrap
    {program : Program} {state : EVMState} {pc : Nat} {instr : Instr}
    (hAt : Program.instrAtPc program state.pc.toNat = some (pc, instr))
    (hNoWrap : (EvmYul.UInt256.ofNat pc).toNat = pc) :
    state.pc = EvmYul.UInt256.ofNat pc := by
  exact
      uint256_eq_of_toNat_eq_ofNat_toNat
      (pc := state.pc) (n := pc)
      (program_instrAtPc_eq_query
        (program := program) (query := state.pc.toNat) (pc := pc)
        (instr := instr) hAt).symm
      hNoWrap

theorem decode_installed_of_state_pc_mem
    {target : TargetProgram} {state : EVMState} {gas : Nat}
    {located : LocatedTarget}
    (hEncoding :
      Bytecode.EncodingCorrect target (Bytecode.encodeTarget target))
    (hMem : located ∈ target.code)
    (hPc : state.pc = EvmYul.UInt256.ofNat located.pc) :
    EvmYul.EVM.decode
        (installCodeAndGas target gas state).executionEnv.code
        state.pc =
      some (located.instr.op, located.instr.arg) := by
  rw [hPc]
  exact decode_installed_of_mem hEncoding hMem

theorem decode_installed_of_state_pc_mem_emitted
    {target : TargetProgram} {state : EVMState} {gas : Nat}
    {located : LocatedTarget} {before emitted after : List LocatedTarget}
    (hEncoding :
      Bytecode.EncodingCorrect target (Bytecode.encodeTarget target))
    (hTargetBlock : target.code = before ++ emitted ++ after)
    (hMem : located ∈ emitted)
    (hPc : state.pc = EvmYul.UInt256.ofNat located.pc) :
    EvmYul.EVM.decode
        (installCodeAndGas target gas state).executionEnv.code
        state.pc =
      some (located.instr.op, located.instr.arg) := by
  exact
    decode_installed_of_state_pc_mem hEncoding
      (mem_target_of_mem_emitted hTargetBlock hMem) hPc

theorem decode_installed_of_instrAt_mem_emitted
    {program : Program} {target : TargetProgram} {state : EVMState}
    {gas : Nat} {pc : Nat} {instr : Instr}
    {located : LocatedTarget} {before emitted after : List LocatedTarget}
    (hEncoding :
      Bytecode.EncodingCorrect target (Bytecode.encodeTarget target))
    (hAt : Program.instrAtPc program state.pc.toNat = some (pc, instr))
    (hTargetBlock : target.code = before ++ emitted ++ after)
    (hMem : located ∈ emitted)
    (hLocatedPc : located.pc = pc)
    (hNoWrap : (EvmYul.UInt256.ofNat located.pc).toNat = located.pc) :
    EvmYul.EVM.decode
        (installCodeAndGas target gas state).executionEnv.code
        state.pc =
      some (located.instr.op, located.instr.arg) := by
  have hNoWrapPc : (EvmYul.UInt256.ofNat pc).toNat = pc := by
    simpa [hLocatedPc] using hNoWrap
  have hPc := state_pc_eq_of_instrAt_of_noWrap hAt hNoWrapPc
  exact
    decode_installed_of_state_pc_mem_emitted hEncoding hTargetBlock hMem
      (by simpa [hLocatedPc] using hPc)

def staticWriteSensitive (op : EVMOp) (stack : EvmYul.Stack Word) : Prop :=
  op = EvmYul.Operation.CREATE ∨
    op = EvmYul.Operation.CREATE2 ∨
    op = EvmYul.Operation.SSTORE ∨
    op = EvmYul.Operation.SELFDESTRUCT ∨
    op = EvmYul.Operation.LOG0 ∨
    op = EvmYul.Operation.LOG1 ∨
    op = EvmYul.Operation.LOG2 ∨
    op = EvmYul.Operation.LOG3 ∨
    op = EvmYul.Operation.LOG4 ∨
    op = EvmYul.Operation.TSTORE ∨
    (op = EvmYul.Operation.CALL ∧ stack[2]? ≠ some ⟨0⟩)

def memoryGasState (state : EVMState) (op : EVMOp) : EVMState :=
  { state with
    gasAvailable :=
      state.gasAvailable -
        EvmYul.UInt256.ofNat (EvmYul.EVM.memoryExpansionCost state op) }

/--
`full` and `target` are the same EVM state up to the gasful runner's bookkeeping
fields.  This is stronger than `eraseGas full = eraseGas target`, and is the
right local invariant for replaying gas-aware `EVM.X` steps against the gasless
target interpreter.
-/
def GasExecRel (full target : EVMState) : Prop :=
  full =
    { target with
      gasAvailable := full.gasAvailable,
      execLength := full.execLength }

namespace GasExecRel

theorem refl (state : EVMState) : GasExecRel state state := by
  simp [GasExecRel]

theorem eraseGas_eq {full target : EVMState}
    (hRel : GasExecRel full target) :
    eraseGas full = eraseGas target := by
  rw [hRel]
  simp [eraseGas]

theorem pc_eq {full target : EVMState}
    (hRel : GasExecRel full target) :
    full.pc = target.pc := by
  rw [hRel]

theorem stack_eq {full target : EVMState}
    (hRel : GasExecRel full target) :
    full.stack = target.stack := by
  rw [hRel]

theorem executionEnv_eq {full target : EVMState}
    (hRel : GasExecRel full target) :
    full.executionEnv = target.executionEnv := by
  rw [hRel]

theorem code_eq {full target : EVMState}
    (hRel : GasExecRel full target) :
    full.executionEnv.code = target.executionEnv.code := by
  rw [hRel]

theorem installCodeAndGas_of_code_eq {target : TargetProgram}
    {gas : Nat} {initial : EVMState}
    (hCode :
      initial.executionEnv.code = Bytecode.encodeTarget target) :
    GasExecRel (installCodeAndGas target gas initial) initial := by
  cases initial with
  | mk shared pc stack execLength =>
      cases shared with
      | mk state machine =>
          cases state with
          | mk accountMap σ₀ totalGasUsedInBlock transactionReceipts substate
              executionEnv blocks genesisBlockHeader createdAccounts =>
              cases executionEnv
              simp [GasExecRel, installCodeAndGas] at hCode ⊢
              exact hCode.symm

theorem memoryGasState_left {full target : EVMState} {op : EVMOp}
    (hRel : GasExecRel full target) :
    GasExecRel (memoryGasState full op) target := by
  rw [hRel]
  simp [GasExecRel, memoryGasState]

theorem memoryGasState_both {full target : EVMState} {op : EVMOp}
    (hRel : GasExecRel full target) :
    GasExecRel (memoryGasState full op) (memoryGasState target op) := by
  rw [hRel]
  simp [GasExecRel, memoryGasState]

theorem charge_left {full target : EVMState} {cost : Nat}
    (hRel : GasExecRel full target) :
    GasExecRel
      { full with
        gasAvailable := full.gasAvailable - EvmYul.UInt256.ofNat cost,
        execLength := full.execLength + 1 }
      target := by
  rw [hRel]
  simp [GasExecRel]

theorem xCharged_left {full target : EVMState} {op : EVMOp} {cost : Nat}
    (hRel : GasExecRel full target) :
    GasExecRel
      { memoryGasState full op with
        gasAvailable :=
          (memoryGasState full op).gasAvailable - EvmYul.UInt256.ofNat cost,
        execLength := (memoryGasState full op).execLength + 1 }
      target := by
  exact (hRel.memoryGasState_left (op := op)).charge_left (cost := cost)

theorem replaceStackAndIncrPC_left {full target : EVMState}
    (hRel : GasExecRel full target) (stack : EvmYul.Stack Word)
    (pcΔ : Nat := 1) :
    GasExecRel
      (EvmYul.EVM.State.replaceStackAndIncrPC full stack pcΔ)
      (EvmYul.EVM.State.replaceStackAndIncrPC target stack pcΔ) := by
  rw [hRel]
  simp [GasExecRel, EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC]

theorem set_pc_stack_left {full target : EVMState}
    (hRel : GasExecRel full target) (pc : Word)
    (stack : EvmYul.Stack Word) :
    GasExecRel
      { full with pc := pc, stack := stack }
      { target with pc := pc, stack := stack } := by
  rw [hRel]
  simp [GasExecRel]

end GasExecRel

theorem EvmYul_step_push32_preserves_gasExecRel
    {full target fullPost targetPost : EVMState} {value : Word}
    (hRel : GasExecRel full target)
    (hTarget :
      Target.stepInstr (TargetInstr.push32 value) target = .ok targetPost)
    (hFull :
      EvmYul.step (TargetInstr.push32 value).op
        (TargetInstr.push32 value).arg full = .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [hRel] at hFull
  simp [Target.stepInstr] at hTarget
  cases hTarget
  change
    Except.ok
      (EvmYul.EVM.State.replaceStackAndIncrPC
        { target with
          gasAvailable := full.gasAvailable,
          execLength := full.execLength }
        (target.stack.push value) (pcΔ := 33)) = .ok fullPost at hFull
  cases hFull
  simp [GasExecRel, EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC]

theorem EvmYul_step_jump_of_stack
    (state : EVMState) (stack : EvmYul.Stack Word) (dest : Word)
    (hStack : state.stack = dest :: stack) :
    EvmYul.step EvmYul.Operation.JUMP none state =
      .ok { state with pc := dest, stack := stack } := by
  cases state with
  | mk shared pc stateStack execLength =>
      simp at hStack
      subst stateStack
      rfl

theorem stack_eq_cons_of_pop {stack rest : EvmYul.Stack Word} {head : Word}
    (hPop : EvmYul.Stack.pop stack = some (rest, head)) :
    stack = head :: rest := by
  cases stack with
  | nil =>
      simp [EvmYul.Stack.pop] at hPop
  | cons hd tl =>
      simp [EvmYul.Stack.pop] at hPop
      rcases hPop with ⟨hRest, hHead⟩
      subst rest
      subst head
      rfl

theorem EvmYul_step_jumpi_of_stack
    (state : EVMState) (stack : EvmYul.Stack Word)
    (dest cond : Word)
    (hStack : state.stack = dest :: cond :: stack) :
    EvmYul.step EvmYul.Operation.JUMPI none state =
      .ok
        { state with
          pc :=
            if cond != EvmYul.UInt256.ofNat 0 then
              dest
            else
              state.pc + EvmYul.UInt256.ofNat 1,
          stack := stack } := by
  cases state with
  | mk shared pc stateStack execLength =>
      simp at hStack
      subst stateStack
      rfl

theorem stack_eq_cons_cons_of_pop2
    {stack rest : EvmYul.Stack Word} {first second : Word}
    (hPop : EvmYul.Stack.pop2 stack = some (rest, first, second)) :
    stack = first :: second :: rest := by
  cases stack with
  | nil =>
      simp [EvmYul.Stack.pop2] at hPop
  | cons hd tl =>
      cases tl with
      | nil =>
          simp [EvmYul.Stack.pop2] at hPop
      | cons hd₁ tl₁ =>
          simp [EvmYul.Stack.pop2] at hPop
          rcases hPop with ⟨hRest, hFirst, hSecond⟩
          subst rest
          subst first
          subst second
          rfl

theorem EvmYul_step_jumpdest_eq (state : EVMState) :
    EvmYul.step EvmYul.Operation.JUMPDEST none state =
      .ok (EvmYul.EVM.State.incrPC state) := by
  cases state
  rfl

theorem EvmYul_step_jump_preserves_gasExecRel
    {full target fullPost targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : Target.stepInstr TargetInstr.jump target = .ok targetPost)
    (hFull :
      EvmYul.step TargetInstr.jump.op TargetInstr.jump.arg full =
        .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [hRel] at hFull
  simp only [TargetInstr.op, TargetInstr.arg] at hFull
  let fullGas : EVMState :=
    { target with
      gasAvailable := full.gasAvailable,
      execLength := full.execLength }
  change
    EvmYul.step
        (EvmYul.Operation.StackMemFlow EvmYul.Operation.SMSFOp.JUMP)
        none fullGas = .ok fullPost at hFull
  cases hPop : target.stack.pop with
  | none =>
      simp [Target.stepInstr, hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, dest⟩
      simp [Target.stepInstr, hPop] at hTarget
      cases hTarget
      have hPopFull :
          ({ target with
            gasAvailable := full.gasAvailable,
            execLength := full.execLength } : EVMState).stack.pop =
            some (stack, dest) := by
        simpa using hPop
      have hStackTarget : target.stack = dest :: stack :=
        stack_eq_cons_of_pop hPop
      have hStackFull : fullGas.stack = dest :: stack := by
        simpa [fullGas] using hStackTarget
      rw [EvmYul_step_jump_of_stack fullGas stack dest hStackFull] at hFull
      cases hFull
      simp [GasExecRel, fullGas]

theorem EvmYul_step_jumpi_preserves_gasExecRel
    {full target fullPost targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : Target.stepInstr TargetInstr.jumpi target = .ok targetPost)
    (hFull :
      EvmYul.step TargetInstr.jumpi.op TargetInstr.jumpi.arg full =
        .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [hRel] at hFull
  simp only [TargetInstr.op, TargetInstr.arg] at hFull
  let fullGas : EVMState :=
    { target with
      gasAvailable := full.gasAvailable,
      execLength := full.execLength }
  change
    EvmYul.step
        (EvmYul.Operation.StackMemFlow EvmYul.Operation.SMSFOp.JUMPI)
        none fullGas = .ok fullPost at hFull
  cases hPop : target.stack.pop2 with
  | none =>
      simp [Target.stepInstr, hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, dest, cond⟩
      simp [Target.stepInstr, hPop] at hTarget
      cases hTarget
      have hStackTarget : target.stack = dest :: cond :: stack :=
        stack_eq_cons_cons_of_pop2 hPop
      have hStackFull : fullGas.stack = dest :: cond :: stack := by
        simpa [fullGas] using hStackTarget
      rw [EvmYul_step_jumpi_of_stack fullGas stack dest cond hStackFull] at hFull
      cases hFull
      simp [GasExecRel, fullGas]

theorem EvmYul_step_jumpdest_preserves_gasExecRel
    {full target fullPost targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : Target.stepInstr TargetInstr.jumpdest target = .ok targetPost)
    (hFull :
      EvmYul.step TargetInstr.jumpdest.op TargetInstr.jumpdest.arg full =
        .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [hRel] at hFull
  simp only [TargetInstr.op, TargetInstr.arg] at hFull
  simp [Target.stepInstr] at hTarget
  cases hTarget
  rw [EvmYul_step_jumpdest_eq
    ({ target with
      gasAvailable := full.gasAvailable,
      execLength := full.execLength } : EVMState)] at hFull
  cases hFull
  simp [GasExecRel, EvmYul.EVM.State.incrPC]

theorem PrimStep_run_bin_preserves_gasExecRel
    (f : EvmYul.Primop.Binary)
    {full target fullPost targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : (PrimStep.bin f).run target = .ok targetPost)
    (hFull : (PrimStep.bin f).run full = .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [hRel] at hFull
  cases hPop : target.stack.pop2 with
  | none =>
      simp [PrimStep.run, EvmYul.EVM.execBinOp, hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, left, right⟩
      simp [PrimStep.run, EvmYul.EVM.execBinOp, hPop] at hTarget
      cases hTarget
      have hPopFull :
          ({ target with
            gasAvailable := full.gasAvailable,
            execLength := full.execLength } : EVMState).stack.pop2 =
            some (stack, left, right) := by
        simpa using hPop
      simp [PrimStep.run, EvmYul.EVM.execBinOp, hPopFull] at hFull
      cases hFull
      simp [GasExecRel, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]

theorem PrimStep_run_un_preserves_gasExecRel
    (f : EvmYul.Primop.Unary)
    {full target fullPost targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : (PrimStep.un f).run target = .ok targetPost)
    (hFull : (PrimStep.un f).run full = .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [hRel] at hFull
  cases hPop : target.stack.pop with
  | none =>
      simp [PrimStep.run, EvmYul.EVM.execUnOp, hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, value⟩
      simp [PrimStep.run, EvmYul.EVM.execUnOp, hPop] at hTarget
      cases hTarget
      have hPopFull :
          ({ target with
            gasAvailable := full.gasAvailable,
            execLength := full.execLength } : EVMState).stack.pop =
            some (stack, value) := by
        simpa using hPop
      simp [PrimStep.run, EvmYul.EVM.execUnOp, hPopFull] at hFull
      cases hFull
      simp [GasExecRel, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]

theorem PrimStep_run_tri_preserves_gasExecRel
    (f : EvmYul.Primop.Ternary)
    {full target fullPost targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : (PrimStep.tri f).run target = .ok targetPost)
    (hFull : (PrimStep.tri f).run full = .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [hRel] at hFull
  cases hPop : target.stack.pop3 with
  | none =>
      simp [PrimStep.run, EvmYul.EVM.execTriOp, hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, first, second, third⟩
      simp [PrimStep.run, EvmYul.EVM.execTriOp, hPop] at hTarget
      cases hTarget
      have hPopFull :
          ({ target with
            gasAvailable := full.gasAvailable,
            execLength := full.execLength } : EVMState).stack.pop3 =
            some (stack, first, second, third) := by
        simpa using hPop
      simp [PrimStep.run, EvmYul.EVM.execTriOp, hPopFull] at hFull
      cases hFull
      simp [GasExecRel, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]

theorem PrimStep_run_executionEnv_preserves_gasExecRel
    (f : EvmYul.ExecutionEnv EvmYul.OperationType.EVM → Word)
    {full target fullPost targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : (PrimStep.executionEnv f).run target = .ok targetPost)
    (hFull : (PrimStep.executionEnv f).run full = .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [hRel] at hFull
  simp [PrimStep.run, EvmYul.EVM.executionEnvOp] at hTarget hFull
  cases hTarget
  cases hFull
  simp [GasExecRel, EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC]

theorem PrimStep_run_state_preserves_gasExecRel
    (f : EvmYul.State EvmYul.OperationType.EVM → Word)
    {full target fullPost targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : (PrimStep.state f).run target = .ok targetPost)
    (hFull : (PrimStep.state f).run full = .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [hRel] at hFull
  simp [PrimStep.run, EvmYul.EVM.stateOp] at hTarget hFull
  cases hTarget
  cases hFull
  simp [GasExecRel, EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC]

theorem PrimStep_run_unaryExecutionEnv_preserves_gasExecRel
    (f : EvmYul.ExecutionEnv EvmYul.OperationType.EVM → Word → Word)
    {full target fullPost targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : (PrimStep.unaryExecutionEnv f).run target = .ok targetPost)
    (hFull : (PrimStep.unaryExecutionEnv f).run full = .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [hRel] at hFull
  cases hPop : target.stack.pop with
  | none =>
      simp [PrimStep.run, EvmYul.EVM.unaryExecutionEnvOp, hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, value⟩
      simp [PrimStep.run, EvmYul.EVM.unaryExecutionEnvOp, hPop] at hTarget
      cases hTarget
      have hPopFull :
          ({ target with
            gasAvailable := full.gasAvailable,
            execLength := full.execLength } : EVMState).stack.pop =
            some (stack, value) := by
        simpa using hPop
      simp [PrimStep.run, EvmYul.EVM.unaryExecutionEnvOp, hPopFull] at hFull
      cases hFull
      simp [GasExecRel, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]

theorem PrimStep_run_unaryState_preserves_gasExecRel
    (f :
      EvmYul.State EvmYul.OperationType.EVM → Word →
        EvmYul.State EvmYul.OperationType.EVM × Word)
    {full target fullPost targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : (PrimStep.unaryState f).run target = .ok targetPost)
    (hFull : (PrimStep.unaryState f).run full = .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [hRel] at hFull
  cases hPop : target.stack.pop with
  | none =>
      simp [PrimStep.run, EvmYul.EVM.unaryStateOp, hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, value⟩
      simp [PrimStep.run, EvmYul.EVM.unaryStateOp, hPop] at hTarget
      cases hTarget
      have hPopFull :
          ({ target with
            gasAvailable := full.gasAvailable,
            execLength := full.execLength } : EVMState).stack.pop =
            some (stack, value) := by
        simpa using hPop
      simp [PrimStep.run, EvmYul.EVM.unaryStateOp, hPopFull] at hFull
      cases hFull
      simp [GasExecRel, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]

theorem PrimStep_run_binaryState_preserves_gasExecRel
    (f :
      EvmYul.State EvmYul.OperationType.EVM → Word → Word →
        EvmYul.State EvmYul.OperationType.EVM)
    {full target fullPost targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : (PrimStep.binaryState f).run target = .ok targetPost)
    (hFull : (PrimStep.binaryState f).run full = .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [hRel] at hFull
  cases hPop : target.stack.pop2 with
  | none =>
      simp [PrimStep.run, EvmYul.EVM.binaryStateOp, hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, left, right⟩
      simp [PrimStep.run, EvmYul.EVM.binaryStateOp, hPop] at hTarget
      cases hTarget
      have hPopFull :
          ({ target with
            gasAvailable := full.gasAvailable,
            execLength := full.execLength } : EVMState).stack.pop2 =
            some (stack, left, right) := by
        simpa using hPop
      simp [PrimStep.run, EvmYul.EVM.binaryStateOp, hPopFull] at hFull
      cases hFull
      simp [GasExecRel, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]

theorem PrimStep_run_pop_preserves_gasExecRel
    {full target fullPost targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : PrimStep.pop.run target = .ok targetPost)
    (hFull : PrimStep.pop.run full = .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [hRel] at hFull
  cases hPop : target.stack.pop with
  | none =>
      simp [PrimStep.run, hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, value⟩
      simp [PrimStep.run, hPop] at hTarget
      cases hTarget
      have hPopFull :
          ({ target with
            gasAvailable := full.gasAvailable,
            execLength := full.execLength } : EVMState).stack.pop =
            some (stack, value) := by
        simpa using hPop
      simp [PrimStep.run, hPopFull] at hFull
      cases hFull
      simp [GasExecRel, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]

theorem PrimStep_run_bin_exists_gasExecRel
    (f : EvmYul.Primop.Binary)
    {full target targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : (PrimStep.bin f).run target = .ok targetPost) :
    ∃ fullPost,
      (PrimStep.bin f).run full = .ok fullPost ∧
        GasExecRel fullPost targetPost := by
  rw [hRel]
  cases hPop : target.stack.pop2 with
  | none =>
      simp [PrimStep.run, EvmYul.EVM.execBinOp, hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, left, right⟩
      simp [PrimStep.run, EvmYul.EVM.execBinOp, hPop] at hTarget
      cases hTarget
      let fullState : EVMState :=
        { target with
          gasAvailable := full.gasAvailable,
          execLength := full.execLength }
      refine
        ⟨EvmYul.EVM.State.replaceStackAndIncrPC fullState
            (stack.push (f left right)),
          ?_, ?_⟩
      · simp [PrimStep.run, EvmYul.EVM.execBinOp, hPop, fullState]
        rfl
      · simp [GasExecRel, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, fullState]

theorem PrimStep_run_un_exists_gasExecRel
    (f : EvmYul.Primop.Unary)
    {full target targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : (PrimStep.un f).run target = .ok targetPost) :
    ∃ fullPost,
      (PrimStep.un f).run full = .ok fullPost ∧
        GasExecRel fullPost targetPost := by
  rw [hRel]
  cases hPop : target.stack.pop with
  | none =>
      simp [PrimStep.run, EvmYul.EVM.execUnOp, hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, value⟩
      simp [PrimStep.run, EvmYul.EVM.execUnOp, hPop] at hTarget
      cases hTarget
      let fullState : EVMState :=
        { target with
          gasAvailable := full.gasAvailable,
          execLength := full.execLength }
      refine
        ⟨EvmYul.EVM.State.replaceStackAndIncrPC fullState
            (stack.push (f value)),
          ?_, ?_⟩
      · simp [PrimStep.run, EvmYul.EVM.execUnOp, hPop, fullState]
        rfl
      · simp [GasExecRel, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, fullState]

theorem PrimStep_run_tri_exists_gasExecRel
    (f : EvmYul.Primop.Ternary)
    {full target targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : (PrimStep.tri f).run target = .ok targetPost) :
    ∃ fullPost,
      (PrimStep.tri f).run full = .ok fullPost ∧
        GasExecRel fullPost targetPost := by
  rw [hRel]
  cases hPop : target.stack.pop3 with
  | none =>
      simp [PrimStep.run, EvmYul.EVM.execTriOp, hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, first, second, third⟩
      simp [PrimStep.run, EvmYul.EVM.execTriOp, hPop] at hTarget
      cases hTarget
      let fullState : EVMState :=
        { target with
          gasAvailable := full.gasAvailable,
          execLength := full.execLength }
      refine
        ⟨EvmYul.EVM.State.replaceStackAndIncrPC fullState
            (stack.push (f first second third)),
          ?_, ?_⟩
      · simp [PrimStep.run, EvmYul.EVM.execTriOp, hPop, fullState]
        rfl
      · simp [GasExecRel, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, fullState]

theorem PrimStep_run_executionEnv_exists_gasExecRel
    (f : EvmYul.ExecutionEnv EvmYul.OperationType.EVM → Word)
    {full target targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : (PrimStep.executionEnv f).run target = .ok targetPost) :
    ∃ fullPost,
      (PrimStep.executionEnv f).run full = .ok fullPost ∧
        GasExecRel fullPost targetPost := by
  rw [hRel]
  simp [PrimStep.run, EvmYul.EVM.executionEnvOp] at hTarget
  cases hTarget
  let fullState : EVMState :=
    { target with
      gasAvailable := full.gasAvailable,
      execLength := full.execLength }
  refine
    ⟨EvmYul.EVM.State.replaceStackAndIncrPC fullState
        (target.stack.push (f target.executionEnv)),
      ?_, ?_⟩
  · simp [PrimStep.run, EvmYul.EVM.executionEnvOp, fullState]
    rfl
  · simp [GasExecRel, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, fullState]

theorem PrimStep_run_state_exists_gasExecRel
    (f : EvmYul.State EvmYul.OperationType.EVM → Word)
    {full target targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : (PrimStep.state f).run target = .ok targetPost) :
    ∃ fullPost,
      (PrimStep.state f).run full = .ok fullPost ∧
        GasExecRel fullPost targetPost := by
  rw [hRel]
  simp [PrimStep.run, EvmYul.EVM.stateOp] at hTarget
  cases hTarget
  let fullState : EVMState :=
    { target with
      gasAvailable := full.gasAvailable,
      execLength := full.execLength }
  refine
    ⟨EvmYul.EVM.State.replaceStackAndIncrPC fullState
        (target.stack.push (f target.toState)),
      ?_, ?_⟩
  · simp [PrimStep.run, EvmYul.EVM.stateOp, fullState]
    rfl
  · simp [GasExecRel, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, fullState]

theorem PrimStep_run_unaryExecutionEnv_exists_gasExecRel
    (f : EvmYul.ExecutionEnv EvmYul.OperationType.EVM → Word → Word)
    {full target targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : (PrimStep.unaryExecutionEnv f).run target = .ok targetPost) :
    ∃ fullPost,
      (PrimStep.unaryExecutionEnv f).run full = .ok fullPost ∧
        GasExecRel fullPost targetPost := by
  rw [hRel]
  cases hPop : target.stack.pop with
  | none =>
      simp [PrimStep.run, EvmYul.EVM.unaryExecutionEnvOp, hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, value⟩
      simp [PrimStep.run, EvmYul.EVM.unaryExecutionEnvOp, hPop] at hTarget
      cases hTarget
      let fullState : EVMState :=
        { target with
          gasAvailable := full.gasAvailable,
          execLength := full.execLength }
      refine
        ⟨EvmYul.EVM.State.replaceStackAndIncrPC fullState
            (stack.push (f target.executionEnv value)),
          ?_, ?_⟩
      · simp [PrimStep.run, EvmYul.EVM.unaryExecutionEnvOp, hPop,
          fullState]
        rfl
      · simp [GasExecRel, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, fullState]

theorem PrimStep_run_unaryState_exists_gasExecRel
    (f :
      EvmYul.State EvmYul.OperationType.EVM → Word →
        EvmYul.State EvmYul.OperationType.EVM × Word)
    {full target targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : (PrimStep.unaryState f).run target = .ok targetPost) :
    ∃ fullPost,
      (PrimStep.unaryState f).run full = .ok fullPost ∧
        GasExecRel fullPost targetPost := by
  rw [hRel]
  cases hPop : target.stack.pop with
  | none =>
      simp [PrimStep.run, EvmYul.EVM.unaryStateOp, hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, value⟩
      simp [PrimStep.run, EvmYul.EVM.unaryStateOp, hPop] at hTarget
      cases hTarget
      let result := f target.toState value
      let fullState : EVMState :=
        { target with
          gasAvailable := full.gasAvailable,
          execLength := full.execLength }
      refine
        ⟨EvmYul.EVM.State.replaceStackAndIncrPC
            { fullState with toState := result.1 }
            (stack.push result.2),
          ?_, ?_⟩
      · simp [PrimStep.run, EvmYul.EVM.unaryStateOp, hPop, fullState,
          result]
        rfl
      · simp [GasExecRel, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, fullState, result]

theorem PrimStep_run_binaryState_exists_gasExecRel
    (f :
      EvmYul.State EvmYul.OperationType.EVM → Word → Word →
        EvmYul.State EvmYul.OperationType.EVM)
    {full target targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : (PrimStep.binaryState f).run target = .ok targetPost) :
    ∃ fullPost,
      (PrimStep.binaryState f).run full = .ok fullPost ∧
        GasExecRel fullPost targetPost := by
  rw [hRel]
  cases hPop : target.stack.pop2 with
  | none =>
      simp [PrimStep.run, EvmYul.EVM.binaryStateOp, hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, left, right⟩
      simp [PrimStep.run, EvmYul.EVM.binaryStateOp, hPop] at hTarget
      cases hTarget
      let fullState : EVMState :=
        { target with
          gasAvailable := full.gasAvailable,
          execLength := full.execLength }
      refine
        ⟨EvmYul.EVM.State.replaceStackAndIncrPC
            { fullState with toState := f target.toState left right }
            stack,
          ?_, ?_⟩
      · simp [PrimStep.run, EvmYul.EVM.binaryStateOp, hPop, fullState]
        rfl
      · simp [GasExecRel, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, fullState]

theorem PrimStep_run_pop_exists_gasExecRel
    {full target targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : PrimStep.pop.run target = .ok targetPost) :
    ∃ fullPost,
      PrimStep.pop.run full = .ok fullPost ∧
        GasExecRel fullPost targetPost := by
  rw [hRel]
  cases hPop : target.stack.pop with
  | none =>
      simp [PrimStep.run, hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, _value⟩
      simp [PrimStep.run, hPop] at hTarget
      cases hTarget
      let fullState : EVMState :=
        { target with
          gasAvailable := full.gasAvailable,
          execLength := full.execLength }
      refine ⟨EvmYul.EVM.State.replaceStackAndIncrPC fullState stack, ?_, ?_⟩
      · simp [PrimStep.run, hPop, fullState]
      · simp [GasExecRel, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, fullState]

theorem PrimStep_run_machineState_preserves_gasExecRel_of_eq
    (f : EvmYul.MachineState → Word)
    {full target fullPost targetPost : EVMState}
    (hValue : f full.toMachineState = f target.toMachineState)
    (hRel : GasExecRel full target)
    (hTarget : (PrimStep.machineState f).run target = .ok targetPost)
    (hFull : (PrimStep.machineState f).run full = .ok fullPost) :
    GasExecRel fullPost targetPost := by
  have hValue' :
      f
          ({ target with
            gasAvailable := full.gasAvailable,
            execLength := full.execLength } : EVMState).toMachineState =
        f target.toMachineState := by
    have hValue'' := hValue
    rw [hRel] at hValue''
    simpa using hValue''
  rw [hRel] at hFull
  simp [PrimStep.run, EvmYul.EVM.machineStateOp] at hTarget hFull
  rw [hValue'] at hFull
  cases hTarget
  cases hFull
  simp [GasExecRel, EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC]

theorem PrimStep_run_machineState_exists_gasExecRel_of_eq
    (f : EvmYul.MachineState → Word)
    {full target targetPost : EVMState}
    (hValue : f full.toMachineState = f target.toMachineState)
    (hRel : GasExecRel full target)
    (hTarget : (PrimStep.machineState f).run target = .ok targetPost) :
    ∃ fullPost,
      (PrimStep.machineState f).run full = .ok fullPost ∧
        GasExecRel fullPost targetPost := by
  have hValue' :
      f
          ({ target with
            gasAvailable := full.gasAvailable,
            execLength := full.execLength } : EVMState).toMachineState =
        f target.toMachineState := by
    have hValue'' := hValue
    rw [hRel] at hValue''
    simpa using hValue''
  rw [hRel]
  simp [PrimStep.run, EvmYul.EVM.machineStateOp] at hTarget
  cases hTarget
  let fullState : EVMState :=
    { target with
      gasAvailable := full.gasAvailable,
      execLength := full.execLength }
  refine
    ⟨EvmYul.EVM.State.replaceStackAndIncrPC fullState
        (target.stack.push (f target.toMachineState)),
      ?_, ?_⟩
  · simp [PrimStep.run, EvmYul.EVM.machineStateOp, fullState, hValue']
    rfl
  · simp [GasExecRel, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, fullState]

theorem PrimStep_run_binaryMachineState_preserves_gasExecRel_of_rel
    (f : EvmYul.MachineState → Word → Word → EvmYul.MachineState)
    {full target fullPost targetPost : EVMState}
    (hMachine :
      ∀ {fullMachine targetMachine : EvmYul.MachineState}
        {left right : Word},
        fullMachine =
          { targetMachine with gasAvailable := fullMachine.gasAvailable } →
        f fullMachine left right =
          { f targetMachine left right with
            gasAvailable := (f fullMachine left right).gasAvailable })
    (hRel : GasExecRel full target)
    (hTarget : (PrimStep.binaryMachineState f).run target = .ok targetPost)
    (hFull : (PrimStep.binaryMachineState f).run full = .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [hRel] at hFull
  cases hPop : target.stack.pop2 with
  | none =>
      simp [PrimStep.run, EvmYul.EVM.binaryMachineStateOp, hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, left, right⟩
      simp [PrimStep.run, EvmYul.EVM.binaryMachineStateOp, hPop] at hTarget
      cases hTarget
      let fullGas : EVMState :=
        { target with
          gasAvailable := full.gasAvailable,
          execLength := full.execLength }
      have hPopFull :
          fullGas.stack.pop2 = some (stack, left, right) := by
        simpa [fullGas] using hPop
      change
        (PrimStep.binaryMachineState f).run fullGas = .ok fullPost at hFull
      simp [PrimStep.run, EvmYul.EVM.binaryMachineStateOp, hPopFull] at hFull
      cases hFull
      have hMachineRel :
          fullGas.toMachineState =
            { target.toMachineState with
              gasAvailable := fullGas.toMachineState.gasAvailable } := by
        simp [fullGas]
      have hMachine' :=
        hMachine (left := left) (right := right) hMachineRel
      rw [hMachine']
      simp [GasExecRel, fullGas, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]

theorem PrimStep_run_binaryMachineState_exists_gasExecRel_of_rel
    (f : EvmYul.MachineState → Word → Word → EvmYul.MachineState)
    {full target targetPost : EVMState}
    (hMachine :
      ∀ {fullMachine targetMachine : EvmYul.MachineState}
        {left right : Word},
        fullMachine =
          { targetMachine with gasAvailable := fullMachine.gasAvailable } →
        f fullMachine left right =
          { f targetMachine left right with
            gasAvailable := (f fullMachine left right).gasAvailable })
    (hRel : GasExecRel full target)
    (hTarget : (PrimStep.binaryMachineState f).run target = .ok targetPost) :
    ∃ fullPost,
      (PrimStep.binaryMachineState f).run full = .ok fullPost ∧
        GasExecRel fullPost targetPost := by
  rw [hRel]
  cases hPop : target.stack.pop2 with
  | none =>
      simp [PrimStep.run, EvmYul.EVM.binaryMachineStateOp, hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, left, right⟩
      simp [PrimStep.run, EvmYul.EVM.binaryMachineStateOp, hPop] at hTarget
      cases hTarget
      let fullGas : EVMState :=
        { target with
          gasAvailable := full.gasAvailable,
          execLength := full.execLength }
      have hMachineRel :
          fullGas.toMachineState =
            { target.toMachineState with
              gasAvailable := fullGas.toMachineState.gasAvailable } := by
        simp [fullGas]
      have hMachine' :=
        hMachine (left := left) (right := right) hMachineRel
      refine
        ⟨EvmYul.EVM.State.replaceStackAndIncrPC
            { fullGas with
              toMachineState := f fullGas.toMachineState left right }
            stack,
          ?_, ?_⟩
      · simp [PrimStep.run, EvmYul.EVM.binaryMachineStateOp, hPop,
          fullGas]
        rfl
      · rw [hMachine']
        simp [GasExecRel, fullGas, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC]

theorem PrimStep_run_binaryMachineStateWithResult_preserves_gasExecRel_of_rel
    (f : EvmYul.MachineState → Word → Word →
      Word × EvmYul.MachineState)
    {full target fullPost targetPost : EVMState}
    (hMachine :
      ∀ {fullMachine targetMachine : EvmYul.MachineState}
        {left right : Word},
        fullMachine =
          { targetMachine with gasAvailable := fullMachine.gasAvailable } →
        (f fullMachine left right).1 = (f targetMachine left right).1 ∧
          (f fullMachine left right).2 =
            { (f targetMachine left right).2 with
              gasAvailable := (f fullMachine left right).2.gasAvailable })
    (hRel : GasExecRel full target)
    (hTarget :
      (PrimStep.binaryMachineStateWithResult f).run target = .ok targetPost)
    (hFull :
      (PrimStep.binaryMachineStateWithResult f).run full = .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [hRel] at hFull
  cases hPop : target.stack.pop2 with
  | none =>
      simp [PrimStep.run, EvmYul.EVM.binaryMachineStateOp', hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, left, right⟩
      simp [PrimStep.run, EvmYul.EVM.binaryMachineStateOp', hPop] at hTarget
      cases hTarget
      let fullGas : EVMState :=
        { target with
          gasAvailable := full.gasAvailable,
          execLength := full.execLength }
      have hPopFull :
          fullGas.stack.pop2 = some (stack, left, right) := by
        simpa [fullGas] using hPop
      change
        (PrimStep.binaryMachineStateWithResult f).run fullGas =
          .ok fullPost at hFull
      simp [PrimStep.run, EvmYul.EVM.binaryMachineStateOp', hPopFull] at hFull
      cases hFull
      have hMachineRel :
          fullGas.toMachineState =
            { target.toMachineState with
              gasAvailable := fullGas.toMachineState.gasAvailable } := by
        simp [fullGas]
      have hMachine' :=
        hMachine (left := left) (right := right) hMachineRel
      rcases hMachine' with ⟨hValue, hState⟩
      rw [hValue, hState]
      simp [GasExecRel, fullGas, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]

theorem PrimStep_run_binaryMachineStateWithResult_exists_gasExecRel_of_rel
    (f : EvmYul.MachineState → Word → Word →
      Word × EvmYul.MachineState)
    {full target targetPost : EVMState}
    (hMachine :
      ∀ {fullMachine targetMachine : EvmYul.MachineState}
        {left right : Word},
        fullMachine =
          { targetMachine with gasAvailable := fullMachine.gasAvailable } →
        (f fullMachine left right).1 = (f targetMachine left right).1 ∧
          (f fullMachine left right).2 =
            { (f targetMachine left right).2 with
              gasAvailable := (f fullMachine left right).2.gasAvailable })
    (hRel : GasExecRel full target)
    (hTarget :
      (PrimStep.binaryMachineStateWithResult f).run target = .ok targetPost) :
    ∃ fullPost,
      (PrimStep.binaryMachineStateWithResult f).run full = .ok fullPost ∧
        GasExecRel fullPost targetPost := by
  rw [hRel]
  cases hPop : target.stack.pop2 with
  | none =>
      simp [PrimStep.run, EvmYul.EVM.binaryMachineStateOp', hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, left, right⟩
      simp [PrimStep.run, EvmYul.EVM.binaryMachineStateOp', hPop] at hTarget
      cases hTarget
      let fullGas : EVMState :=
        { target with
          gasAvailable := full.gasAvailable,
          execLength := full.execLength }
      have hMachineRel :
          fullGas.toMachineState =
            { target.toMachineState with
              gasAvailable := fullGas.toMachineState.gasAvailable } := by
        simp [fullGas]
      have hMachine' :=
        hMachine (left := left) (right := right) hMachineRel
      rcases hMachine' with ⟨hValue, hState⟩
      refine
        ⟨EvmYul.EVM.State.replaceStackAndIncrPC
            { fullGas with
              toMachineState := (f fullGas.toMachineState left right).2 }
            (stack.push (f fullGas.toMachineState left right).1),
          ?_, ?_⟩
      · simp [PrimStep.run, EvmYul.EVM.binaryMachineStateOp', hPop,
          fullGas]
        rfl
      · rw [hValue, hState]
        simp [GasExecRel, fullGas, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC]

theorem PrimStep_run_ternaryMachineState_preserves_gasExecRel_of_rel
    (f :
      EvmYul.MachineState → Word → Word → Word → EvmYul.MachineState)
    {full target fullPost targetPost : EVMState}
    (hMachine :
      ∀ {fullMachine targetMachine : EvmYul.MachineState}
        {first second third : Word},
        fullMachine =
          { targetMachine with gasAvailable := fullMachine.gasAvailable } →
        f fullMachine first second third =
          { f targetMachine first second third with
            gasAvailable :=
              (f fullMachine first second third).gasAvailable })
    (hRel : GasExecRel full target)
    (hTarget : (PrimStep.ternaryMachineState f).run target = .ok targetPost)
    (hFull : (PrimStep.ternaryMachineState f).run full = .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [hRel] at hFull
  cases hPop : target.stack.pop3 with
  | none =>
      simp [PrimStep.run, EvmYul.EVM.ternaryMachineStateOp, hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, first, second, third⟩
      simp [PrimStep.run, EvmYul.EVM.ternaryMachineStateOp, hPop] at hTarget
      cases hTarget
      let fullGas : EVMState :=
        { target with
          gasAvailable := full.gasAvailable,
          execLength := full.execLength }
      have hPopFull :
          fullGas.stack.pop3 = some (stack, first, second, third) := by
        simpa [fullGas] using hPop
      change
        (PrimStep.ternaryMachineState f).run fullGas = .ok fullPost at hFull
      simp [PrimStep.run, EvmYul.EVM.ternaryMachineStateOp, hPopFull] at hFull
      cases hFull
      have hMachineRel :
          fullGas.toMachineState =
            { target.toMachineState with
              gasAvailable := fullGas.toMachineState.gasAvailable } := by
        simp [fullGas]
      have hMachine' :=
        hMachine (first := first) (second := second) (third := third)
          hMachineRel
      rw [hMachine']
      simp [GasExecRel, fullGas, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]

theorem PrimStep_run_ternaryMachineState_exists_gasExecRel_of_rel
    (f :
      EvmYul.MachineState → Word → Word → Word → EvmYul.MachineState)
    {full target targetPost : EVMState}
    (hMachine :
      ∀ {fullMachine targetMachine : EvmYul.MachineState}
        {first second third : Word},
        fullMachine =
          { targetMachine with gasAvailable := fullMachine.gasAvailable } →
        f fullMachine first second third =
          { f targetMachine first second third with
            gasAvailable :=
              (f fullMachine first second third).gasAvailable })
    (hRel : GasExecRel full target)
    (hTarget : (PrimStep.ternaryMachineState f).run target = .ok targetPost) :
    ∃ fullPost,
      (PrimStep.ternaryMachineState f).run full = .ok fullPost ∧
        GasExecRel fullPost targetPost := by
  rw [hRel]
  cases hPop : target.stack.pop3 with
  | none =>
      simp [PrimStep.run, EvmYul.EVM.ternaryMachineStateOp, hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, first, second, third⟩
      simp [PrimStep.run, EvmYul.EVM.ternaryMachineStateOp, hPop] at hTarget
      cases hTarget
      let fullGas : EVMState :=
        { target with
          gasAvailable := full.gasAvailable,
          execLength := full.execLength }
      have hMachineRel :
          fullGas.toMachineState =
            { target.toMachineState with
              gasAvailable := fullGas.toMachineState.gasAvailable } := by
        simp [fullGas]
      have hMachine' :=
        hMachine (first := first) (second := second) (third := third)
          hMachineRel
      refine
        ⟨EvmYul.EVM.State.replaceStackAndIncrPC
            { fullGas with
              toMachineState :=
                f fullGas.toMachineState first second third }
            stack,
          ?_, ?_⟩
      · simp [PrimStep.run, EvmYul.EVM.ternaryMachineStateOp, hPop,
          fullGas]
        rfl
      · rw [hMachine']
        simp [GasExecRel, fullGas, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC]

theorem PrimStep_run_ternaryCopy_preserves_gasExecRel_of_rel
    (f :
      EvmYul.SharedState .EVM → Word → Word → Word →
        EvmYul.SharedState .EVM)
    {full target fullPost targetPost : EVMState}
    (hShared :
      ∀ {fullShared targetShared : EvmYul.SharedState .EVM}
        {first second third : Word},
        fullShared =
          { targetShared with
            toMachineState :=
              { targetShared.toMachineState with
                gasAvailable := fullShared.toMachineState.gasAvailable } } →
        f fullShared first second third =
          { f targetShared first second third with
            toMachineState :=
              { (f targetShared first second third).toMachineState with
                gasAvailable :=
                  (f fullShared first second third).toMachineState.gasAvailable } })
    (hRel : GasExecRel full target)
    (hTarget : (PrimStep.ternaryCopy f).run target = .ok targetPost)
    (hFull : (PrimStep.ternaryCopy f).run full = .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [hRel] at hFull
  cases hPop : target.stack.pop3 with
  | none =>
      simp [PrimStep.run, EvmYul.EVM.ternaryCopyOp, hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, first, second, third⟩
      simp [PrimStep.run, EvmYul.EVM.ternaryCopyOp, hPop] at hTarget
      cases hTarget
      let fullGas : EVMState :=
        { target with
          gasAvailable := full.gasAvailable,
          execLength := full.execLength }
      have hPopFull :
          fullGas.stack.pop3 = some (stack, first, second, third) := by
        simpa [fullGas] using hPop
      change
        (PrimStep.ternaryCopy f).run fullGas = .ok fullPost at hFull
      simp [PrimStep.run, EvmYul.EVM.ternaryCopyOp, hPopFull] at hFull
      cases hFull
      have hSharedRel :
          fullGas.toSharedState =
            { target.toSharedState with
              toMachineState :=
                { target.toSharedState.toMachineState with
                  gasAvailable :=
                    fullGas.toSharedState.toMachineState.gasAvailable } } := by
        simp [fullGas]
      have hShared' :=
        hShared (first := first) (second := second) (third := third)
          hSharedRel
      rw [hShared']
      simp [GasExecRel, fullGas, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]

theorem PrimStep_run_ternaryCopy_exists_gasExecRel_of_rel
    (f :
      EvmYul.SharedState .EVM → Word → Word → Word →
        EvmYul.SharedState .EVM)
    {full target targetPost : EVMState}
    (hShared :
      ∀ {fullShared targetShared : EvmYul.SharedState .EVM}
        {first second third : Word},
        fullShared =
          { targetShared with
            toMachineState :=
              { targetShared.toMachineState with
                gasAvailable := fullShared.toMachineState.gasAvailable } } →
        f fullShared first second third =
          { f targetShared first second third with
            toMachineState :=
              { (f targetShared first second third).toMachineState with
                gasAvailable :=
                  (f fullShared first second third).toMachineState.gasAvailable } })
    (hRel : GasExecRel full target)
    (hTarget : (PrimStep.ternaryCopy f).run target = .ok targetPost) :
    ∃ fullPost,
      (PrimStep.ternaryCopy f).run full = .ok fullPost ∧
        GasExecRel fullPost targetPost := by
  rw [hRel]
  cases hPop : target.stack.pop3 with
  | none =>
      simp [PrimStep.run, EvmYul.EVM.ternaryCopyOp, hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, first, second, third⟩
      simp [PrimStep.run, EvmYul.EVM.ternaryCopyOp, hPop] at hTarget
      cases hTarget
      let fullGas : EVMState :=
        { target with
          gasAvailable := full.gasAvailable,
          execLength := full.execLength }
      have hSharedRel :
          fullGas.toSharedState =
            { target.toSharedState with
              toMachineState :=
                { target.toSharedState.toMachineState with
                  gasAvailable :=
                    fullGas.toSharedState.toMachineState.gasAvailable } } := by
        simp [fullGas]
      have hShared' :=
        hShared (first := first) (second := second) (third := third)
          hSharedRel
      refine
        ⟨EvmYul.EVM.State.replaceStackAndIncrPC
            { fullGas with
              toSharedState :=
                f fullGas.toSharedState first second third }
            stack,
          ?_, ?_⟩
      · simp [PrimStep.run, EvmYul.EVM.ternaryCopyOp, hPop, fullGas]
        rfl
      · rw [hShared']
        simp [GasExecRel, fullGas, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC]

theorem PrimStep_run_quaternaryCopy_preserves_gasExecRel_of_rel
    (f :
      EvmYul.SharedState .EVM → Word → Word → Word → Word →
        EvmYul.SharedState .EVM)
    {full target fullPost targetPost : EVMState}
    (hShared :
      ∀ {fullShared targetShared : EvmYul.SharedState .EVM}
        {first second third fourth : Word},
        fullShared =
          { targetShared with
            toMachineState :=
              { targetShared.toMachineState with
                gasAvailable := fullShared.toMachineState.gasAvailable } } →
        f fullShared first second third fourth =
          { f targetShared first second third fourth with
            toMachineState :=
              { (f targetShared first second third fourth).toMachineState with
                gasAvailable :=
                  (f fullShared first second third fourth).toMachineState.gasAvailable } })
    (hRel : GasExecRel full target)
    (hTarget : (PrimStep.quaternaryCopy f).run target = .ok targetPost)
    (hFull : (PrimStep.quaternaryCopy f).run full = .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [hRel] at hFull
  cases hPop : target.stack.pop4 with
  | none =>
      simp [PrimStep.run, EvmYul.EVM.quaternaryCopyOp, hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, first, second, third, fourth⟩
      simp [PrimStep.run, EvmYul.EVM.quaternaryCopyOp, hPop] at hTarget
      cases hTarget
      let fullGas : EVMState :=
        { target with
          gasAvailable := full.gasAvailable,
          execLength := full.execLength }
      have hPopFull :
          fullGas.stack.pop4 = some (stack, first, second, third, fourth) := by
        simpa [fullGas] using hPop
      change
        (PrimStep.quaternaryCopy f).run fullGas = .ok fullPost at hFull
      simp [PrimStep.run, EvmYul.EVM.quaternaryCopyOp, hPopFull] at hFull
      cases hFull
      have hSharedRel :
          fullGas.toSharedState =
            { target.toSharedState with
              toMachineState :=
                { target.toSharedState.toMachineState with
                  gasAvailable :=
                    fullGas.toSharedState.toMachineState.gasAvailable } } := by
        simp [fullGas]
      have hShared' :=
        hShared (first := first) (second := second) (third := third)
          (fourth := fourth) hSharedRel
      rw [hShared']
      simp [GasExecRel, fullGas, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]

theorem PrimStep_run_quaternaryCopy_exists_gasExecRel_of_rel
    (f :
      EvmYul.SharedState .EVM → Word → Word → Word → Word →
        EvmYul.SharedState .EVM)
    {full target targetPost : EVMState}
    (hShared :
      ∀ {fullShared targetShared : EvmYul.SharedState .EVM}
        {first second third fourth : Word},
        fullShared =
          { targetShared with
            toMachineState :=
              { targetShared.toMachineState with
                gasAvailable := fullShared.toMachineState.gasAvailable } } →
        f fullShared first second third fourth =
          { f targetShared first second third fourth with
            toMachineState :=
              { (f targetShared first second third fourth).toMachineState with
                gasAvailable :=
                  (f fullShared first second third fourth).toMachineState.gasAvailable } })
    (hRel : GasExecRel full target)
    (hTarget : (PrimStep.quaternaryCopy f).run target = .ok targetPost) :
    ∃ fullPost,
      (PrimStep.quaternaryCopy f).run full = .ok fullPost ∧
        GasExecRel fullPost targetPost := by
  rw [hRel]
  cases hPop : target.stack.pop4 with
  | none =>
      simp [PrimStep.run, EvmYul.EVM.quaternaryCopyOp, hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, first, second, third, fourth⟩
      simp [PrimStep.run, EvmYul.EVM.quaternaryCopyOp, hPop] at hTarget
      cases hTarget
      let fullGas : EVMState :=
        { target with
          gasAvailable := full.gasAvailable,
          execLength := full.execLength }
      have hSharedRel :
          fullGas.toSharedState =
            { target.toSharedState with
              toMachineState :=
                { target.toSharedState.toMachineState with
                  gasAvailable :=
                    fullGas.toSharedState.toMachineState.gasAvailable } } := by
        simp [fullGas]
      have hShared' :=
        hShared (first := first) (second := second) (third := third)
          (fourth := fourth) hSharedRel
      refine
        ⟨EvmYul.EVM.State.replaceStackAndIncrPC
            { fullGas with
              toSharedState :=
                f fullGas.toSharedState first second third fourth }
            stack,
          ?_, ?_⟩
      · simp [PrimStep.run, EvmYul.EVM.quaternaryCopyOp, hPop, fullGas]
        rfl
      · rw [hShared']
        simp [GasExecRel, fullGas, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC]

theorem PrimStep_run_dup_preserves_gasExecRel
    (n : Nat)
    {full target fullPost targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : (PrimStep.dup n).run target = .ok targetPost)
    (hFull : (PrimStep.dup n).run full = .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [hRel] at hFull
  by_cases hLen : n ≤ target.stack.length
  · simp [PrimStep.run, EvmYul.dup, hLen] at hTarget hFull
    cases hTarget
    cases hFull
    simp [GasExecRel, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC]
  · simp [PrimStep.run, EvmYul.dup, hLen] at hTarget

theorem PrimStep_run_dup_exists_gasExecRel
    (n : Nat)
    {full target targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : (PrimStep.dup n).run target = .ok targetPost) :
    ∃ fullPost,
      (PrimStep.dup n).run full = .ok fullPost ∧
        GasExecRel fullPost targetPost := by
  rw [hRel]
  by_cases hLen : n ≤ target.stack.length
  · simp [PrimStep.run, EvmYul.dup, hLen] at hTarget
    cases hTarget
    let fullState : EVMState :=
      { target with
        gasAvailable := full.gasAvailable,
        execLength := full.execLength }
    refine
      ⟨EvmYul.EVM.State.replaceStackAndIncrPC fullState
          ((target.stack.take n).getLast! :: target.stack),
        ?_, ?_⟩
    · simp [PrimStep.run, EvmYul.dup, hLen, fullState]
    · simp [GasExecRel, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC, fullState]
  · simp [PrimStep.run, EvmYul.dup, hLen] at hTarget

theorem PrimStep_run_swap_preserves_gasExecRel
    (n : Nat)
    {full target fullPost targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : (PrimStep.swap n).run target = .ok targetPost)
    (hFull : (PrimStep.swap n).run full = .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [hRel] at hFull
  by_cases hLen : n + 1 ≤ target.stack.length
  · simp [PrimStep.run, EvmYul.swap, hLen] at hTarget hFull
    cases hTarget
    cases hFull
    simp [GasExecRel, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC]
  · simp [PrimStep.run, EvmYul.swap, hLen] at hTarget

theorem PrimStep_run_swap_exists_gasExecRel
    (n : Nat)
    {full target targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : (PrimStep.swap n).run target = .ok targetPost) :
    ∃ fullPost,
      (PrimStep.swap n).run full = .ok fullPost ∧
        GasExecRel fullPost targetPost := by
  rw [hRel]
  by_cases hLen : n + 1 ≤ target.stack.length
  · simp [PrimStep.run, EvmYul.swap, hLen] at hTarget
    cases hTarget
    let fullState : EVMState :=
      { target with
        gasAvailable := full.gasAvailable,
        execLength := full.execLength }
    let top := target.stack.take (n + 1)
    let bottom := target.stack.drop (n + 1)
    refine
      ⟨EvmYul.EVM.State.replaceStackAndIncrPC fullState
          (top.getLast! :: top.tail!.dropLast ++ [top.head!] ++ bottom),
        ?_, ?_⟩
    · simp [PrimStep.run, EvmYul.swap, hLen, fullState, top, bottom]
    · simp [GasExecRel, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC, fullState, top, bottom]
  · simp [PrimStep.run, EvmYul.swap, hLen] at hTarget

theorem PrimStep_run_invalid_preserves_gasExecRel
    {target fullPost targetPost : EVMState}
    (hTarget : PrimStep.invalid.run target = .ok targetPost) :
    GasExecRel fullPost targetPost := by
  simp [PrimStep.run] at hTarget

theorem machine_mload_gasAvailable_rel
    {fullMachine targetMachine : EvmYul.MachineState} {offset : Word}
    (hRel :
      fullMachine =
        { targetMachine with gasAvailable := fullMachine.gasAvailable }) :
    (fullMachine.mload offset).1 = (targetMachine.mload offset).1 ∧
      (fullMachine.mload offset).2 =
        { (targetMachine.mload offset).2 with
          gasAvailable := (fullMachine.mload offset).2.gasAvailable } := by
  rw [hRel]
  simp [EvmYul.MachineState.mload, EvmYul.MachineState.lookupMemory]

theorem machine_mstore_gasAvailable_rel
    {fullMachine targetMachine : EvmYul.MachineState}
    {offset value : Word}
    (hRel :
      fullMachine =
        { targetMachine with gasAvailable := fullMachine.gasAvailable }) :
    EvmYul.MachineState.mstore fullMachine offset value =
      { EvmYul.MachineState.mstore targetMachine offset value with
        gasAvailable :=
          (EvmYul.MachineState.mstore fullMachine offset value).gasAvailable } := by
  rw [hRel]
  simp [EvmYul.MachineState.mstore, EvmYul.MachineState.writeWord,
    EvmYul.writeBytes]

theorem machine_mstore8_gasAvailable_rel
    {fullMachine targetMachine : EvmYul.MachineState}
    {offset value : Word}
    (hRel :
      fullMachine =
        { targetMachine with gasAvailable := fullMachine.gasAvailable }) :
    EvmYul.MachineState.mstore8 fullMachine offset value =
      { EvmYul.MachineState.mstore8 targetMachine offset value with
        gasAvailable :=
          (EvmYul.MachineState.mstore8 fullMachine offset value).gasAvailable } := by
  rw [hRel]
  simp [EvmYul.MachineState.mstore8, EvmYul.writeBytes]

theorem machine_mcopy_gasAvailable_rel
    {fullMachine targetMachine : EvmYul.MachineState}
    {writeStart readStart size : Word}
    (hRel :
      fullMachine =
        { targetMachine with gasAvailable := fullMachine.gasAvailable }) :
    EvmYul.MachineState.mcopy fullMachine writeStart readStart size =
      { EvmYul.MachineState.mcopy targetMachine writeStart readStart size with
        gasAvailable :=
          (EvmYul.MachineState.mcopy fullMachine writeStart readStart size).gasAvailable } := by
  rw [hRel]
  simp [EvmYul.MachineState.mcopy, EvmYul.writeBytes]

theorem machine_keccak256_gasAvailable_rel
    {fullMachine targetMachine : EvmYul.MachineState}
    {offset size : Word}
    (hRel :
      fullMachine =
        { targetMachine with gasAvailable := fullMachine.gasAvailable }) :
    (EvmYul.MachineState.keccak256 fullMachine offset size).1 =
        (EvmYul.MachineState.keccak256 targetMachine offset size).1 ∧
      (EvmYul.MachineState.keccak256 fullMachine offset size).2 =
        { (EvmYul.MachineState.keccak256 targetMachine offset size).2 with
          gasAvailable :=
            (EvmYul.MachineState.keccak256 fullMachine offset size).2.gasAvailable } := by
  rw [hRel]
  simp [EvmYul.MachineState.keccak256]

theorem machine_returndatacopy_gasAvailable_rel
    {fullMachine targetMachine : EvmYul.MachineState}
    {mstart rstart size : Word}
    (hRel :
      fullMachine =
        { targetMachine with gasAvailable := fullMachine.gasAvailable }) :
    fullMachine.returndatacopy mstart rstart size =
      { targetMachine.returndatacopy mstart rstart size with
        gasAvailable :=
          (fullMachine.returndatacopy mstart rstart size).gasAvailable } := by
  rw [hRel]
  simp [EvmYul.MachineState.returndatacopy, EvmYul.writeBytes]

theorem machine_evmReturn_gasAvailable_rel
    {fullMachine targetMachine : EvmYul.MachineState}
    {mstart size : Word}
    (hRel :
      fullMachine =
        { targetMachine with gasAvailable := fullMachine.gasAvailable }) :
    EvmYul.MachineState.evmReturn fullMachine mstart size =
      { EvmYul.MachineState.evmReturn targetMachine mstart size with
        gasAvailable :=
          (EvmYul.MachineState.evmReturn fullMachine mstart size).gasAvailable } := by
  rw [hRel]
  simp [EvmYul.MachineState.evmReturn]

theorem machine_evmRevert_gasAvailable_rel
    {fullMachine targetMachine : EvmYul.MachineState}
    {mstart size : Word}
    (hRel :
      fullMachine =
        { targetMachine with gasAvailable := fullMachine.gasAvailable }) :
    EvmYul.MachineState.evmRevert fullMachine mstart size =
      { EvmYul.MachineState.evmRevert targetMachine mstart size with
        gasAvailable :=
          (EvmYul.MachineState.evmRevert fullMachine mstart size).gasAvailable } := by
  rw [hRel]
  simp [EvmYul.MachineState.evmRevert, EvmYul.MachineState.evmReturn]

theorem shared_calldatacopy_gasAvailable_rel
    {fullShared targetShared : EvmYul.SharedState .EVM}
    {mstart datastart size : Word}
    (hRel :
      fullShared =
        { targetShared with
          toMachineState :=
            { targetShared.toMachineState with
              gasAvailable := fullShared.toMachineState.gasAvailable } }) :
    EvmYul.SharedState.calldatacopy fullShared mstart datastart size =
      { EvmYul.SharedState.calldatacopy targetShared mstart datastart size with
        toMachineState :=
          { (EvmYul.SharedState.calldatacopy targetShared mstart datastart
              size).toMachineState with
            gasAvailable :=
              (EvmYul.SharedState.calldatacopy fullShared mstart datastart
                size).toMachineState.gasAvailable } } := by
  rw [hRel]
  simp [EvmYul.SharedState.calldatacopy]

theorem shared_codeCopy_gasAvailable_rel
    {fullShared targetShared : EvmYul.SharedState .EVM}
    {mstart cstart size : Word}
    (hRel :
      fullShared =
        { targetShared with
          toMachineState :=
            { targetShared.toMachineState with
              gasAvailable := fullShared.toMachineState.gasAvailable } }) :
    EvmYul.SharedState.codeCopy fullShared mstart cstart size =
      { EvmYul.SharedState.codeCopy targetShared mstart cstart size with
        toMachineState :=
          { (EvmYul.SharedState.codeCopy targetShared mstart cstart
              size).toMachineState with
            gasAvailable :=
              (EvmYul.SharedState.codeCopy fullShared mstart cstart
                size).toMachineState.gasAvailable } } := by
  rw [hRel]
  simp [EvmYul.SharedState.codeCopy]

theorem shared_extCodeCopy'_gasAvailable_rel
    {fullShared targetShared : EvmYul.SharedState .EVM}
    {account mstart cstart size : Word}
    (hRel :
      fullShared =
        { targetShared with
          toMachineState :=
            { targetShared.toMachineState with
              gasAvailable := fullShared.toMachineState.gasAvailable } }) :
    EvmYul.SharedState.extCodeCopy' fullShared account mstart cstart size =
      { EvmYul.SharedState.extCodeCopy' targetShared account mstart cstart
          size with
        toMachineState :=
          { (EvmYul.SharedState.extCodeCopy' targetShared account mstart
              cstart size).toMachineState with
            gasAvailable :=
              (EvmYul.SharedState.extCodeCopy' fullShared account mstart
                cstart size).toMachineState.gasAvailable } } := by
  rw [hRel]
  simp [EvmYul.SharedState.extCodeCopy']

theorem machine_mstore_gasAvailable_eq
    {machine : EvmYul.MachineState} {offset value : Word} :
    (EvmYul.MachineState.mstore machine offset value).gasAvailable =
      machine.gasAvailable := by
  simp [EvmYul.MachineState.mstore, EvmYul.MachineState.writeWord,
    EvmYul.writeBytes]

theorem machine_mstore8_gasAvailable_eq
    {machine : EvmYul.MachineState} {offset value : Word} :
    (EvmYul.MachineState.mstore8 machine offset value).gasAvailable =
      machine.gasAvailable := by
  simp [EvmYul.MachineState.mstore8, EvmYul.writeBytes]

theorem machine_mcopy_gasAvailable_eq
    {machine : EvmYul.MachineState} {writeStart readStart size : Word} :
    (EvmYul.MachineState.mcopy machine writeStart readStart size).gasAvailable =
      machine.gasAvailable := by
  simp [EvmYul.MachineState.mcopy, EvmYul.writeBytes]

theorem machine_keccak256_gasAvailable_eq
    {machine : EvmYul.MachineState} {offset size : Word} :
    (EvmYul.MachineState.keccak256 machine offset size).2.gasAvailable =
      machine.gasAvailable := by
  simp [EvmYul.MachineState.keccak256]

theorem shared_calldatacopy_gasAvailable_eq
    {shared : EvmYul.SharedState .EVM} {mstart datastart size : Word} :
    (EvmYul.SharedState.calldatacopy shared mstart datastart
      size).toMachineState.gasAvailable =
      shared.toMachineState.gasAvailable := by
  simp [EvmYul.SharedState.calldatacopy]

theorem shared_codeCopy_gasAvailable_eq
    {shared : EvmYul.SharedState .EVM} {mstart cstart size : Word} :
    (EvmYul.SharedState.codeCopy shared mstart cstart
      size).toMachineState.gasAvailable =
      shared.toMachineState.gasAvailable := by
  simp [EvmYul.SharedState.codeCopy]

theorem shared_extCodeCopy'_gasAvailable_eq
    {shared : EvmYul.SharedState .EVM}
    {account mstart cstart size : Word} :
    (EvmYul.SharedState.extCodeCopy' shared account mstart cstart
      size).toMachineState.gasAvailable =
      shared.toMachineState.gasAvailable := by
  simp [EvmYul.SharedState.extCodeCopy']

theorem PrimStep_run_bin_gasAvailable_eq
    (f : EvmYul.Primop.Binary) {state post : EVMState}
    (hRun : (PrimStep.bin f).run state = .ok post) :
    post.gasAvailable = state.gasAvailable := by
  simp [PrimStep.run, EvmYul.EVM.execBinOp] at hRun
  split at hRun <;> cases hRun <;> rfl

theorem PrimStep_run_un_gasAvailable_eq
    (f : EvmYul.Primop.Unary) {state post : EVMState}
    (hRun : (PrimStep.un f).run state = .ok post) :
    post.gasAvailable = state.gasAvailable := by
  simp [PrimStep.run, EvmYul.EVM.execUnOp] at hRun
  split at hRun <;> cases hRun <;> rfl

theorem PrimStep_run_tri_gasAvailable_eq
    (f : EvmYul.Primop.Ternary) {state post : EVMState}
    (hRun : (PrimStep.tri f).run state = .ok post) :
    post.gasAvailable = state.gasAvailable := by
  simp [PrimStep.run, EvmYul.EVM.execTriOp] at hRun
  split at hRun <;> cases hRun <;> rfl

theorem PrimStep_run_executionEnv_gasAvailable_eq
    (f : EvmYul.ExecutionEnv EvmYul.OperationType.EVM → Word)
    {state post : EVMState}
    (hRun : (PrimStep.executionEnv f).run state = .ok post) :
    post.gasAvailable = state.gasAvailable := by
  simp [PrimStep.run, EvmYul.EVM.executionEnvOp,
    EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC] at hRun
  cases hRun
  rfl

theorem PrimStep_run_unaryExecutionEnv_gasAvailable_eq
    (f : EvmYul.ExecutionEnv EvmYul.OperationType.EVM → Word → Word)
    {state post : EVMState}
    (hRun : (PrimStep.unaryExecutionEnv f).run state = .ok post) :
    post.gasAvailable = state.gasAvailable := by
  simp [PrimStep.run, EvmYul.EVM.unaryExecutionEnvOp] at hRun
  split at hRun <;> cases hRun <;> rfl

theorem PrimStep_run_machineState_gasAvailable_eq
    (f : EvmYul.MachineState → Word) {state post : EVMState}
    (hRun : (PrimStep.machineState f).run state = .ok post) :
    post.gasAvailable = state.gasAvailable := by
  simp [PrimStep.run, EvmYul.EVM.machineStateOp,
    EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC] at hRun
  cases hRun
  rfl

theorem PrimStep_run_binaryMachineState_gasAvailable_eq
    (f : EvmYul.MachineState → Word → Word → EvmYul.MachineState)
    (hGas :
      ∀ machine left right,
        (f machine left right).gasAvailable = machine.gasAvailable)
    {state post : EVMState}
    (hRun : (PrimStep.binaryMachineState f).run state = .ok post) :
    post.gasAvailable = state.gasAvailable := by
  simp [PrimStep.run, EvmYul.EVM.binaryMachineStateOp] at hRun
  split at hRun <;> cases hRun
  · simp [EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, hGas]

theorem PrimStep_run_binaryMachineStateWithResult_gasAvailable_eq
    (f : EvmYul.MachineState → Word → Word → Word × EvmYul.MachineState)
    (hGas :
      ∀ machine left right,
        (f machine left right).2.gasAvailable = machine.gasAvailable)
    {state post : EVMState}
    (hRun : (PrimStep.binaryMachineStateWithResult f).run state =
      .ok post) :
    post.gasAvailable = state.gasAvailable := by
  simp [PrimStep.run, EvmYul.EVM.binaryMachineStateOp'] at hRun
  split at hRun <;> cases hRun
  · simp [EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, hGas]

theorem PrimStep_run_ternaryMachineState_gasAvailable_eq
    (f : EvmYul.MachineState → Word → Word → Word → EvmYul.MachineState)
    (hGas :
      ∀ machine first second third,
        (f machine first second third).gasAvailable =
          machine.gasAvailable)
    {state post : EVMState}
    (hRun : (PrimStep.ternaryMachineState f).run state = .ok post) :
    post.gasAvailable = state.gasAvailable := by
  simp [PrimStep.run, EvmYul.EVM.ternaryMachineStateOp] at hRun
  split at hRun <;> cases hRun
  · simp [EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, hGas]

theorem PrimStep_run_state_gasAvailable_eq
    (f : EvmYul.State EvmYul.OperationType.EVM → Word)
    {state post : EVMState}
    (hRun : (PrimStep.state f).run state = .ok post) :
    post.gasAvailable = state.gasAvailable := by
  simp [PrimStep.run, EvmYul.EVM.stateOp,
    EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC] at hRun
  cases hRun
  rfl

theorem PrimStep_run_unaryState_gasAvailable_eq
    (f :
      EvmYul.State EvmYul.OperationType.EVM → Word →
        EvmYul.State EvmYul.OperationType.EVM × Word)
    {state post : EVMState}
    (hRun : (PrimStep.unaryState f).run state = .ok post) :
    post.gasAvailable = state.gasAvailable := by
  simp [PrimStep.run, EvmYul.EVM.unaryStateOp] at hRun
  split at hRun <;> cases hRun <;> rfl

theorem PrimStep_run_binaryState_gasAvailable_eq
    (f :
      EvmYul.State EvmYul.OperationType.EVM → Word → Word →
        EvmYul.State EvmYul.OperationType.EVM)
    {state post : EVMState}
    (hRun : (PrimStep.binaryState f).run state = .ok post) :
    post.gasAvailable = state.gasAvailable := by
  simp [PrimStep.run, EvmYul.EVM.binaryStateOp] at hRun
  split at hRun <;> cases hRun <;> rfl

theorem PrimStep_run_ternaryCopy_gasAvailable_eq
    (f :
      EvmYul.SharedState EvmYul.OperationType.EVM → Word → Word →
        Word → EvmYul.SharedState EvmYul.OperationType.EVM)
    (hGas :
      ∀ shared first second third,
        (f shared first second third).toMachineState.gasAvailable =
          shared.toMachineState.gasAvailable)
    {state post : EVMState}
    (hRun : (PrimStep.ternaryCopy f).run state = .ok post) :
    post.gasAvailable = state.gasAvailable := by
  simp [PrimStep.run, EvmYul.EVM.ternaryCopyOp] at hRun
  split at hRun <;> cases hRun
  · simp [EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, hGas]

theorem PrimStep_run_quaternaryCopy_gasAvailable_eq
    (f :
      EvmYul.SharedState EvmYul.OperationType.EVM → Word → Word →
        Word → Word → EvmYul.SharedState EvmYul.OperationType.EVM)
    (hGas :
      ∀ shared first second third fourth,
        (f shared first second third fourth).toMachineState.gasAvailable =
          shared.toMachineState.gasAvailable)
    {state post : EVMState}
    (hRun : (PrimStep.quaternaryCopy f).run state = .ok post) :
    post.gasAvailable = state.gasAvailable := by
  simp [PrimStep.run, EvmYul.EVM.quaternaryCopyOp] at hRun
  split at hRun <;> cases hRun
  · simp [EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, hGas]

theorem PrimStep_run_pop_gasAvailable_eq {state post : EVMState}
    (hRun : PrimStep.pop.run state = .ok post) :
    post.gasAvailable = state.gasAvailable := by
  simp [PrimStep.run] at hRun
  split at hRun <;> cases hRun <;> rfl

theorem PrimStep_run_mload_gasAvailable_eq {state post : EVMState}
    (hRun : PrimStep.mload.run state = .ok post) :
    post.gasAvailable = state.gasAvailable := by
  simp [PrimStep.run, EvmYul.MachineState.mload,
    EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC] at hRun
  split at hRun <;> cases hRun <;> rfl

theorem PrimStep_run_returndatacopy_gasAvailable_eq
    {state post : EVMState}
    (hRun : PrimStep.returndatacopy.run state = .ok post) :
    post.gasAvailable = state.gasAvailable := by
  simp [PrimStep.run, EvmYul.MachineState.returndatacopy,
    EvmYul.writeBytes, EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC] at hRun
  split at hRun <;> cases hRun <;> rfl

theorem PrimStep_run_dup_gasAvailable_eq (n : Nat)
    {state post : EVMState}
    (hRun : (PrimStep.dup n).run state = .ok post) :
    post.gasAvailable = state.gasAvailable := by
  simp [PrimStep.run, EvmYul.dup] at hRun
  split at hRun <;> cases hRun <;> rfl

theorem PrimStep_run_swap_gasAvailable_eq (n : Nat)
    {state post : EVMState}
    (hRun : (PrimStep.swap n).run state = .ok post) :
    post.gasAvailable = state.gasAvailable := by
  simp [PrimStep.run, EvmYul.swap] at hRun
  split at hRun <;> cases hRun <;> rfl

theorem PrimStep_run_log0_gasAvailable_eq {state post : EVMState}
    (hRun : PrimStep.log0.run state = .ok post) :
    post.gasAvailable = state.gasAvailable := by
  simp [PrimStep.run, EvmYul.SharedState.logOp,
    EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC] at hRun
  split at hRun <;> cases hRun <;> rfl

theorem PrimStep_run_log1_gasAvailable_eq {state post : EVMState}
    (hRun : PrimStep.log1.run state = .ok post) :
    post.gasAvailable = state.gasAvailable := by
  simp [PrimStep.run, EvmYul.SharedState.logOp,
    EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC] at hRun
  split at hRun <;> cases hRun <;> rfl

theorem PrimStep_run_log2_gasAvailable_eq {state post : EVMState}
    (hRun : PrimStep.log2.run state = .ok post) :
    post.gasAvailable = state.gasAvailable := by
  simp [PrimStep.run, EvmYul.SharedState.logOp,
    EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC] at hRun
  split at hRun <;> cases hRun <;> rfl

theorem PrimStep_run_log3_gasAvailable_eq {state post : EVMState}
    (hRun : PrimStep.log3.run state = .ok post) :
    post.gasAvailable = state.gasAvailable := by
  simp [PrimStep.run, EvmYul.SharedState.logOp,
    EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC] at hRun
  split at hRun <;> cases hRun <;> rfl

theorem PrimStep_run_log4_gasAvailable_eq {state post : EVMState}
    (hRun : PrimStep.log4.run state = .ok post) :
    post.gasAvailable = state.gasAvailable := by
  simp [PrimStep.run, EvmYul.SharedState.logOp,
    EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC] at hRun
  split at hRun <;> cases hRun <;> rfl

theorem PrimStep_run_invalid_gasAvailable_eq {state post : EVMState}
    (hRun : PrimStep.invalid.run state = .ok post) :
    post.gasAvailable = state.gasAvailable := by
  simp [PrimStep.run] at hRun

set_option maxHeartbeats 1200000 in
theorem PrimStep_run_of_continuing_prim_gasAvailable_eq
    {op : PrimOp} {step : PrimStep}
    (hStep : op.continuingStep? = some step)
    {state post : EVMState}
    (hRun : step.run state = .ok post) :
    post.gasAvailable = state.gasAvailable := by
  cases step with
  | bin f => exact PrimStep_run_bin_gasAvailable_eq f hRun
  | un f => exact PrimStep_run_un_gasAvailable_eq f hRun
  | tri f => exact PrimStep_run_tri_gasAvailable_eq f hRun
  | executionEnv f =>
      exact PrimStep_run_executionEnv_gasAvailable_eq f hRun
  | unaryExecutionEnv f =>
      exact PrimStep_run_unaryExecutionEnv_gasAvailable_eq f hRun
  | machineState f =>
      exact PrimStep_run_machineState_gasAvailable_eq f hRun
  | binaryMachineState f =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      · exact PrimStep_run_binaryMachineState_gasAvailable_eq
          EvmYul.MachineState.mstore
          (fun machine left right =>
            machine_mstore_gasAvailable_eq (machine := machine)
              (offset := left) (value := right)) hRun
      · exact PrimStep_run_binaryMachineState_gasAvailable_eq
          EvmYul.MachineState.mstore8
          (fun machine left right =>
            machine_mstore8_gasAvailable_eq (machine := machine)
              (offset := left) (value := right)) hRun
  | binaryMachineStateWithResult f =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      exact PrimStep_run_binaryMachineStateWithResult_gasAvailable_eq
        EvmYul.MachineState.keccak256
        (fun machine left right =>
          machine_keccak256_gasAvailable_eq (machine := machine)
            (offset := left) (size := right)) hRun
  | ternaryMachineState f =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      exact PrimStep_run_ternaryMachineState_gasAvailable_eq
        EvmYul.MachineState.mcopy
        (fun machine first second third =>
          machine_mcopy_gasAvailable_eq (machine := machine)
            (writeStart := first) (readStart := second) (size := third)) hRun
  | state f => exact PrimStep_run_state_gasAvailable_eq f hRun
  | unaryState f => exact PrimStep_run_unaryState_gasAvailable_eq f hRun
  | binaryState f => exact PrimStep_run_binaryState_gasAvailable_eq f hRun
  | ternaryCopy f =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      · exact PrimStep_run_ternaryCopy_gasAvailable_eq
          EvmYul.SharedState.calldatacopy
          (fun shared first second third =>
            shared_calldatacopy_gasAvailable_eq (shared := shared)
              (mstart := first) (datastart := second) (size := third))
          hRun
      · exact PrimStep_run_ternaryCopy_gasAvailable_eq
          EvmYul.SharedState.codeCopy
          (fun shared first second third =>
            shared_codeCopy_gasAvailable_eq (shared := shared)
              (mstart := first) (cstart := second) (size := third)) hRun
  | quaternaryCopy f =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      exact PrimStep_run_quaternaryCopy_gasAvailable_eq
        EvmYul.SharedState.extCodeCopy'
        (fun shared first second third fourth =>
          shared_extCodeCopy'_gasAvailable_eq (shared := shared)
            (account := first) (mstart := second) (cstart := third)
            (size := fourth)) hRun
  | pop => exact PrimStep_run_pop_gasAvailable_eq hRun
  | mload => exact PrimStep_run_mload_gasAvailable_eq hRun
  | returndatacopy =>
      exact PrimStep_run_returndatacopy_gasAvailable_eq hRun
  | dup n => exact PrimStep_run_dup_gasAvailable_eq n hRun
  | swap n => exact PrimStep_run_swap_gasAvailable_eq n hRun
  | log0 => exact PrimStep_run_log0_gasAvailable_eq hRun
  | log1 => exact PrimStep_run_log1_gasAvailable_eq hRun
  | log2 => exact PrimStep_run_log2_gasAvailable_eq hRun
  | log3 => exact PrimStep_run_log3_gasAvailable_eq hRun
  | log4 => exact PrimStep_run_log4_gasAvailable_eq hRun
  | invalid => exact PrimStep_run_invalid_gasAvailable_eq hRun

theorem EvmYul_step_continuing_prim_gasAvailable_eq
    {op : PrimOp} {step : PrimStep}
    (hStep : op.continuingStep? = some step)
    {state post : EVMState}
    (hRun : EvmYul.step op.toEVM none state = .ok post) :
    post.gasAvailable = state.gasAvailable := by
  have hRunStep : step.run state = .ok post := by
    rw [← EvmYul_step_eq_continuingStep_run_exact hStep state]
    exact hRun
  exact PrimStep_run_of_continuing_prim_gasAvailable_eq hStep hRunStep

theorem EvmYul_step_pop_preserves_gasExecRel
    {full target fullPost targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : PrimStep.pop.run target = .ok targetPost)
    (hFull :
      EvmYul.step (τ := .EVM) EvmYul.Operation.POP none full =
        .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [hRel] at hFull
  cases hPop : target.stack.pop with
  | none =>
      simp [PrimStep.run, hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, value⟩
      simp [PrimStep.run, hPop] at hTarget
      cases hTarget
      let fullGas : EVMState :=
        { target with
          gasAvailable := full.gasAvailable,
          execLength := full.execLength }
      change
        EvmYul.step (τ := .EVM) EvmYul.Operation.POP none fullGas =
          .ok fullPost at hFull
      have hStackTarget : target.stack = value :: stack :=
        stack_eq_cons_of_pop hPop
      have hStackFull : fullGas.stack = value :: stack := by
        simpa [fullGas] using hStackTarget
      have hStep :
          EvmYul.step (τ := .EVM) EvmYul.Operation.POP none fullGas =
            .ok (EvmYul.EVM.State.replaceStackAndIncrPC fullGas stack) := by
        dsimp [fullGas]
        rw [hStackTarget]
        rfl
      rw [hStep] at hFull
      cases hFull
      simp [GasExecRel, fullGas, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]

theorem EvmYul_step_mload_preserves_gasExecRel
    {full target fullPost targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : PrimStep.mload.run target = .ok targetPost)
    (hFull :
      EvmYul.step (τ := .EVM) EvmYul.Operation.MLOAD none full =
        .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [hRel] at hFull
  cases hPop : target.stack.pop with
  | none =>
      simp [PrimStep.run, hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, offset⟩
      simp [PrimStep.run, hPop] at hTarget
      cases hTarget
      let fullGas : EVMState :=
        { target with
          gasAvailable := full.gasAvailable,
          execLength := full.execLength }
      change
        EvmYul.step (τ := .EVM) EvmYul.Operation.MLOAD none fullGas =
          .ok fullPost at hFull
      have hStackTarget : target.stack = offset :: stack :=
        stack_eq_cons_of_pop hPop
      have hStep :
          EvmYul.step (τ := .EVM) EvmYul.Operation.MLOAD none fullGas =
            .ok
              (let loaded := fullGas.toMachineState.mload offset
               EvmYul.EVM.State.replaceStackAndIncrPC
                { fullGas with toMachineState := loaded.2 }
                (stack.push loaded.1)) := by
        dsimp [fullGas]
        rw [hStackTarget]
        rfl
      rw [hStep] at hFull
      cases hFull
      have hMachineRel :
          fullGas.toMachineState =
            { target.toMachineState with
              gasAvailable := fullGas.toMachineState.gasAvailable } := by
        simp [fullGas]
      have hMload :=
        machine_mload_gasAvailable_rel (offset := offset) hMachineRel
      rcases hMload with ⟨hMloadValue, hMloadState⟩
      dsimp
      rw [hMloadValue, hMloadState]
      simp [GasExecRel, fullGas, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]

theorem stack_eq_cons_cons_cons_of_pop3
    {stack rest : EvmYul.Stack Word} {first second third : Word}
    (hPop : EvmYul.Stack.pop3 stack = some (rest, first, second, third)) :
    stack = first :: second :: third :: rest := by
  cases stack with
  | nil =>
      simp [EvmYul.Stack.pop3] at hPop
  | cons hd tl =>
      cases tl with
      | nil =>
          simp [EvmYul.Stack.pop3] at hPop
      | cons hd₁ tl₁ =>
          cases tl₁ with
          | nil =>
              simp [EvmYul.Stack.pop3] at hPop
          | cons hd₂ tl₂ =>
              simp [EvmYul.Stack.pop3] at hPop
              rcases hPop with ⟨hRest, hFirst, hSecond, hThird⟩
              subst rest
              subst first
              subst second
              subst third
              rfl

theorem EvmYul_step_returndatacopy_preserves_gasExecRel
    {full target fullPost targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : PrimStep.returndatacopy.run target = .ok targetPost)
    (hFull :
      EvmYul.step (τ := .EVM) EvmYul.Operation.RETURNDATACOPY none full =
        .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [hRel] at hFull
  cases hPop : target.stack.pop3 with
  | none =>
      simp [PrimStep.run, hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, mstart, rstart, size⟩
      simp [PrimStep.run, hPop] at hTarget
      cases hTarget
      let fullGas : EVMState :=
        { target with
          gasAvailable := full.gasAvailable,
          execLength := full.execLength }
      change
        EvmYul.step (τ := .EVM) EvmYul.Operation.RETURNDATACOPY none
          fullGas = .ok fullPost at hFull
      have hStackTarget :
          target.stack = mstart :: rstart :: size :: stack :=
        stack_eq_cons_cons_cons_of_pop3 hPop
      have hStep :
          EvmYul.step (τ := .EVM) EvmYul.Operation.RETURNDATACOPY none
              fullGas =
            .ok
              (EvmYul.EVM.State.replaceStackAndIncrPC
                { fullGas with
                  toMachineState :=
                    fullGas.toMachineState.returndatacopy mstart rstart size }
                stack) := by
        dsimp [fullGas]
        rw [hStackTarget]
        rfl
      rw [hStep] at hFull
      cases hFull
      have hMachineRel :
          fullGas.toMachineState =
            { target.toMachineState with
              gasAvailable := fullGas.toMachineState.gasAvailable } := by
        simp [fullGas]
      have hCopy :=
        machine_returndatacopy_gasAvailable_rel
          (mstart := mstart) (rstart := rstart) (size := size) hMachineRel
      dsimp
      rw [hCopy]
      simp [GasExecRel, fullGas, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]

theorem EvmYul_step_log0_preserves_gasExecRel
    {full target fullPost targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : PrimStep.log0.run target = .ok targetPost)
    (hFull :
      EvmYul.step (τ := .EVM) EvmYul.Operation.LOG0 none full =
        .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [hRel] at hFull
  cases hPop : target.stack.pop2 with
  | none =>
      simp [PrimStep.run, hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, offset, size⟩
      simp [PrimStep.run, hPop] at hTarget
      cases hTarget
      let fullGas : EVMState :=
        { target with
          gasAvailable := full.gasAvailable,
          execLength := full.execLength }
      change
        EvmYul.step (τ := .EVM) EvmYul.Operation.LOG0 none fullGas =
          .ok fullPost at hFull
      have hStackTarget : target.stack = offset :: size :: stack :=
        stack_eq_cons_cons_of_pop2 hPop
      have hStep :
          EvmYul.step (τ := .EVM) EvmYul.Operation.LOG0 none fullGas =
            .ok
              (EvmYul.EVM.State.replaceStackAndIncrPC
                { fullGas with
                  toSharedState :=
                    EvmYul.SharedState.logOp offset size #[]
                      fullGas.toSharedState }
                stack) := by
        dsimp [fullGas]
        rw [hStackTarget]
        rfl
      rw [hStep] at hFull
      cases hFull
      simp [GasExecRel, fullGas, EvmYul.SharedState.logOp,
        EvmYul.EVM.State.replaceStackAndIncrPC, EvmYul.EVM.State.incrPC]

theorem stack_eq_cons_cons_cons_cons_of_pop4
    {stack rest : EvmYul.Stack Word}
    {first second third fourth : Word}
    (hPop :
      EvmYul.Stack.pop4 stack = some (rest, first, second, third, fourth)) :
    stack = first :: second :: third :: fourth :: rest := by
  cases stack with
  | nil =>
      simp [EvmYul.Stack.pop4] at hPop
  | cons hd tl =>
      cases tl with
      | nil =>
          simp [EvmYul.Stack.pop4] at hPop
      | cons hd₁ tl₁ =>
          cases tl₁ with
          | nil =>
              simp [EvmYul.Stack.pop4] at hPop
          | cons hd₂ tl₂ =>
              cases tl₂ with
              | nil =>
                  simp [EvmYul.Stack.pop4] at hPop
              | cons hd₃ tl₃ =>
                  simp [EvmYul.Stack.pop4] at hPop
                  rcases hPop with ⟨hRest, hFirst, hSecond, hThird, hFourth⟩
                  subst rest
                  subst first
                  subst second
                  subst third
                  subst fourth
                  rfl

theorem stack_eq_cons_cons_cons_cons_cons_of_pop5
    {stack rest : EvmYul.Stack Word}
    {first second third fourth fifth : Word}
    (hPop :
      EvmYul.Stack.pop5 stack =
        some (rest, first, second, third, fourth, fifth)) :
    stack = first :: second :: third :: fourth :: fifth :: rest := by
  cases stack with
  | nil =>
      simp [EvmYul.Stack.pop5] at hPop
  | cons hd tl =>
      cases tl with
      | nil =>
          simp [EvmYul.Stack.pop5] at hPop
      | cons hd₁ tl₁ =>
          cases tl₁ with
          | nil =>
              simp [EvmYul.Stack.pop5] at hPop
          | cons hd₂ tl₂ =>
              cases tl₂ with
              | nil =>
                  simp [EvmYul.Stack.pop5] at hPop
              | cons hd₃ tl₃ =>
                  cases tl₃ with
                  | nil =>
                      simp [EvmYul.Stack.pop5] at hPop
                  | cons hd₄ tl₄ =>
                      simp [EvmYul.Stack.pop5] at hPop
                      rcases hPop with
                        ⟨hRest, hFirst, hSecond, hThird, hFourth, hFifth⟩
                      subst rest
                      subst first
                      subst second
                      subst third
                      subst fourth
                      subst fifth
                      rfl

theorem stack_eq_cons_cons_cons_cons_cons_cons_of_pop6
    {stack rest : EvmYul.Stack Word}
    {first second third fourth fifth sixth : Word}
    (hPop :
      EvmYul.Stack.pop6 stack =
        some (rest, first, second, third, fourth, fifth, sixth)) :
    stack = first :: second :: third :: fourth :: fifth :: sixth :: rest := by
  cases stack with
  | nil =>
      simp [EvmYul.Stack.pop6] at hPop
  | cons hd tl =>
      cases tl with
      | nil =>
          simp [EvmYul.Stack.pop6] at hPop
      | cons hd₁ tl₁ =>
          cases tl₁ with
          | nil =>
              simp [EvmYul.Stack.pop6] at hPop
          | cons hd₂ tl₂ =>
              cases tl₂ with
              | nil =>
                  simp [EvmYul.Stack.pop6] at hPop
              | cons hd₃ tl₃ =>
                  cases tl₃ with
                  | nil =>
                      simp [EvmYul.Stack.pop6] at hPop
                  | cons hd₄ tl₄ =>
                      cases tl₄ with
                      | nil =>
                          simp [EvmYul.Stack.pop6] at hPop
                      | cons hd₅ tl₅ =>
                          simp [EvmYul.Stack.pop6] at hPop
                          rcases hPop with
                            ⟨hRest, hFirst, hSecond, hThird, hFourth,
                              hFifth, hSixth⟩
                          subst rest
                          subst first
                          subst second
                          subst third
                          subst fourth
                          subst fifth
                          subst sixth
                          rfl

theorem EvmYul_step_log1_preserves_gasExecRel
    {full target fullPost targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : PrimStep.log1.run target = .ok targetPost)
    (hFull :
      EvmYul.step (τ := .EVM) EvmYul.Operation.LOG1 none full =
        .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [hRel] at hFull
  cases hPop : target.stack.pop3 with
  | none =>
      simp [PrimStep.run, hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, offset, size, topic0⟩
      simp [PrimStep.run, hPop] at hTarget
      cases hTarget
      let fullGas : EVMState :=
        { target with
          gasAvailable := full.gasAvailable,
          execLength := full.execLength }
      change
        EvmYul.step (τ := .EVM) EvmYul.Operation.LOG1 none fullGas =
          .ok fullPost at hFull
      have hStackTarget : target.stack = offset :: size :: topic0 :: stack :=
        stack_eq_cons_cons_cons_of_pop3 hPop
      have hStep :
          EvmYul.step (τ := .EVM) EvmYul.Operation.LOG1 none fullGas =
            .ok
              (EvmYul.EVM.State.replaceStackAndIncrPC
                { fullGas with
                  toSharedState :=
                    EvmYul.SharedState.logOp offset size #[topic0]
                      fullGas.toSharedState }
                stack) := by
        dsimp [fullGas]
        rw [hStackTarget]
        rfl
      rw [hStep] at hFull
      cases hFull
      simp [GasExecRel, fullGas, EvmYul.SharedState.logOp,
        EvmYul.EVM.State.replaceStackAndIncrPC, EvmYul.EVM.State.incrPC]

theorem EvmYul_step_log2_preserves_gasExecRel
    {full target fullPost targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : PrimStep.log2.run target = .ok targetPost)
    (hFull :
      EvmYul.step (τ := .EVM) EvmYul.Operation.LOG2 none full =
        .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [hRel] at hFull
  cases hPop : target.stack.pop4 with
  | none =>
      simp [PrimStep.run, hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, offset, size, topic0, topic1⟩
      simp [PrimStep.run, hPop] at hTarget
      cases hTarget
      let fullGas : EVMState :=
        { target with
          gasAvailable := full.gasAvailable,
          execLength := full.execLength }
      change
        EvmYul.step (τ := .EVM) EvmYul.Operation.LOG2 none fullGas =
          .ok fullPost at hFull
      have hStackTarget :
          target.stack = offset :: size :: topic0 :: topic1 :: stack :=
        stack_eq_cons_cons_cons_cons_of_pop4 hPop
      have hStep :
          EvmYul.step (τ := .EVM) EvmYul.Operation.LOG2 none fullGas =
            .ok
              (EvmYul.EVM.State.replaceStackAndIncrPC
                { fullGas with
                  toSharedState :=
                    EvmYul.SharedState.logOp offset size #[topic0, topic1]
                      fullGas.toSharedState }
                stack) := by
        dsimp [fullGas]
        rw [hStackTarget]
        rfl
      rw [hStep] at hFull
      cases hFull
      simp [GasExecRel, fullGas, EvmYul.SharedState.logOp,
        EvmYul.EVM.State.replaceStackAndIncrPC, EvmYul.EVM.State.incrPC]

theorem EvmYul_step_log3_preserves_gasExecRel
    {full target fullPost targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : PrimStep.log3.run target = .ok targetPost)
    (hFull :
      EvmYul.step (τ := .EVM) EvmYul.Operation.LOG3 none full =
        .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [hRel] at hFull
  cases hPop : target.stack.pop5 with
  | none =>
      simp [PrimStep.run, hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, offset, size, topic0, topic1, topic2⟩
      simp [PrimStep.run, hPop] at hTarget
      cases hTarget
      let fullGas : EVMState :=
        { target with
          gasAvailable := full.gasAvailable,
          execLength := full.execLength }
      change
        EvmYul.step (τ := .EVM) EvmYul.Operation.LOG3 none fullGas =
          .ok fullPost at hFull
      have hStackTarget :
          target.stack =
            offset :: size :: topic0 :: topic1 :: topic2 :: stack :=
        stack_eq_cons_cons_cons_cons_cons_of_pop5 hPop
      have hStep :
          EvmYul.step (τ := .EVM) EvmYul.Operation.LOG3 none fullGas =
            .ok
              (EvmYul.EVM.State.replaceStackAndIncrPC
                { fullGas with
                  toSharedState :=
                    EvmYul.SharedState.logOp offset size
                      #[topic0, topic1, topic2] fullGas.toSharedState }
                stack) := by
        dsimp [fullGas]
        rw [hStackTarget]
        rfl
      rw [hStep] at hFull
      cases hFull
      simp [GasExecRel, fullGas, EvmYul.SharedState.logOp,
        EvmYul.EVM.State.replaceStackAndIncrPC, EvmYul.EVM.State.incrPC]

theorem EvmYul_step_log4_preserves_gasExecRel
    {full target fullPost targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : PrimStep.log4.run target = .ok targetPost)
    (hFull :
      EvmYul.step (τ := .EVM) EvmYul.Operation.LOG4 none full =
        .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [hRel] at hFull
  cases hPop : target.stack.pop6 with
  | none =>
      simp [PrimStep.run, hPop] at hTarget
  | some popped =>
      rcases popped with
        ⟨stack, offset, size, topic0, topic1, topic2, topic3⟩
      simp [PrimStep.run, hPop] at hTarget
      cases hTarget
      let fullGas : EVMState :=
        { target with
          gasAvailable := full.gasAvailable,
          execLength := full.execLength }
      change
        EvmYul.step (τ := .EVM) EvmYul.Operation.LOG4 none fullGas =
          .ok fullPost at hFull
      have hStackTarget :
          target.stack =
            offset :: size :: topic0 :: topic1 :: topic2 :: topic3 :: stack :=
        stack_eq_cons_cons_cons_cons_cons_cons_of_pop6 hPop
      have hStep :
          EvmYul.step (τ := .EVM) EvmYul.Operation.LOG4 none fullGas =
            .ok
              (EvmYul.EVM.State.replaceStackAndIncrPC
                { fullGas with
                  toSharedState :=
                    EvmYul.SharedState.logOp offset size
                      #[topic0, topic1, topic2, topic3]
                      fullGas.toSharedState }
                stack) := by
        dsimp [fullGas]
        rw [hStackTarget]
        rfl
      rw [hStep] at hFull
      cases hFull
      simp [GasExecRel, fullGas, EvmYul.SharedState.logOp,
        EvmYul.EVM.State.replaceStackAndIncrPC, EvmYul.EVM.State.incrPC]

theorem EvmYul_step_stop_preserves_gasExecRel
    {full target fullPost targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget :
      EvmYul.step (τ := .EVM) EvmYul.Operation.STOP none target =
        .ok targetPost)
    (hFull :
      EvmYul.step (τ := .EVM) EvmYul.Operation.STOP none full =
        .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [hRel] at hFull
  have hTargetStep :
      EvmYul.step (τ := .EVM) EvmYul.Operation.STOP none target =
        .ok
          { target with
            toMachineState :=
              (target.toMachineState.setReturnData ByteArray.empty).setHReturn
                ByteArray.empty } := by
    rfl
  rw [hTargetStep] at hTarget
  cases hTarget
  let fullGas : EVMState :=
    { target with
      gasAvailable := full.gasAvailable,
      execLength := full.execLength }
  change
    EvmYul.step (τ := .EVM) EvmYul.Operation.STOP none fullGas =
      .ok fullPost at hFull
  have hFullStep :
      EvmYul.step (τ := .EVM) EvmYul.Operation.STOP none fullGas =
        .ok
          { fullGas with
            toMachineState :=
              (fullGas.toMachineState.setReturnData ByteArray.empty).setHReturn
                ByteArray.empty } := by
    rfl
  rw [hFullStep] at hFull
  cases hFull
  simp [GasExecRel, fullGas, EvmYul.MachineState.setReturnData,
    EvmYul.MachineState.setHReturn]

theorem EvmYul_step_pc_preserves_gasExecRel
    {full target fullPost targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget :
      EvmYul.step (τ := .EVM) EvmYul.Operation.PC none target =
        .ok targetPost)
    (hFull :
      EvmYul.step (τ := .EVM) EvmYul.Operation.PC none full =
        .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [hRel] at hFull
  have hTargetStep :
      EvmYul.step (τ := .EVM) EvmYul.Operation.PC none target =
        .ok
          (EvmYul.EVM.State.replaceStackAndIncrPC target
            (target.stack.push target.pc)) := by
    rfl
  rw [hTargetStep] at hTarget
  cases hTarget
  let fullGas : EVMState :=
    { target with
      gasAvailable := full.gasAvailable,
      execLength := full.execLength }
  change
    EvmYul.step (τ := .EVM) EvmYul.Operation.PC none fullGas =
      .ok fullPost at hFull
  have hFullStep :
      EvmYul.step (τ := .EVM) EvmYul.Operation.PC none fullGas =
        .ok
          (EvmYul.EVM.State.replaceStackAndIncrPC fullGas
            (fullGas.stack.push fullGas.pc)) := by
    rfl
  rw [hFullStep] at hFull
  cases hFull
  simp [GasExecRel, fullGas, EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC]

theorem EvmYul_step_return_preserves_gasExecRel
    {full target fullPost targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget :
      EvmYul.step (τ := .EVM) EvmYul.Operation.RETURN none target =
        .ok targetPost)
    (hFull :
      EvmYul.step (τ := .EVM) EvmYul.Operation.RETURN none full =
        .ok fullPost) :
    GasExecRel fullPost targetPost := by
  change
    (PrimStep.binaryMachineState EvmYul.MachineState.evmReturn).run target =
      .ok targetPost at hTarget
  change
    (PrimStep.binaryMachineState EvmYul.MachineState.evmReturn).run full =
      .ok fullPost at hFull
  exact
    PrimStep_run_binaryMachineState_preserves_gasExecRel_of_rel
      EvmYul.MachineState.evmReturn
      (fun hMachine => machine_evmReturn_gasAvailable_rel hMachine)
      hRel hTarget hFull

theorem EvmYul_step_revert_preserves_gasExecRel
    {full target fullPost targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget :
      EvmYul.step (τ := .EVM) EvmYul.Operation.REVERT none target =
        .ok targetPost)
    (hFull :
      EvmYul.step (τ := .EVM) EvmYul.Operation.REVERT none full =
        .ok fullPost) :
    GasExecRel fullPost targetPost := by
  change
    (PrimStep.binaryMachineState EvmYul.MachineState.evmRevert).run target =
      .ok targetPost at hTarget
  change
    (PrimStep.binaryMachineState EvmYul.MachineState.evmRevert).run full =
      .ok fullPost at hFull
  exact
    PrimStep_run_binaryMachineState_preserves_gasExecRel_of_rel
      EvmYul.MachineState.evmRevert
      (fun hMachine => machine_evmRevert_gasAvailable_rel hMachine)
      hRel hTarget hFull

theorem EvmYul_step_selfdestruct_stackUnderflow_of_pop_none
    {state : EVMState}
    (hPop : state.stack.pop = none) :
    EvmYul.step (τ := .EVM) EvmYul.Operation.SELFDESTRUCT none state =
      .error EvmYul.EVM.ExecutionException.StackUnderflow := by
  cases state with
  | mk shared pc stack execLength =>
      cases stack with
      | nil =>
          rfl
      | cons hd tl =>
          simp [EvmYul.Stack.pop] at hPop

theorem EvmYul_step_selfdestruct_preserves_gasExecRel
    {full target fullPost targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget :
      EvmYul.step (τ := .EVM) EvmYul.Operation.SELFDESTRUCT none target =
        .ok targetPost)
    (hFull :
      EvmYul.step (τ := .EVM) EvmYul.Operation.SELFDESTRUCT none full =
        .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [hRel] at hFull
  cases hPop : target.stack.pop with
  | none =>
      rw [EvmYul_step_selfdestruct_stackUnderflow_of_pop_none hPop] at hTarget
      cases hTarget
  | some popped =>
      rcases popped with ⟨stack, recipient⟩
      let fullGas : EVMState :=
        { target with
          gasAvailable := full.gasAvailable,
          execLength := full.execLength }
      change
        EvmYul.step (τ := .EVM) EvmYul.Operation.SELFDESTRUCT none fullGas =
          .ok fullPost at hFull
      have hStackTarget : target.stack = recipient :: stack :=
        stack_eq_cons_of_pop hPop
      have hStackFull : fullGas.stack = recipient :: stack := by
        simpa [fullGas] using hStackTarget
      rw [EvmYul.EVM.step_selfdestruct_of_stack target recipient stack
        hStackTarget] at hTarget
      rw [EvmYul.EVM.step_selfdestruct_of_stack fullGas recipient stack
        hStackFull] at hFull
      cases hTarget
      cases hFull
      simp [GasExecRel, fullGas, EvmYul.EVM.selfdestructState,
        EvmYul.selfdestructAccountMap, EvmYul.MachineState.setHReturn,
        EvmYul.EVM.State.replaceStackAndIncrPC, EvmYul.EVM.State.incrPC]

set_option maxHeartbeats 800000 in
theorem EvmYul_step_noncontinuing_prim_gasAvailable_eq
    {op : PrimOp}
    (hStep : op.continuingStep? = none)
    (hNoCallCreate : op.isCallCreate = false)
    {state post : EVMState}
    (hRun : EvmYul.step op.toEVM none state = .ok post) :
    post.gasAvailable = state.gasAvailable := by
  cases op <;>
    simp [PrimOp.continuingStep?, PrimOp.isCallCreate] at hStep hNoCallCreate
  · change EvmYul.step (τ := .EVM) EvmYul.Operation.STOP none state =
      .ok post at hRun
    have hStop :
        EvmYul.step (τ := .EVM) EvmYul.Operation.STOP none state =
          .ok
            { state with
              toMachineState :=
                (state.toMachineState.setReturnData ByteArray.empty).setHReturn
                  ByteArray.empty } := by
      rfl
    rw [hStop] at hRun
    cases hRun
    simp [EvmYul.MachineState.setReturnData,
      EvmYul.MachineState.setHReturn]
  · change EvmYul.step (τ := .EVM) EvmYul.Operation.PC none state =
      .ok post at hRun
    have hPc :
        EvmYul.step (τ := .EVM) EvmYul.Operation.PC none state =
          .ok
            (EvmYul.EVM.State.replaceStackAndIncrPC state
              (state.stack.push state.pc)) := by
      rfl
    rw [hPc] at hRun
    cases hRun
    simp [EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC]
  · change
      (PrimStep.binaryMachineState EvmYul.MachineState.evmReturn).run
          state = .ok post at hRun
    exact PrimStep_run_binaryMachineState_gasAvailable_eq
      EvmYul.MachineState.evmReturn
      (fun machine mstart size => by
        simp [EvmYul.MachineState.evmReturn]) hRun
  · change
      (PrimStep.binaryMachineState EvmYul.MachineState.evmRevert).run
          state = .ok post at hRun
    exact PrimStep_run_binaryMachineState_gasAvailable_eq
      EvmYul.MachineState.evmRevert
      (fun machine mstart size => by
        simp [EvmYul.MachineState.evmRevert,
          EvmYul.MachineState.evmReturn]) hRun
  · change EvmYul.step (τ := .EVM) EvmYul.Operation.SELFDESTRUCT none
      state = .ok post at hRun
    cases hPop : state.stack.pop with
    | none =>
        rw [EvmYul_step_selfdestruct_stackUnderflow_of_pop_none hPop] at hRun
        cases hRun
    | some popped =>
        rcases popped with ⟨stack, recipient⟩
        have hStack : state.stack = recipient :: stack :=
          stack_eq_cons_of_pop hPop
        rw [EvmYul.EVM.step_selfdestruct_of_stack state recipient stack
          hStack] at hRun
        cases hRun
        simp [EvmYul.EVM.selfdestructState, EvmYul.selfdestructAccountMap,
          EvmYul.MachineState.setHReturn,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC]

set_option maxHeartbeats 800000 in
theorem EvmYul_step_continuing_prim_preserves_gasExecRel
    {op : PrimOp} {step : PrimStep}
    {full target fullPost targetPost : EVMState}
    (hStep : op.continuingStep? = some step)
    (hRel : GasExecRel full target)
    (hTarget : step.run target = .ok targetPost)
    (hFull : EvmYul.step op.toEVM none full = .ok fullPost) :
    GasExecRel fullPost targetPost := by
  cases step with
  | bin f =>
      have hFullRun : (PrimStep.bin f).run full = .ok fullPost := by
        rw [EvmYul_step_eq_continuingStep_run hStep
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)] at hFull
        exact hFull
      exact PrimStep_run_bin_preserves_gasExecRel f hRel hTarget hFullRun
  | un f =>
      have hFullRun : (PrimStep.un f).run full = .ok fullPost := by
        rw [EvmYul_step_eq_continuingStep_run hStep
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)] at hFull
        exact hFull
      exact PrimStep_run_un_preserves_gasExecRel f hRel hTarget hFullRun
  | tri f =>
      have hFullRun : (PrimStep.tri f).run full = .ok fullPost := by
        rw [EvmYul_step_eq_continuingStep_run hStep
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)] at hFull
        exact hFull
      exact PrimStep_run_tri_preserves_gasExecRel f hRel hTarget hFullRun
  | executionEnv f =>
      have hFullRun :
          (PrimStep.executionEnv f).run full = .ok fullPost := by
        rw [EvmYul_step_eq_continuingStep_run hStep
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)] at hFull
        exact hFull
      exact
        PrimStep_run_executionEnv_preserves_gasExecRel f hRel hTarget
          hFullRun
  | unaryExecutionEnv f =>
      have hFullRun :
          (PrimStep.unaryExecutionEnv f).run full = .ok fullPost := by
        rw [EvmYul_step_eq_continuingStep_run hStep
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)] at hFull
        exact hFull
      exact
        PrimStep_run_unaryExecutionEnv_preserves_gasExecRel f hRel hTarget
          hFullRun
  | machineState f =>
      have hFullRun :
          (PrimStep.machineState f).run full = .ok fullPost := by
        rw [EvmYul_step_eq_continuingStep_run hStep
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)] at hFull
        exact hFull
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      all_goals
        exact
          PrimStep_run_machineState_preserves_gasExecRel_of_eq _
            (by
              rw [hRel]
              simp [EvmYul.MachineState.returndatasize,
                EvmYul.MachineState.msize])
            hRel hTarget hFullRun
  | binaryMachineState f =>
      have hFullRun :
          (PrimStep.binaryMachineState f).run full = .ok fullPost := by
        rw [EvmYul_step_eq_continuingStep_run hStep
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)] at hFull
        exact hFull
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      · exact
          PrimStep_run_binaryMachineState_preserves_gasExecRel_of_rel
            EvmYul.MachineState.mstore
            (fun hMachine =>
              machine_mstore_gasAvailable_rel hMachine)
            hRel hTarget hFullRun
      · exact
          PrimStep_run_binaryMachineState_preserves_gasExecRel_of_rel
            EvmYul.MachineState.mstore8
            (fun hMachine =>
              machine_mstore8_gasAvailable_rel hMachine)
            hRel hTarget hFullRun
  | binaryMachineStateWithResult f =>
      have hFullRun :
          (PrimStep.binaryMachineStateWithResult f).run full =
            .ok fullPost := by
        rw [EvmYul_step_eq_continuingStep_run hStep
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)] at hFull
        exact hFull
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      exact
        PrimStep_run_binaryMachineStateWithResult_preserves_gasExecRel_of_rel
          EvmYul.MachineState.keccak256
          (fun hMachine =>
            machine_keccak256_gasAvailable_rel hMachine)
          hRel hTarget hFullRun
  | ternaryMachineState f =>
      have hFullRun :
          (PrimStep.ternaryMachineState f).run full = .ok fullPost := by
        rw [EvmYul_step_eq_continuingStep_run hStep
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)] at hFull
        exact hFull
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      exact
        PrimStep_run_ternaryMachineState_preserves_gasExecRel_of_rel
          EvmYul.MachineState.mcopy
          (fun hMachine =>
            machine_mcopy_gasAvailable_rel hMachine)
          hRel hTarget hFullRun
  | state f =>
      have hFullRun : (PrimStep.state f).run full = .ok fullPost := by
        rw [EvmYul_step_eq_continuingStep_run hStep
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)] at hFull
        exact hFull
      exact PrimStep_run_state_preserves_gasExecRel f hRel hTarget hFullRun
  | unaryState f =>
      have hFullRun :
          (PrimStep.unaryState f).run full = .ok fullPost := by
        rw [EvmYul_step_eq_continuingStep_run hStep
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)] at hFull
        exact hFull
      exact
        PrimStep_run_unaryState_preserves_gasExecRel f hRel hTarget
          hFullRun
  | binaryState f =>
      have hFullRun :
          (PrimStep.binaryState f).run full = .ok fullPost := by
        rw [EvmYul_step_eq_continuingStep_run hStep
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)] at hFull
        exact hFull
      exact
        PrimStep_run_binaryState_preserves_gasExecRel f hRel hTarget
          hFullRun
  | ternaryCopy f =>
      have hFullRun :
          (PrimStep.ternaryCopy f).run full = .ok fullPost := by
        rw [EvmYul_step_eq_continuingStep_run hStep
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)] at hFull
        exact hFull
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      · exact
          PrimStep_run_ternaryCopy_preserves_gasExecRel_of_rel
            EvmYul.SharedState.calldatacopy
            (fun hShared =>
              shared_calldatacopy_gasAvailable_rel hShared)
            hRel hTarget hFullRun
      · exact
          PrimStep_run_ternaryCopy_preserves_gasExecRel_of_rel
            EvmYul.SharedState.codeCopy
            (fun hShared =>
              shared_codeCopy_gasAvailable_rel hShared)
            hRel hTarget hFullRun
  | quaternaryCopy f =>
      have hFullRun :
          (PrimStep.quaternaryCopy f).run full = .ok fullPost := by
        rw [EvmYul_step_eq_continuingStep_run hStep
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)] at hFull
        exact hFull
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      exact
        PrimStep_run_quaternaryCopy_preserves_gasExecRel_of_rel
          EvmYul.SharedState.extCodeCopy'
          (fun hShared =>
            shared_extCodeCopy'_gasAvailable_rel hShared)
          hRel hTarget hFullRun
  | pop =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      exact EvmYul_step_pop_preserves_gasExecRel hRel hTarget hFull
  | mload =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      exact EvmYul_step_mload_preserves_gasExecRel hRel hTarget hFull
  | returndatacopy =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      exact EvmYul_step_returndatacopy_preserves_gasExecRel hRel hTarget hFull
  | dup n =>
      have hFullRun : (PrimStep.dup n).run full = .ok fullPost := by
        rw [EvmYul_step_eq_continuingStep_run hStep
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)] at hFull
        exact hFull
      exact PrimStep_run_dup_preserves_gasExecRel n hRel hTarget hFullRun
  | swap n =>
      have hFullRun : (PrimStep.swap n).run full = .ok fullPost := by
        rw [EvmYul_step_eq_continuingStep_run hStep
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)] at hFull
        exact hFull
      exact PrimStep_run_swap_preserves_gasExecRel n hRel hTarget hFullRun
  | log0 =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      exact EvmYul_step_log0_preserves_gasExecRel hRel hTarget hFull
  | log1 =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      exact EvmYul_step_log1_preserves_gasExecRel hRel hTarget hFull
  | log2 =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      exact EvmYul_step_log2_preserves_gasExecRel hRel hTarget hFull
  | log3 =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      exact EvmYul_step_log3_preserves_gasExecRel hRel hTarget hFull
  | log4 =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      exact EvmYul_step_log4_preserves_gasExecRel hRel hTarget hFull
  | invalid =>
      exact PrimStep_run_invalid_preserves_gasExecRel hTarget

theorem EvmYul_step_noncontinuing_prim_preserves_gasExecRel
    {op : PrimOp}
    {full target fullPost targetPost : EVMState}
    (hStep : op.continuingStep? = none)
    (hNoCallCreate : op.isCallCreate = false)
    (hRel : GasExecRel full target)
    (hTarget : op.step target = .ok targetPost)
    (hFull : EvmYul.step op.toEVM none full = .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [PrimOp.step_eq_evm_step_of_not_continuing hStep] at hTarget
  cases op <;>
    simp [PrimOp.continuingStep?, PrimOp.isCallCreate] at hStep hNoCallCreate
  · exact EvmYul_step_stop_preserves_gasExecRel hRel hTarget hFull
  · exact EvmYul_step_pc_preserves_gasExecRel hRel hTarget hFull
  · exact EvmYul_step_return_preserves_gasExecRel hRel hTarget hFull
  · exact EvmYul_step_revert_preserves_gasExecRel hRel hTarget hFull
  · exact EvmYul_step_selfdestruct_preserves_gasExecRel hRel hTarget hFull

set_option maxHeartbeats 1200000 in
theorem EvmYul_step_continuing_prim_exists_gasExecRel
    {op : PrimOp} {step : PrimStep}
    {full target targetPost : EVMState}
    (hStep : op.continuingStep? = some step)
    (hRel : GasExecRel full target)
    (hTarget : step.run target = .ok targetPost) :
    ∃ fullPost,
      EvmYul.step op.toEVM none full = .ok fullPost ∧
        GasExecRel fullPost targetPost := by
  cases step with
  | bin f =>
      obtain ⟨fullPost, hRun, hRelPost⟩ :=
        PrimStep_run_bin_exists_gasExecRel f hRel hTarget
      refine ⟨fullPost, ?_, hRelPost⟩
      simpa [EvmYul_step_eq_continuingStep_run hStep
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)] using hRun
  | un f =>
      obtain ⟨fullPost, hRun, hRelPost⟩ :=
        PrimStep_run_un_exists_gasExecRel f hRel hTarget
      refine ⟨fullPost, ?_, hRelPost⟩
      simpa [EvmYul_step_eq_continuingStep_run hStep
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)] using hRun
  | tri f =>
      obtain ⟨fullPost, hRun, hRelPost⟩ :=
        PrimStep_run_tri_exists_gasExecRel f hRel hTarget
      refine ⟨fullPost, ?_, hRelPost⟩
      simpa [EvmYul_step_eq_continuingStep_run hStep
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)] using hRun
  | executionEnv f =>
      obtain ⟨fullPost, hRun, hRelPost⟩ :=
        PrimStep_run_executionEnv_exists_gasExecRel f hRel hTarget
      refine ⟨fullPost, ?_, hRelPost⟩
      simpa [EvmYul_step_eq_continuingStep_run hStep
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)] using hRun
  | unaryExecutionEnv f =>
      obtain ⟨fullPost, hRun, hRelPost⟩ :=
        PrimStep_run_unaryExecutionEnv_exists_gasExecRel f hRel hTarget
      refine ⟨fullPost, ?_, hRelPost⟩
      simpa [EvmYul_step_eq_continuingStep_run hStep
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)] using hRun
  | machineState f =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      all_goals
        obtain ⟨fullPost, hRun, hRelPost⟩ :=
          PrimStep_run_machineState_exists_gasExecRel_of_eq _
            (by
              rw [hRel]
              simp [EvmYul.MachineState.returndatasize,
                EvmYul.MachineState.msize])
            hRel hTarget
        refine ⟨fullPost, ?_, hRelPost⟩
        simpa [PrimOp.toEVM, PrimStep.run] using hRun
  | binaryMachineState f =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      · obtain ⟨fullPost, hRun, hRelPost⟩ :=
          PrimStep_run_binaryMachineState_exists_gasExecRel_of_rel
            EvmYul.MachineState.mstore
            (fun hMachine => machine_mstore_gasAvailable_rel hMachine)
            hRel hTarget
        refine ⟨fullPost, ?_, hRelPost⟩
        simpa [PrimOp.toEVM, PrimStep.run] using hRun
      · obtain ⟨fullPost, hRun, hRelPost⟩ :=
          PrimStep_run_binaryMachineState_exists_gasExecRel_of_rel
            EvmYul.MachineState.mstore8
            (fun hMachine => machine_mstore8_gasAvailable_rel hMachine)
            hRel hTarget
        refine ⟨fullPost, ?_, hRelPost⟩
        simpa [PrimOp.toEVM, PrimStep.run] using hRun
  | binaryMachineStateWithResult f =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      obtain ⟨fullPost, hRun, hRelPost⟩ :=
        PrimStep_run_binaryMachineStateWithResult_exists_gasExecRel_of_rel
          EvmYul.MachineState.keccak256
          (fun hMachine => machine_keccak256_gasAvailable_rel hMachine)
          hRel hTarget
      refine ⟨fullPost, ?_, hRelPost⟩
      simpa [PrimOp.toEVM, PrimStep.run] using hRun
  | ternaryMachineState f =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      obtain ⟨fullPost, hRun, hRelPost⟩ :=
        PrimStep_run_ternaryMachineState_exists_gasExecRel_of_rel
          EvmYul.MachineState.mcopy
          (fun hMachine => machine_mcopy_gasAvailable_rel hMachine)
          hRel hTarget
      refine ⟨fullPost, ?_, hRelPost⟩
      simpa [PrimOp.toEVM, PrimStep.run] using hRun
  | state f =>
      obtain ⟨fullPost, hRun, hRelPost⟩ :=
        PrimStep_run_state_exists_gasExecRel f hRel hTarget
      refine ⟨fullPost, ?_, hRelPost⟩
      simpa [EvmYul_step_eq_continuingStep_run hStep
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)] using hRun
  | unaryState f =>
      obtain ⟨fullPost, hRun, hRelPost⟩ :=
        PrimStep_run_unaryState_exists_gasExecRel f hRel hTarget
      refine ⟨fullPost, ?_, hRelPost⟩
      simpa [EvmYul_step_eq_continuingStep_run hStep
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)] using hRun
  | binaryState f =>
      obtain ⟨fullPost, hRun, hRelPost⟩ :=
        PrimStep_run_binaryState_exists_gasExecRel f hRel hTarget
      refine ⟨fullPost, ?_, hRelPost⟩
      simpa [EvmYul_step_eq_continuingStep_run hStep
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)] using hRun
  | ternaryCopy f =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      · obtain ⟨fullPost, hRun, hRelPost⟩ :=
          PrimStep_run_ternaryCopy_exists_gasExecRel_of_rel
            EvmYul.SharedState.calldatacopy
            (fun hShared => shared_calldatacopy_gasAvailable_rel hShared)
            hRel hTarget
        refine ⟨fullPost, ?_, hRelPost⟩
        simpa [PrimOp.toEVM, PrimStep.run] using hRun
      · obtain ⟨fullPost, hRun, hRelPost⟩ :=
          PrimStep_run_ternaryCopy_exists_gasExecRel_of_rel
            EvmYul.SharedState.codeCopy
            (fun hShared => shared_codeCopy_gasAvailable_rel hShared)
            hRel hTarget
        refine ⟨fullPost, ?_, hRelPost⟩
        simpa [PrimOp.toEVM, PrimStep.run] using hRun
  | quaternaryCopy f =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      obtain ⟨fullPost, hRun, hRelPost⟩ :=
        PrimStep_run_quaternaryCopy_exists_gasExecRel_of_rel
          EvmYul.SharedState.extCodeCopy'
          (fun hShared => shared_extCodeCopy'_gasAvailable_rel hShared)
          hRel hTarget
      refine ⟨fullPost, ?_, hRelPost⟩
      simpa [PrimOp.toEVM, PrimStep.run] using hRun
  | pop =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      rw [hRel]
      cases hPop : target.stack.pop with
      | none =>
          simp [PrimStep.run, hPop] at hTarget
      | some popped =>
          rcases popped with ⟨stack, value⟩
          simp [PrimStep.run, hPop] at hTarget
          cases hTarget
          have hStackTarget : target.stack = value :: stack :=
            stack_eq_cons_of_pop hPop
          let fullGas : EVMState :=
            { target with
              gasAvailable := full.gasAvailable,
              execLength := full.execLength }
          refine
            ⟨EvmYul.EVM.State.replaceStackAndIncrPC fullGas stack,
              ?_, ?_⟩
          · dsimp [fullGas]
            rw [hStackTarget]
            rfl
          · simp [GasExecRel, fullGas, EvmYul.EVM.State.replaceStackAndIncrPC,
              EvmYul.EVM.State.incrPC]
  | mload =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      rw [hRel]
      cases hPop : target.stack.pop with
      | none =>
          simp [PrimStep.run, hPop] at hTarget
      | some popped =>
          rcases popped with ⟨stack, offset⟩
          simp [PrimStep.run, hPop] at hTarget
          cases hTarget
          have hStackTarget : target.stack = offset :: stack :=
            stack_eq_cons_of_pop hPop
          let fullGas : EVMState :=
            { target with
              gasAvailable := full.gasAvailable,
              execLength := full.execLength }
          refine
            ⟨(let loaded := fullGas.toMachineState.mload offset;
               EvmYul.EVM.State.replaceStackAndIncrPC
                { fullGas with toMachineState := loaded.2 }
                (stack.push loaded.1)),
              ?_, ?_⟩
          · dsimp [fullGas]
            rw [hStackTarget]
            rfl
          · have hMachineRel :
                fullGas.toMachineState =
                  { target.toMachineState with
                    gasAvailable := fullGas.toMachineState.gasAvailable } := by
              simp [fullGas]
            have hMload :=
              machine_mload_gasAvailable_rel (offset := offset) hMachineRel
            rcases hMload with ⟨hMloadValue, hMloadState⟩
            dsimp
            rw [hMloadValue, hMloadState]
            simp [GasExecRel, fullGas, EvmYul.EVM.State.replaceStackAndIncrPC,
              EvmYul.EVM.State.incrPC]
  | returndatacopy =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      rw [hRel]
      cases hPop : target.stack.pop3 with
      | none =>
          simp [PrimStep.run, hPop] at hTarget
      | some popped =>
          rcases popped with ⟨stack, mstart, rstart, size⟩
          simp [PrimStep.run, hPop] at hTarget
          cases hTarget
          have hStackTarget :
              target.stack = mstart :: rstart :: size :: stack :=
            stack_eq_cons_cons_cons_of_pop3 hPop
          let fullGas : EVMState :=
            { target with
              gasAvailable := full.gasAvailable,
              execLength := full.execLength }
          refine
            ⟨EvmYul.EVM.State.replaceStackAndIncrPC
                { fullGas with
                  toMachineState :=
                    fullGas.toMachineState.returndatacopy mstart rstart size }
                stack,
              ?_, ?_⟩
          · dsimp [fullGas]
            rw [hStackTarget]
            rfl
          · have hMachineRel :
                fullGas.toMachineState =
                  { target.toMachineState with
                    gasAvailable := fullGas.toMachineState.gasAvailable } := by
              simp [fullGas]
            have hCopy :=
              machine_returndatacopy_gasAvailable_rel
                (mstart := mstart) (rstart := rstart) (size := size)
                hMachineRel
            dsimp
            rw [hCopy]
            simp [GasExecRel, fullGas, EvmYul.EVM.State.replaceStackAndIncrPC,
              EvmYul.EVM.State.incrPC]
  | dup n =>
      obtain ⟨fullPost, hRun, hRelPost⟩ :=
        PrimStep_run_dup_exists_gasExecRel n hRel hTarget
      refine ⟨fullPost, ?_, hRelPost⟩
      simpa [EvmYul_step_eq_continuingStep_run hStep
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)] using hRun
  | swap n =>
      obtain ⟨fullPost, hRun, hRelPost⟩ :=
        PrimStep_run_swap_exists_gasExecRel n hRel hTarget
      refine ⟨fullPost, ?_, hRelPost⟩
      simpa [EvmYul_step_eq_continuingStep_run hStep
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)] using hRun
  | log0 =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      rw [hRel]
      cases hPop : target.stack.pop2 with
      | none =>
          simp [PrimStep.run, hPop] at hTarget
      | some popped =>
          rcases popped with ⟨stack, offset, size⟩
          simp [PrimStep.run, hPop] at hTarget
          cases hTarget
          have hStackTarget : target.stack = offset :: size :: stack :=
            stack_eq_cons_cons_of_pop2 hPop
          let fullGas : EVMState :=
            { target with
              gasAvailable := full.gasAvailable,
              execLength := full.execLength }
          refine
            ⟨EvmYul.EVM.State.replaceStackAndIncrPC
                { fullGas with
                  toSharedState :=
                    EvmYul.SharedState.logOp offset size #[]
                      fullGas.toSharedState }
                stack,
              ?_, ?_⟩
          · dsimp [fullGas]
            rw [hStackTarget]
            rfl
          · simp [GasExecRel, fullGas, EvmYul.SharedState.logOp,
              EvmYul.EVM.State.replaceStackAndIncrPC,
              EvmYul.EVM.State.incrPC]
  | log1 =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      rw [hRel]
      cases hPop : target.stack.pop3 with
      | none =>
          simp [PrimStep.run, hPop] at hTarget
      | some popped =>
          rcases popped with ⟨stack, offset, size, topic0⟩
          simp [PrimStep.run, hPop] at hTarget
          cases hTarget
          have hStackTarget : target.stack = offset :: size :: topic0 :: stack :=
            stack_eq_cons_cons_cons_of_pop3 hPop
          let fullGas : EVMState :=
            { target with
              gasAvailable := full.gasAvailable,
              execLength := full.execLength }
          refine
            ⟨EvmYul.EVM.State.replaceStackAndIncrPC
                { fullGas with
                  toSharedState :=
                    EvmYul.SharedState.logOp offset size #[topic0]
                      fullGas.toSharedState }
                stack,
              ?_, ?_⟩
          · dsimp [fullGas]
            rw [hStackTarget]
            rfl
          · simp [GasExecRel, fullGas, EvmYul.SharedState.logOp,
              EvmYul.EVM.State.replaceStackAndIncrPC,
              EvmYul.EVM.State.incrPC]
  | log2 =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      rw [hRel]
      cases hPop : target.stack.pop4 with
      | none =>
          simp [PrimStep.run, hPop] at hTarget
      | some popped =>
          rcases popped with ⟨stack, offset, size, topic0, topic1⟩
          simp [PrimStep.run, hPop] at hTarget
          cases hTarget
          have hStackTarget :
              target.stack = offset :: size :: topic0 :: topic1 :: stack :=
            stack_eq_cons_cons_cons_cons_of_pop4 hPop
          let fullGas : EVMState :=
            { target with
              gasAvailable := full.gasAvailable,
              execLength := full.execLength }
          refine
            ⟨EvmYul.EVM.State.replaceStackAndIncrPC
                { fullGas with
                  toSharedState :=
                    EvmYul.SharedState.logOp offset size #[topic0, topic1]
                      fullGas.toSharedState }
                stack,
              ?_, ?_⟩
          · dsimp [fullGas]
            rw [hStackTarget]
            rfl
          · simp [GasExecRel, fullGas, EvmYul.SharedState.logOp,
              EvmYul.EVM.State.replaceStackAndIncrPC,
              EvmYul.EVM.State.incrPC]
  | log3 =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      rw [hRel]
      cases hPop : target.stack.pop5 with
      | none =>
          simp [PrimStep.run, hPop] at hTarget
      | some popped =>
          rcases popped with ⟨stack, offset, size, topic0, topic1, topic2⟩
          simp [PrimStep.run, hPop] at hTarget
          cases hTarget
          have hStackTarget :
              target.stack =
                offset :: size :: topic0 :: topic1 :: topic2 :: stack :=
            stack_eq_cons_cons_cons_cons_cons_of_pop5 hPop
          let fullGas : EVMState :=
            { target with
              gasAvailable := full.gasAvailable,
              execLength := full.execLength }
          refine
            ⟨EvmYul.EVM.State.replaceStackAndIncrPC
                { fullGas with
                  toSharedState :=
                    EvmYul.SharedState.logOp offset size
                      #[topic0, topic1, topic2] fullGas.toSharedState }
                stack,
              ?_, ?_⟩
          · dsimp [fullGas]
            rw [hStackTarget]
            rfl
          · simp [GasExecRel, fullGas, EvmYul.SharedState.logOp,
              EvmYul.EVM.State.replaceStackAndIncrPC,
              EvmYul.EVM.State.incrPC]
  | log4 =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      rw [hRel]
      cases hPop : target.stack.pop6 with
      | none =>
          simp [PrimStep.run, hPop] at hTarget
      | some popped =>
          rcases popped with
            ⟨stack, offset, size, topic0, topic1, topic2, topic3⟩
          simp [PrimStep.run, hPop] at hTarget
          cases hTarget
          have hStackTarget :
              target.stack =
                offset :: size :: topic0 :: topic1 :: topic2 :: topic3 ::
                  stack :=
            stack_eq_cons_cons_cons_cons_cons_cons_of_pop6 hPop
          let fullGas : EVMState :=
            { target with
              gasAvailable := full.gasAvailable,
              execLength := full.execLength }
          refine
            ⟨EvmYul.EVM.State.replaceStackAndIncrPC
                { fullGas with
                  toSharedState :=
                    EvmYul.SharedState.logOp offset size
                      #[topic0, topic1, topic2, topic3]
                      fullGas.toSharedState }
                stack,
              ?_, ?_⟩
          · dsimp [fullGas]
            rw [hStackTarget]
            rfl
          · simp [GasExecRel, fullGas, EvmYul.SharedState.logOp,
              EvmYul.EVM.State.replaceStackAndIncrPC,
              EvmYul.EVM.State.incrPC]
  | invalid =>
      simp [PrimStep.run] at hTarget

theorem EvmYul_step_noncontinuing_prim_exists_gasExecRel
    {op : PrimOp}
    {full target targetPost : EVMState}
    (hStep : op.continuingStep? = none)
    (hNoCallCreate : op.isCallCreate = false)
    (hRel : GasExecRel full target)
    (hTarget : op.step target = .ok targetPost) :
    ∃ fullPost,
      EvmYul.step op.toEVM none full = .ok fullPost ∧
        GasExecRel fullPost targetPost := by
  rw [PrimOp.step_eq_evm_step_of_not_continuing hStep] at hTarget
  cases op <;>
    simp [PrimOp.continuingStep?, PrimOp.isCallCreate] at hStep hNoCallCreate
  · rw [hRel]
    cases hTarget
    let fullGas : EVMState :=
      { target with
        gasAvailable := full.gasAvailable,
        execLength := full.execLength }
    refine
      ⟨{ fullGas with
          toMachineState :=
            (fullGas.toMachineState.setReturnData ByteArray.empty).setHReturn
              ByteArray.empty },
        ?_, ?_⟩
    · rfl
    · simp [GasExecRel, fullGas, EvmYul.MachineState.setReturnData,
        EvmYul.MachineState.setHReturn]
  · rw [hRel]
    cases hTarget
    let fullGas : EVMState :=
      { target with
        gasAvailable := full.gasAvailable,
        execLength := full.execLength }
    refine
      ⟨EvmYul.EVM.State.replaceStackAndIncrPC fullGas
          (fullGas.stack.push fullGas.pc),
        ?_, ?_⟩
    · rfl
    · simp [GasExecRel, fullGas, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]
  · change
      (PrimStep.binaryMachineState EvmYul.MachineState.evmReturn).run target =
        .ok targetPost at hTarget
    exact
      PrimStep_run_binaryMachineState_exists_gasExecRel_of_rel
        EvmYul.MachineState.evmReturn
        (fun hMachine => machine_evmReturn_gasAvailable_rel hMachine)
        hRel hTarget
  · change
      (PrimStep.binaryMachineState EvmYul.MachineState.evmRevert).run target =
        .ok targetPost at hTarget
    exact
      PrimStep_run_binaryMachineState_exists_gasExecRel_of_rel
        EvmYul.MachineState.evmRevert
        (fun hMachine => machine_evmRevert_gasAvailable_rel hMachine)
        hRel hTarget
  · rw [hRel]
    change
      EvmYul.step (τ := .EVM) EvmYul.Operation.SELFDESTRUCT none target =
        .ok targetPost at hTarget
    cases hPop : target.stack.pop with
    | none =>
        rw [EvmYul_step_selfdestruct_stackUnderflow_of_pop_none hPop] at hTarget
        cases hTarget
    | some popped =>
        rcases popped with ⟨stack, recipient⟩
        have hStackTarget : target.stack = recipient :: stack :=
          stack_eq_cons_of_pop hPop
        rw [EvmYul.EVM.step_selfdestruct_of_stack target recipient stack
          hStackTarget] at hTarget
        cases hTarget
        let fullGas : EVMState :=
          { target with
            gasAvailable := full.gasAvailable,
            execLength := full.execLength }
        have hStackFull : fullGas.stack = recipient :: stack := by
          simpa [fullGas] using hStackTarget
        refine
          ⟨{ (EvmYul.EVM.selfdestructState fullGas recipient stack) with
              toMachineState :=
                (EvmYul.EVM.selfdestructState fullGas recipient stack).toMachineState.setHReturn
                  ByteArray.empty },
            ?_, ?_⟩
        · simpa [fullGas] using
            EvmYul.EVM.step_selfdestruct_of_stack fullGas recipient stack
              hStackFull
        · simp [GasExecRel, fullGas, EvmYul.EVM.selfdestructState,
            EvmYul.selfdestructAccountMap, EvmYul.MachineState.setHReturn,
            EvmYul.EVM.State.replaceStackAndIncrPC, EvmYul.EVM.State.incrPC]

theorem EvmYul_step_targetInstr_preserves_gasExecRel
    {instr : TargetInstr}
    {full target fullPost targetPost : EVMState}
    (hNoCallCreate : targetInstrUsesCallCreate instr = false)
    (hRel : GasExecRel full target)
    (hTarget : Target.stepInstr instr target = .ok targetPost)
    (hFull : EvmYul.step instr.op instr.arg full = .ok fullPost) :
    GasExecRel fullPost targetPost := by
  cases instr with
  | push32 value =>
      exact EvmYul_step_push32_preserves_gasExecRel hRel hTarget hFull
  | jump =>
      exact EvmYul_step_jump_preserves_gasExecRel hRel hTarget hFull
  | jumpi =>
      exact EvmYul_step_jumpi_preserves_gasExecRel hRel hTarget hFull
  | jumpdest =>
      exact EvmYul_step_jumpdest_preserves_gasExecRel hRel hTarget hFull
  | prim op =>
      change op.step target = .ok targetPost at hTarget
      change EvmYul.step op.toEVM none full = .ok fullPost at hFull
      cases hStep : op.continuingStep? with
      | none =>
          exact
            EvmYul_step_noncontinuing_prim_preserves_gasExecRel
              hStep (by simpa [targetInstrUsesCallCreate] using hNoCallCreate)
              hRel hTarget hFull
      | some step =>
          have hTargetRun : step.run target = .ok targetPost := by
            rw [PrimOp.step_eq_continuingStep_run hStep] at hTarget
            exact hTarget
          exact
            EvmYul_step_continuing_prim_preserves_gasExecRel hStep hRel
              hTargetRun hFull

theorem EVM_step_targetInstr_preserves_gasExecRel
    {fuel gasCost : Nat} {instr : TargetInstr}
    {full target fullPost targetPost : EVMState}
    (hNoCallCreate : targetInstrUsesCallCreate instr = false)
    (hRel : GasExecRel full target)
    (hTarget : Target.stepInstr instr target = .ok targetPost)
    (hFull :
      EvmYul.EVM.step fuel.succ gasCost (some (instr.op, instr.arg)) full =
        .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [EVM_step_targetInstr_eq_of_no_call_create
    (fuel := fuel) (gasCost := gasCost) (state := full)
    (instr := instr) hNoCallCreate] at hFull
  exact
    EvmYul_step_targetInstr_preserves_gasExecRel hNoCallCreate
      (hRel.charge_left (cost := gasCost)) hTarget hFull

theorem EVM_step_targetInstr_preserves_gasExecRel_of_ok
    {fuel gasCost : Nat} {instr : TargetInstr}
    {full target fullPost targetPost : EVMState}
    (hNoCallCreate : targetInstrUsesCallCreate instr = false)
    (hRel : GasExecRel full target)
    (hTarget : Target.stepInstr instr target = .ok targetPost)
    (hFull :
      EvmYul.EVM.step fuel gasCost (some (instr.op, instr.arg)) full =
        .ok fullPost) :
    GasExecRel fullPost targetPost := by
  cases fuel with
  | zero =>
      simp [EvmYul.EVM.step] at hFull
  | succ fuel =>
      exact
        EVM_step_targetInstr_preserves_gasExecRel
          (fuel := fuel) (gasCost := gasCost) hNoCallCreate hRel hTarget
          hFull

set_option maxHeartbeats 2000000 in
theorem EvmYul_step_control_targetInstr_exists_gasExecRel
    {instr : TargetInstr} {value : Word}
    {full target targetPost : EVMState}
    (hControl :
      instr = .push32 value ∨ instr = .jump ∨ instr = .jumpi ∨
        instr = .jumpdest)
    (hRel : GasExecRel full target)
    (hTarget : Target.stepInstr instr target = .ok targetPost) :
    ∃ fullPost,
      EvmYul.step instr.op instr.arg full = .ok fullPost ∧
        GasExecRel fullPost targetPost := by
  rcases hControl with hPush | hJump | hJumpi | hJumpdest
  · subst instr
    rw [hRel]
    simp [Target.stepInstr] at hTarget
    cases hTarget
    refine ⟨_, rfl, ?_⟩
    simp [GasExecRel, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC]
  · subst instr
    rw [hRel]
    cases hPop : target.stack.pop with
    | none =>
        simp [Target.stepInstr, hPop] at hTarget
    | some popped =>
        rcases popped with ⟨stack, dest⟩
        simp [Target.stepInstr, hPop] at hTarget
        cases hTarget
        have hStack : target.stack = dest :: stack :=
          stack_eq_cons_of_pop hPop
        let fullState : EVMState :=
          { target with
            gasAvailable := full.gasAvailable,
            execLength := full.execLength }
        refine ⟨{ fullState with pc := dest, stack := stack }, ?_, ?_⟩
        · simpa [TargetInstr.op, TargetInstr.arg, fullState] using
            EvmYul_step_jump_of_stack
              fullState stack dest (by simpa [fullState] using hStack)
        · simp [GasExecRel, fullState]
  · subst instr
    rw [hRel]
    cases hPop : target.stack.pop2 with
    | none =>
        simp [Target.stepInstr, hPop] at hTarget
    | some popped =>
        rcases popped with ⟨stack, dest, cond⟩
        simp [Target.stepInstr, hPop] at hTarget
        cases hTarget
        have hStack : target.stack = dest :: cond :: stack :=
          stack_eq_cons_cons_of_pop2 hPop
        let fullState : EVMState :=
          { target with
            gasAvailable := full.gasAvailable,
            execLength := full.execLength }
        refine
          ⟨{ fullState with
              pc :=
                if cond != EvmYul.UInt256.ofNat 0 then
                  dest
                else
                  fullState.pc + EvmYul.UInt256.ofNat 1,
              stack := stack },
            ?_, ?_⟩
        · simpa [TargetInstr.op, TargetInstr.arg, fullState] using
            EvmYul_step_jumpi_of_stack
              fullState stack dest cond (by simpa [fullState] using hStack)
        · simp [GasExecRel, fullState]
  · subst instr
    rw [hRel]
    simp [Target.stepInstr] at hTarget
    cases hTarget
    let fullState : EVMState :=
      { target with
        gasAvailable := full.gasAvailable,
        execLength := full.execLength }
    refine ⟨EvmYul.EVM.State.incrPC fullState, ?_, ?_⟩
    · simpa [TargetInstr.op, TargetInstr.arg, fullState] using
        EvmYul_step_jumpdest_eq fullState
    · simp [GasExecRel, EvmYul.EVM.State.incrPC, fullState]

theorem EvmYul_step_targetInstr_exists_gasExecRel
    {instr : TargetInstr}
    {full target targetPost : EVMState}
    (hNoCallCreate : targetInstrUsesCallCreate instr = false)
    (hRel : GasExecRel full target)
    (hTarget : Target.stepInstr instr target = .ok targetPost) :
    ∃ fullPost,
      EvmYul.step instr.op instr.arg full = .ok fullPost ∧
        GasExecRel fullPost targetPost := by
  cases instr with
  | push32 value =>
      exact
        EvmYul_step_control_targetInstr_exists_gasExecRel
          (value := value) (hControl := Or.inl rfl) hRel hTarget
  | jump =>
      exact
        EvmYul_step_control_targetInstr_exists_gasExecRel
          (value := EvmYul.UInt256.ofNat 0)
          (hControl := Or.inr (Or.inl rfl)) hRel hTarget
  | jumpi =>
      exact
        EvmYul_step_control_targetInstr_exists_gasExecRel
          (value := EvmYul.UInt256.ofNat 0)
          (hControl := Or.inr (Or.inr (Or.inl rfl))) hRel hTarget
  | jumpdest =>
      exact
        EvmYul_step_control_targetInstr_exists_gasExecRel
          (value := EvmYul.UInt256.ofNat 0)
          (hControl := Or.inr (Or.inr (Or.inr rfl))) hRel hTarget
  | prim op =>
      change op.step target = .ok targetPost at hTarget
      change
        ∃ fullPost,
          EvmYul.step op.toEVM none full = .ok fullPost ∧
            GasExecRel fullPost targetPost
      cases hStep : op.continuingStep? with
      | none =>
          exact
            EvmYul_step_noncontinuing_prim_exists_gasExecRel
              hStep (by simpa [targetInstrUsesCallCreate] using hNoCallCreate)
              hRel hTarget
      | some step =>
          have hTargetRun : step.run target = .ok targetPost := by
            rw [PrimOp.step_eq_continuingStep_run hStep] at hTarget
            exact hTarget
          exact
            EvmYul_step_continuing_prim_exists_gasExecRel hStep hRel
              hTargetRun

theorem EVM_step_targetInstr_exists_gasExecRel
    {fuel gasCost : Nat} {instr : TargetInstr}
    {full target targetPost : EVMState}
    (hNoCallCreate : targetInstrUsesCallCreate instr = false)
    (hRel : GasExecRel full target)
    (hTarget : Target.stepInstr instr target = .ok targetPost) :
    ∃ fullPost,
      EvmYul.EVM.step fuel.succ gasCost (some (instr.op, instr.arg)) full =
        .ok fullPost ∧
        GasExecRel fullPost targetPost := by
  obtain ⟨fullPost, hRun, hRelPost⟩ :=
    EvmYul_step_targetInstr_exists_gasExecRel hNoCallCreate
      (hRel.charge_left (cost := gasCost)) hTarget
  refine ⟨fullPost, ?_, hRelPost⟩
  rw [EVM_step_targetInstr_eq_of_no_call_create
    (fuel := fuel) (gasCost := gasCost) (state := full)
    (instr := instr) hNoCallCreate]
  exact hRun

theorem Target.stepInstrResult_running_stepInstr
    {instr : TargetInstr} {state mid : EVMState}
    (hRun : Target.stepInstrResult instr state = .ok (.running mid)) :
    Target.stepInstr instr state = .ok mid ∧ instr.haltKind? = none := by
  unfold Target.stepInstrResult at hRun
  cases hStep : Target.stepInstr instr state with
  | error err =>
      rw [hStep] at hRun
      cases hRun
  | ok state' =>
      rw [hStep] at hRun
      cases hKind : instr.haltKind? with
      | none =>
          rw [hKind] at hRun
          cases hRun
          exact ⟨rfl, rfl⟩
      | some kind =>
          rw [hKind] at hRun
          cases hRun

theorem Target.stepInstrResult_halted_stepInstr
    {instr : TargetInstr} {state : EVMState} {halt : Halt}
    (hRun : Target.stepInstrResult instr state = .ok (.halted halt)) :
    Target.stepInstr instr state = .ok halt.state ∧
      instr.haltKind? = some halt.kind ∧
        halt.output = halt.kind.output halt.state := by
  unfold Target.stepInstrResult at hRun
  cases hStep : Target.stepInstr instr state with
  | error err =>
      rw [hStep] at hRun
      cases hRun
  | ok state' =>
      rw [hStep] at hRun
      cases hKind : instr.haltKind? with
      | none =>
          rw [hKind] at hRun
          cases hRun
      | some kind =>
          rw [hKind] at hRun
          cases hRun
          exact ⟨rfl, rfl, rfl⟩

theorem Target.runListResult_cons_ok_cases
    {instr : TargetInstr} {rest : List TargetInstr}
    {state : EVMState} {result : StepResult}
    (hRun :
      Target.runListResult (instr :: rest) state = .ok result) :
    (∃ mid,
      Target.stepInstrResult instr state = .ok (.running mid) ∧
        Target.runListResult rest mid = .ok result) ∨
      (∃ halt,
        Target.stepInstrResult instr state = .ok (.halted halt) ∧
          result = .halted halt) := by
  unfold Target.runListResult at hRun
  cases hStep : Target.stepInstrResult instr state with
  | error err =>
      rw [hStep] at hRun
      cases hRun
  | ok stepResult =>
      rw [hStep] at hRun
      cases stepResult with
      | running mid =>
          exact Or.inl ⟨mid, rfl, hRun⟩
      | halted halt =>
          cases hRun
          exact Or.inr ⟨halt, rfl, rfl⟩

theorem HaltKind.output_eq_of_gasExecRel
    (kind : HaltKind) {full target : EVMState}
    (hRel : GasExecRel full target) :
  kind.output full = kind.output target := by
  rw [hRel]
  cases kind <;> simp [HaltKind.output]

theorem memoryExpansionCost_eq_of_gasExecRel {full target : EVMState}
    (hRel : GasExecRel full target) (op : EVMOp) :
    EvmYul.EVM.memoryExpansionCost full op =
      EvmYul.EVM.memoryExpansionCost target op := by
  rw [hRel]
  cases target
  rfl

set_option maxHeartbeats 2000000 in
theorem C'_eq_of_gasExecRel_of_targetInstr_no_call_create
    {full target : EVMState} {instr : TargetInstr}
    (hNoCallCreate : targetInstrUsesCallCreate instr = false)
    (hRel : GasExecRel full target) :
    EvmYul.EVM.C' full instr.op =
      EvmYul.EVM.C' target instr.op := by
  rw [hRel]
  cases target
  cases instr with
  | push32 value =>
      simp [TargetInstr.op, EvmYul.EVM.C']
  | jump =>
      simp [TargetInstr.op, EvmYul.EVM.C']
  | jumpi =>
      simp [TargetInstr.op, EvmYul.EVM.C']
  | jumpdest =>
      simp [TargetInstr.op, EvmYul.EVM.C']
  | prim op =>
      cases op <;>
        simp [targetInstrUsesCallCreate, PrimOp.isCallCreate,
          TargetInstr.op, PrimOp.toEVM, EvmYul.EVM.C',
          EvmYul.EVM.Csstore, EvmYul.EVM.Cselfdestruct] at hNoCallCreate ⊢

def jumpTargetAllowed (target? : Option Word)
    (validJumps : Array Word) : Prop :=
  match target? with
  | some target => validJumps.contains target = true
  | none => False

/--
The non-gas exceptional-halting checks performed by `EVM.X` before it calls
`EVM.step`. These are not made true by giving the machine more gas; they must
come from bytecode/path safety, stack bounds, static-mode compatibility, and
the no-CALL/CREATE fragment boundary.
-/
def XNonGasChecksPass (validJumps : Array Word) (state : EVMState)
    (op : EVMOp) : Prop :=
  EvmYul.EVM.δ op ≠ none ∧
    state.stack.length ≥ (EvmYul.EVM.δ op).getD 0 ∧
      (op = EvmYul.Operation.JUMP →
        jumpTargetAllowed state.stack[0]? validJumps) ∧
        (op = EvmYul.Operation.JUMPI →
          state.stack[1]? ≠ some ⟨0⟩ →
            jumpTargetAllowed state.stack[0]? validJumps) ∧
          (op = EvmYul.Operation.RETURNDATACOPY →
            (state.stack.getD 1 ⟨0⟩).toNat +
                (state.stack.getD 2 ⟨0⟩).toNat ≤
              state.returnData.size) ∧
            state.stack.length - (EvmYul.EVM.δ op).getD 0 +
                (EvmYul.EVM.α op).getD 0 ≤ 1024 ∧
              (state.executionEnv.perm = false →
                ¬ staticWriteSensitive op state.stack) ∧
                (op.isCreate = true →
                  state.stack.getD 2 ⟨0⟩ ≤ ⟨49152⟩)

theorem XNonGasChecksPass_iff_of_gasExecRel {validJumps : Array Word}
    {full target : EVMState} {op : EVMOp}
    (hRel : GasExecRel full target) :
    XNonGasChecksPass validJumps full op ↔
      XNonGasChecksPass validJumps target op := by
  rw [hRel]
  cases target
  rfl

/--
The gas-only checks performed by `EVM.X` before it calls `EVM.step`, expressed
against the state after the memory-expansion charge has been subtracted.
-/
def XGasChecksPassAt (state : EVMState) (op : EVMOp) : Prop :=
  EvmYul.EVM.memoryExpansionCost state op ≤ state.gasAvailable.toNat ∧
    EvmYul.EVM.C' (memoryGasState state op) op ≤
      (memoryGasState state op).gasAvailable.toNat ∧
      (op = EvmYul.Operation.SSTORE →
        GasConstants.Gcallstipend <
          (memoryGasState state op).gasAvailable.toNat)

def sstoreStipendExtra (op : EVMOp) : Nat :=
  if op = EvmYul.Operation.SSTORE then GasConstants.Gcallstipend + 1 else 0

def XGasRequiredAt (state : EVMState) (op : EVMOp) : Nat :=
  EvmYul.EVM.memoryExpansionCost state op +
    EvmYul.EVM.C' (memoryGasState state op) op +
      sstoreStipendExtra op

def xBodyState (state : EVMState) (op : EVMOp) : EVMState :=
  { memoryGasState state op with
    gasAvailable :=
      (memoryGasState state op).gasAvailable -
        EvmYul.UInt256.ofNat (EvmYul.EVM.C' (memoryGasState state op) op),
    execLength := (memoryGasState state op).execLength + 1 }

theorem XGasRequiredAt_eq_of_gasExecRel_of_targetInstr_no_call_create
    {full target : EVMState} {instr : TargetInstr}
    (hNoCallCreate : targetInstrUsesCallCreate instr = false)
    (hRel : GasExecRel full target) :
    XGasRequiredAt full instr.op =
      XGasRequiredAt target instr.op := by
  unfold XGasRequiredAt
  rw [memoryExpansionCost_eq_of_gasExecRel hRel instr.op]
  rw [C'_eq_of_gasExecRel_of_targetInstr_no_call_create
    hNoCallCreate (hRel.memoryGasState_both (op := instr.op))]

theorem memoryGasState_gasAvailable_toNat
    {state : EVMState} {op : EVMOp}
    (hMem :
      EvmYul.EVM.memoryExpansionCost state op ≤ state.gasAvailable.toNat) :
    (memoryGasState state op).gasAvailable.toNat =
      state.gasAvailable.toNat -
        EvmYul.EVM.memoryExpansionCost state op := by
  have hMemLt :
      EvmYul.EVM.memoryExpansionCost state op < EvmYul.UInt256.size :=
    lt_of_le_of_lt hMem state.gasAvailable.val.2
  have hMemNat :
      (EvmYul.UInt256.ofNat
        (EvmYul.EVM.memoryExpansionCost state op)).toNat =
          EvmYul.EVM.memoryExpansionCost state op :=
    Bytecode.uint256_ofNat_toNat_of_lt_size hMemLt
  have hSub :=
    uint256_sub_toNat_of_le
      (left := state.gasAvailable)
      (right :=
        EvmYul.UInt256.ofNat (EvmYul.EVM.memoryExpansionCost state op))
      (by simpa [hMemNat] using hMem)
  simpa [memoryGasState, hMemNat] using hSub

theorem xBodyState_gasAvailable_toNat_of_required
    {state : EVMState} {op : EVMOp} {restBudget : Nat}
    (hRequired :
      XGasRequiredAt state op + restBudget ≤ state.gasAvailable.toNat) :
    restBudget ≤ (xBodyState state op).gasAvailable.toNat := by
  have hMem :
      EvmYul.EVM.memoryExpansionCost state op ≤
        state.gasAvailable.toNat := by
    unfold XGasRequiredAt at hRequired
    omega
  have hMemGas :
      (memoryGasState state op).gasAvailable.toNat =
        state.gasAvailable.toNat -
          EvmYul.EVM.memoryExpansionCost state op :=
    memoryGasState_gasAvailable_toNat (state := state) (op := op) hMem
  have hCostLe :
      EvmYul.EVM.C' (memoryGasState state op) op ≤
        (memoryGasState state op).gasAvailable.toNat := by
    rw [hMemGas]
    unfold XGasRequiredAt at hRequired
    omega
  have hCostLt :
      EvmYul.EVM.C' (memoryGasState state op) op < EvmYul.UInt256.size :=
    lt_of_le_of_lt hCostLe (memoryGasState state op).gasAvailable.val.2
  have hCostNat :
      (EvmYul.UInt256.ofNat
        (EvmYul.EVM.C' (memoryGasState state op) op)).toNat =
          EvmYul.EVM.C' (memoryGasState state op) op :=
    Bytecode.uint256_ofNat_toNat_of_lt_size hCostLt
  have hSub :
      ((memoryGasState state op).gasAvailable -
          EvmYul.UInt256.ofNat
            (EvmYul.EVM.C' (memoryGasState state op) op)).toNat =
        (memoryGasState state op).gasAvailable.toNat -
          EvmYul.EVM.C' (memoryGasState state op) op := by
    simpa [hCostNat] using
      uint256_sub_toNat_of_le
        (left := (memoryGasState state op).gasAvailable)
        (right :=
          EvmYul.UInt256.ofNat
            (EvmYul.EVM.C' (memoryGasState state op) op))
        (by simpa [hCostNat] using hCostLe)
  have hRest :
      restBudget ≤
        (memoryGasState state op).gasAvailable.toNat -
          EvmYul.EVM.C' (memoryGasState state op) op := by
    rw [hMemGas]
    unfold XGasRequiredAt at hRequired
    omega
  change
    restBudget ≤
      ((memoryGasState state op).gasAvailable -
        EvmYul.UInt256.ofNat
          (EvmYul.EVM.C' (memoryGasState state op) op)).toNat
  rw [hSub]
  exact hRest

theorem EVM_step_targetInstr_eq_xBodyState {fuel : Nat}
    {state : EVMState} {instr : TargetInstr}
    (hNoCallCreate : targetInstrUsesCallCreate instr = false) :
    EvmYul.EVM.step fuel.succ
        (EvmYul.EVM.C' (memoryGasState state instr.op) instr.op)
        (some (instr.op, instr.arg)) (memoryGasState state instr.op) =
      EvmYul.step instr.op instr.arg (xBodyState state instr.op) := by
  simpa [xBodyState] using
    EVM_step_targetInstr_eq_of_no_call_create
      (fuel := fuel)
      (gasCost := EvmYul.EVM.C' (memoryGasState state instr.op) instr.op)
      (state := memoryGasState state instr.op)
      (instr := instr) hNoCallCreate

theorem XGasChecksPassAt.of_required_le
    {state : EVMState} {op : EVMOp}
    (hRequired :
      XGasRequiredAt state op ≤ state.gasAvailable.toNat) :
    XGasChecksPassAt state op := by
  have hMem :
      EvmYul.EVM.memoryExpansionCost state op ≤ state.gasAvailable.toNat := by
    unfold XGasRequiredAt at hRequired
    omega
  have hGasAfter :=
    memoryGasState_gasAvailable_toNat (state := state) (op := op) hMem
  refine ⟨hMem, ?_, ?_⟩
  · rw [hGasAfter]
    unfold XGasRequiredAt at hRequired
    omega
  · intro hSstore
    rw [hGasAfter]
    subst op
    simp [XGasRequiredAt, sstoreStipendExtra] at hRequired
    omega

def XStepChecksPass (validJumps : Array Word) (state : EVMState)
    (op : EVMOp) : Prop :=
  XNonGasChecksPass validJumps state op ∧ XGasChecksPassAt state op

theorem XNonGasChecksPass_stop {validJumps : Array Word}
    {state : EVMState}
    (hStack : state.stack.length ≤ 1024) :
    XNonGasChecksPass validJumps state EvmYul.Operation.STOP := by
  simp [XNonGasChecksPass, jumpTargetAllowed, staticWriteSensitive,
    EvmYul.EVM.δ, EvmYul.EVM.α, EvmYul.Operation.isCreate, hStack]

theorem XStepChecksPass_stop_of_required_le {validJumps : Array Word}
    {state : EVMState}
    (hStack : state.stack.length ≤ 1024)
    (hRequired :
      XGasRequiredAt state EvmYul.Operation.STOP ≤ state.gasAvailable.toNat) :
    XStepChecksPass validJumps state EvmYul.Operation.STOP :=
  ⟨XNonGasChecksPass_stop hStack, XGasChecksPassAt.of_required_le hRequired⟩

theorem XStepChecksPass.of_nonGas_required_le {validJumps : Array Word}
    {state : EVMState} {op : EVMOp}
    (hNonGas : XNonGasChecksPass validJumps state op)
    (hRequired : XGasRequiredAt state op ≤ state.gasAvailable.toNat) :
    XStepChecksPass validJumps state op :=
  ⟨hNonGas, XGasChecksPassAt.of_required_le hRequired⟩

structure XStepRawChecksPass (validJumps : Array Word) (state : EVMState)
    (op : EVMOp) : Prop where
  memoryGas : ¬ (state.gasAvailable.toNat < EvmYul.EVM.memoryExpansionCost state op)
  dynamicGas : ¬ ((memoryGasState state op).gasAvailable.toNat <
    EvmYul.EVM.C' (memoryGasState state op) op)
  delta : ¬ (EvmYul.EVM.δ op = none)
  stack : ¬ ((memoryGasState state op).stack.length < (EvmYul.EVM.δ op).getD 0)
  jump : ¬ (op = EvmYul.Operation.JUMP ∧
    EvmYul.EVM.X.notIn (memoryGasState state op).stack[0]? validJumps = true)
  jumpi : ¬ (op = EvmYul.Operation.JUMPI ∧
    (memoryGasState state op).stack[1]? ≠ some (⟨0⟩ : Word) ∧
      EvmYul.EVM.X.notIn (memoryGasState state op).stack[0]? validJumps = true)
  returnData : ¬ (op = EvmYul.Operation.RETURNDATACOPY ∧
    ((memoryGasState state op).stack.getD 1 (⟨0⟩ : Word)).toNat +
      ((memoryGasState state op).stack.getD 2 (⟨0⟩ : Word)).toNat >
        (memoryGasState state op).returnData.size)
  stackOverflow : ¬ ((memoryGasState state op).stack.length -
      (EvmYul.EVM.δ op).getD 0 + (EvmYul.EVM.α op).getD 0 > 1024)
  staticMode : ¬ ((¬ (memoryGasState state op).executionEnv.perm) ∧
    (op ∈ [EvmYul.Operation.CREATE, EvmYul.Operation.CREATE2,
      EvmYul.Operation.SSTORE, EvmYul.Operation.SELFDESTRUCT,
      EvmYul.Operation.LOG0, EvmYul.Operation.LOG1, EvmYul.Operation.LOG2,
      EvmYul.Operation.LOG3, EvmYul.Operation.LOG4,
      EvmYul.Operation.TSTORE] ∨
      (op = EvmYul.Operation.CALL ∧
        (memoryGasState state op).stack[2]? ≠ some (⟨0⟩ : Word))))
  sstoreStipend : ¬ (op = EvmYul.Operation.SSTORE ∧
    (memoryGasState state op).gasAvailable.toNat ≤ GasConstants.Gcallstipend)
  createSize : ¬ (op.isCreate = true ∧
    (memoryGasState state op).stack.getD 2 (⟨0⟩ : Word) > (⟨49152⟩ : Word))

def XHaltOutput? (op : EVMOp) (state : EVMState) : Option ByteArray :=
  if op ∈ [EvmYul.Operation.RETURN, EvmYul.Operation.REVERT] then
    some state.toMachineState.H_return
  else if op ∈ [EvmYul.Operation.STOP, EvmYul.Operation.SELFDESTRUCT] then
    some ByteArray.empty
  else
    none

def XStepHaltOutput? (op : EVMOp) (state : EVMState) : Option ByteArray :=
  if op = EvmYul.Operation.RETURN ∨ op = EvmYul.Operation.REVERT then
    some state.toMachineState.H_return
  else if op = EvmYul.Operation.STOP ∨ op = EvmYul.Operation.SELFDESTRUCT then
    some ByteArray.empty
  else
    none

theorem XHaltOutput?_eq_XStepHaltOutput?
    (op : EVMOp) (state : EVMState) :
    XHaltOutput? op state = XStepHaltOutput? op state := by
  simp [XHaltOutput?, XStepHaltOutput?]

theorem XHaltOutput?_none_of_targetInstr_haltKind_none
    {instr : TargetInstr} {state : EVMState}
    (hKind : instr.haltKind? = none) :
    XHaltOutput? instr.op state = none := by
  cases instr with
  | push32 value =>
      rfl
  | jump =>
      rfl
  | jumpi =>
      rfl
  | jumpdest =>
      rfl
  | prim op =>
      cases op <;> simp [TargetInstr.haltKind?, PrimOp.haltKind?,
        TargetInstr.op, PrimOp.toEVM, XHaltOutput?] at hKind ⊢

theorem XHaltOutput?_some_of_targetInstr_haltKind_some
    {instr : TargetInstr} {state : EVMState} {kind : HaltKind}
    (hKind : instr.haltKind? = some kind) :
    XHaltOutput? instr.op state = some (kind.output state) := by
  cases instr with
  | push32 value =>
      simp [TargetInstr.haltKind?] at hKind
  | jump =>
      simp [TargetInstr.haltKind?] at hKind
  | jumpi =>
      simp [TargetInstr.haltKind?] at hKind
  | jumpdest =>
      simp [TargetInstr.haltKind?] at hKind
  | prim op =>
      cases op <;> simp [TargetInstr.haltKind?, PrimOp.haltKind?,
        TargetInstr.op, PrimOp.toEVM, XHaltOutput?, HaltKind.output] at hKind ⊢
      all_goals cases hKind
      all_goals rfl

theorem targetInstr_op_ne_revert_of_haltKind_some_ne
    {instr : TargetInstr} {kind : HaltKind}
    (hKind : instr.haltKind? = some kind)
    (hNotRevert : kind ≠ .revert) :
    instr.op ≠ EvmYul.Operation.REVERT := by
  intro hOp
  cases instr with
  | push32 value =>
      simp [TargetInstr.haltKind?] at hKind
  | jump =>
      simp [TargetInstr.haltKind?] at hKind
  | jumpi =>
      simp [TargetInstr.haltKind?] at hKind
  | jumpdest =>
      simp [TargetInstr.haltKind?] at hKind
  | prim op =>
      cases op <;> simp [TargetInstr.haltKind?, PrimOp.haltKind?,
        TargetInstr.op, PrimOp.toEVM] at hKind hOp
      cases hKind
      exact hNotRevert rfl

theorem targetInstr_op_eq_revert_of_haltKind_revert
    {instr : TargetInstr}
    (hKind : instr.haltKind? = some .revert) :
    instr.op = EvmYul.Operation.REVERT := by
  cases instr with
  | push32 value =>
      simp [TargetInstr.haltKind?] at hKind
  | jump =>
      simp [TargetInstr.haltKind?] at hKind
  | jumpi =>
      simp [TargetInstr.haltKind?] at hKind
  | jumpdest =>
      simp [TargetInstr.haltKind?] at hKind
  | prim op =>
      cases op <;> simp [TargetInstr.haltKind?, PrimOp.haltKind?,
        TargetInstr.op, PrimOp.toEVM] at hKind ⊢

theorem XStepRawChecksPass.of_step_checks {validJumps : Array Word}
    {state : EVMState} {op : EVMOp}
    (hChecks : XStepChecksPass validJumps state op) :
    XStepRawChecksPass validJumps state op := by
  rcases hChecks with ⟨hNon, hGas⟩
  rcases hNon with
    ⟨hDelta, hStack, hJump, hJumpi, hReturnData, hOverflow, hStatic, hCreate⟩
  rcases hGas with ⟨hMemoryGas, hDynamicGas, hSstore⟩
  refine
    { memoryGas := ?_
      dynamicGas := ?_
      delta := hDelta
      stack := ?_
      jump := ?_
      jumpi := ?_
      returnData := ?_
      stackOverflow := ?_
      staticMode := ?_
      sstoreStipend := ?_
      createSize := ?_ }
  · omega
  · omega
  · simpa [memoryGasState] using (not_lt_of_ge hStack)
  · intro hBad
    rcases hBad with ⟨hOp, hBad⟩
    have hAllowed := hJump hOp
    unfold jumpTargetAllowed at hAllowed
    subst op
    cases hTarget : state.stack[0]? with
    | none =>
        simp [hTarget] at hAllowed
    | some target =>
        simp [hTarget] at hAllowed
        simp [memoryGasState, EvmYul.EVM.X.notIn, EvmYul.EVM.X.belongs,
          hTarget, hAllowed] at hBad
  · intro hBad
    rcases hBad with ⟨hOp, hCond, hBad⟩
    have hCond' : state.stack[1]? ≠ some (⟨0⟩ : Word) := by
      simpa [memoryGasState] using hCond
    have hAllowed := hJumpi hOp hCond'
    unfold jumpTargetAllowed at hAllowed
    subst op
    cases hTarget : state.stack[0]? with
    | none =>
        simp [hTarget] at hAllowed
    | some target =>
        simp [hTarget] at hAllowed
        simp [memoryGasState, EvmYul.EVM.X.notIn, EvmYul.EVM.X.belongs,
          hTarget, hAllowed] at hBad
  · intro hBad
    exact (not_lt_of_ge (hReturnData hBad.1)) (by
      simpa [memoryGasState] using hBad.2)
  · simpa [memoryGasState] using (not_lt_of_ge hOverflow)
  · intro hBad
    rcases hBad with ⟨hNoPerm, hWrite⟩
    have hPermFalse : state.executionEnv.perm = false := by
      simpa using hNoPerm
    exact (hStatic hPermFalse) (by
      simpa [memoryGasState, staticWriteSensitive, or_assoc] using hWrite)
  · intro hBad
    exact (not_le_of_gt (hSstore hBad.1)) hBad.2
  · intro hBad
    have hCreateGet :
        state.stack[2]?.getD (⟨0⟩ : Word) ≤ (⟨49152⟩ : Word) := by
      simpa using hCreate hBad.1
    have hTooLarge0 := hBad.2
    simp [memoryGasState] at hTooLarge0
    have hTooLarge :
        (⟨49152⟩ : Word).val <
          (state.stack[2]?.getD (⟨0⟩ : Word)).val := by
      change (⟨49152⟩ : Word).val <
        (state.stack[2]?.getD (⟨0⟩ : Word)).val at hTooLarge0
      exact hTooLarge0
    have hCreateGet0 := hCreateGet
    have hCreateVal :
        (state.stack[2]?.getD (⟨0⟩ : Word)).val ≤
          (⟨49152⟩ : Word).val := by
      change (state.stack[2]?.getD (⟨0⟩ : Word)).val ≤
        (⟨49152⟩ : Word).val at hCreateGet0
      exact hCreateGet0
    exact (not_lt_of_ge hCreateVal) hTooLarge

set_option linter.unusedSimpArgs false in
theorem X_step_expand_of_raw_checks_of_getD {fuel : Nat}
    {validJumps : Array Word}
    {state : EVMState} {op : EVMOp} {arg : Option (Word × Nat)}
    (hInstr :
      (EvmYul.EVM.decode state.executionEnv.code state.pc).getD
        (EvmYul.Operation.STOP, none) = (op, arg))
    (hChecks : XStepRawChecksPass validJumps state op) :
    EvmYul.EVM.X fuel.succ validJumps state =
      (do
        let evmState' ←
          EvmYul.EVM.step fuel (EvmYul.EVM.C' (memoryGasState state op) op)
            (some (op, arg)) (memoryGasState state op)
        match XStepHaltOutput? op evmState' with
        | none => EvmYul.EVM.X fuel validJumps evmState'
        | some output =>
            if op = EvmYul.Operation.REVERT then
              .ok (EvmYul.EVM.ExecutionResult.revert evmState'.gasAvailable output)
            else
              .ok (EvmYul.EVM.ExecutionResult.success evmState' output)) := by
  have hDynamic : ¬ ((state.gasAvailable -
        EvmYul.UInt256.ofNat (EvmYul.EVM.memoryExpansionCost state op)).toNat <
      EvmYul.EVM.C'
        { state with
          gasAvailable :=
            state.gasAvailable -
              EvmYul.UInt256.ofNat (EvmYul.EVM.memoryExpansionCost state op) }
        op) := by
    simpa [memoryGasState] using hChecks.dynamicGas
  have hStack : ¬ (state.stack.length < (EvmYul.EVM.δ op).getD 0) := by
    simpa [memoryGasState] using hChecks.stack
  have hJump : ¬ (op = EvmYul.Operation.JUMP ∧
      EvmYul.EVM.X.notIn state.stack[0]? validJumps = true) := by
    simpa [memoryGasState] using hChecks.jump
  have hJumpi : ¬ (op = EvmYul.Operation.JUMPI ∧
      state.stack[1]? ≠ some (⟨0⟩ : Word) ∧
        EvmYul.EVM.X.notIn state.stack[0]? validJumps = true) := by
    simpa [memoryGasState] using hChecks.jumpi
  have hReturnData : ¬ (op = EvmYul.Operation.RETURNDATACOPY ∧
      state.returnData.size <
        (state.stack.getD 1 (⟨0⟩ : Word)).toNat +
          (state.stack.getD 2 (⟨0⟩ : Word)).toNat) := by
    simpa [memoryGasState, Nat.lt_iff_add_one_le] using hChecks.returnData
  have hStackOverflow : ¬ (1024 <
      state.stack.length - (EvmYul.EVM.δ op).getD 0 +
        (EvmYul.EVM.α op).getD 0) := by
    simpa [memoryGasState] using hChecks.stackOverflow
  have hStatic : ¬ (state.executionEnv.perm = false ∧
      ((op = EvmYul.Operation.CREATE ∨
          op = EvmYul.Operation.CREATE2 ∨
            op = EvmYul.Operation.SSTORE ∨
              op = EvmYul.Operation.SELFDESTRUCT ∨
                op = EvmYul.Operation.LOG0 ∨
                  op = EvmYul.Operation.LOG1 ∨
                    op = EvmYul.Operation.LOG2 ∨
                      op = EvmYul.Operation.LOG3 ∨
                        op = EvmYul.Operation.LOG4 ∨
                          op = EvmYul.Operation.TSTORE) ∨
        op = EvmYul.Operation.CALL ∧
          state.stack[2]? ≠ some (⟨0⟩ : Word))) := by
    simpa [memoryGasState] using hChecks.staticMode
  have hSstore : ¬ (op = EvmYul.Operation.SSTORE ∧
      (state.gasAvailable -
          EvmYul.UInt256.ofNat (EvmYul.EVM.memoryExpansionCost state op)).toNat ≤
        GasConstants.Gcallstipend) := by
    simpa [memoryGasState] using hChecks.sstoreStipend
  have hCreate : ¬ (op.isCreate = true ∧
      (⟨49152⟩ : Word) <
        state.stack.getD 2 (⟨0⟩ : Word)) := by
    simpa [memoryGasState] using hChecks.createSize
  have hReturnData' : ¬ (op = EvmYul.Operation.RETURNDATACOPY ∧
      state.returnData.size <
        (state.stack[1]?.getD (⟨0⟩ : Word)).toNat +
          (state.stack[2]?.getD (⟨0⟩ : Word)).toNat) := by
    simpa using hReturnData
  have hStatic' : ¬ (state.executionEnv.perm = false ∧
      ((op = EvmYul.Operation.CREATE ∨
          op = EvmYul.Operation.CREATE2 ∨
            op = EvmYul.Operation.SSTORE ∨
              op = EvmYul.Operation.SELFDESTRUCT ∨
                op = EvmYul.Operation.LOG0 ∨
                  op = EvmYul.Operation.LOG1 ∨
                    op = EvmYul.Operation.LOG2 ∨
                      op = EvmYul.Operation.LOG3 ∨
                        op = EvmYul.Operation.LOG4 ∨
                          op = EvmYul.Operation.TSTORE) ∨
        op = EvmYul.Operation.CALL ∧
          ¬ state.stack[2]? = some (⟨0⟩ : Word))) := by
    simpa using hStatic
  have hCreate' : ¬ (op.isCreate = true ∧
      (⟨49152⟩ : Word) < state.stack[2]?.getD (⟨0⟩ : Word)) := by
    simpa using hCreate
  simp [EvmYul.EVM.X, hInstr, hChecks.memoryGas, hDynamic,
    hChecks.delta, hStack, hJump, hStackOverflow, hSstore]
  rw [if_neg hJumpi]
  rw [if_neg hReturnData']
  rw [if_neg hStatic']
  rw [if_neg hCreate']
  change
    (match
      pure
        ({ state with
          gasAvailable :=
            state.gasAvailable -
              EvmYul.UInt256.ofNat (EvmYul.EVM.memoryExpansionCost state op) },
          EvmYul.EVM.C'
            { state with
              gasAvailable :=
                state.gasAvailable -
                  EvmYul.UInt256.ofNat (EvmYul.EVM.memoryExpansionCost state op) }
            op) with
    | Except.error e => Except.error e
    | Except.ok (evmState, cost₂) => do
      let evmState' ← EvmYul.EVM.step fuel cost₂ (some (op, arg)) evmState
      match XStepHaltOutput? op evmState' with
      | none => EvmYul.EVM.X fuel validJumps evmState'
      | some output =>
          if op = EvmYul.Operation.REVERT then
            .ok (EvmYul.EVM.ExecutionResult.revert evmState'.gasAvailable output)
          else
            .ok (EvmYul.EVM.ExecutionResult.success evmState' output)) =
      (do
        let evmState' ←
          EvmYul.EVM.step fuel
            (EvmYul.EVM.C'
              { state with
                gasAvailable :=
                  state.gasAvailable -
                    EvmYul.UInt256.ofNat
                      (EvmYul.EVM.memoryExpansionCost state op) }
              op)
            (some (op, arg))
            { state with
              gasAvailable :=
                state.gasAvailable -
                  EvmYul.UInt256.ofNat
                    (EvmYul.EVM.memoryExpansionCost state op) }
        match XStepHaltOutput? op evmState' with
        | none => EvmYul.EVM.X fuel validJumps evmState'
        | some output =>
            if op = EvmYul.Operation.REVERT then
              .ok (EvmYul.EVM.ExecutionResult.revert evmState'.gasAvailable output)
            else
              .ok (EvmYul.EVM.ExecutionResult.success evmState' output))
  rfl

theorem X_step_expand_of_raw_checks {fuel : Nat} {validJumps : Array Word}
    {state : EVMState} {op : EVMOp} {arg : Option (Word × Nat)}
    (hDecode : EvmYul.EVM.decode state.executionEnv.code state.pc = some (op, arg))
    (hChecks : XStepRawChecksPass validJumps state op) :
    EvmYul.EVM.X fuel.succ validJumps state =
      (do
        let evmState' ←
          EvmYul.EVM.step fuel (EvmYul.EVM.C' (memoryGasState state op) op)
            (some (op, arg)) (memoryGasState state op)
        match XStepHaltOutput? op evmState' with
        | none => EvmYul.EVM.X fuel validJumps evmState'
        | some output =>
            if op = EvmYul.Operation.REVERT then
              .ok (EvmYul.EVM.ExecutionResult.revert evmState'.gasAvailable output)
            else
              .ok (EvmYul.EVM.ExecutionResult.success evmState' output)) := by
  exact
    X_step_expand_of_raw_checks_of_getD
      (by simp [hDecode]) hChecks

theorem X_step_expand_default_stop_of_raw_checks {fuel : Nat}
    {validJumps : Array Word} {state : EVMState}
    (hDecodeNone : EvmYul.EVM.decode state.executionEnv.code state.pc = none)
    (hChecks :
      XStepRawChecksPass validJumps state EvmYul.Operation.STOP) :
    EvmYul.EVM.X fuel.succ validJumps state =
      (do
        let evmState' ←
          EvmYul.EVM.step fuel
            (EvmYul.EVM.C'
              (memoryGasState state EvmYul.Operation.STOP)
              EvmYul.Operation.STOP)
            (some (EvmYul.Operation.STOP, none))
            (memoryGasState state EvmYul.Operation.STOP)
        match XStepHaltOutput? EvmYul.Operation.STOP evmState' with
        | none => EvmYul.EVM.X fuel validJumps evmState'
        | some output =>
            if (EvmYul.Operation.STOP : EVMOp) =
                (EvmYul.Operation.REVERT : EVMOp) then
              .ok (EvmYul.EVM.ExecutionResult.revert evmState'.gasAvailable output)
            else
              .ok (EvmYul.EVM.ExecutionResult.success evmState' output)) := by
  exact
    X_step_expand_of_raw_checks_of_getD
      (by simp [hDecodeNone]) hChecks

theorem X_step_running_of_raw_checks {fuel : Nat} {validJumps : Array Word}
    {state post : EVMState} {op : EVMOp} {arg : Option (Word × Nat)}
    (hDecode : EvmYul.EVM.decode state.executionEnv.code state.pc = some (op, arg))
    (hChecks : XStepRawChecksPass validJumps state op)
    (hStep : EvmYul.EVM.step fuel (EvmYul.EVM.C' (memoryGasState state op) op)
      (some (op, arg)) (memoryGasState state op) = .ok post)
    (hNoHalt : XHaltOutput? op post = none) :
    EvmYul.EVM.X fuel.succ validJumps state =
      EvmYul.EVM.X fuel validJumps post := by
  have hDynamic : ¬ ((state.gasAvailable -
        EvmYul.UInt256.ofNat (EvmYul.EVM.memoryExpansionCost state op)).toNat <
      EvmYul.EVM.C'
        { state with
          gasAvailable :=
            state.gasAvailable -
              EvmYul.UInt256.ofNat (EvmYul.EVM.memoryExpansionCost state op) }
        op) := by
    simpa [memoryGasState] using hChecks.dynamicGas
  have hStack : ¬ (state.stack.length < (EvmYul.EVM.δ op).getD 0) := by
    simpa [memoryGasState] using hChecks.stack
  have hJump : ¬ (op = EvmYul.Operation.JUMP ∧
      EvmYul.EVM.X.notIn state.stack[0]? validJumps = true) := by
    simpa [memoryGasState] using hChecks.jump
  have hJumpi : ¬ (op = EvmYul.Operation.JUMPI ∧
      state.stack[1]? ≠ some (⟨0⟩ : Word) ∧
        EvmYul.EVM.X.notIn state.stack[0]? validJumps = true) := by
    simpa [memoryGasState] using hChecks.jumpi
  have hReturnData : ¬ (op = EvmYul.Operation.RETURNDATACOPY ∧
      state.returnData.size <
        (state.stack.getD 1 (⟨0⟩ : Word)).toNat +
          (state.stack.getD 2 (⟨0⟩ : Word)).toNat) := by
    simpa [memoryGasState, Nat.lt_iff_add_one_le] using hChecks.returnData
  have hStackOverflow : ¬ (1024 <
      state.stack.length - (EvmYul.EVM.δ op).getD 0 +
        (EvmYul.EVM.α op).getD 0) := by
    simpa [memoryGasState] using hChecks.stackOverflow
  have hStatic : ¬ (state.executionEnv.perm = false ∧
      ((op = EvmYul.Operation.CREATE ∨
          op = EvmYul.Operation.CREATE2 ∨
            op = EvmYul.Operation.SSTORE ∨
              op = EvmYul.Operation.SELFDESTRUCT ∨
                op = EvmYul.Operation.LOG0 ∨
                  op = EvmYul.Operation.LOG1 ∨
                    op = EvmYul.Operation.LOG2 ∨
                      op = EvmYul.Operation.LOG3 ∨
                        op = EvmYul.Operation.LOG4 ∨
                          op = EvmYul.Operation.TSTORE) ∨
        op = EvmYul.Operation.CALL ∧
          state.stack[2]? ≠ some (⟨0⟩ : Word))) := by
    simpa [memoryGasState] using hChecks.staticMode
  have hSstore : ¬ (op = EvmYul.Operation.SSTORE ∧
      (state.gasAvailable -
          EvmYul.UInt256.ofNat (EvmYul.EVM.memoryExpansionCost state op)).toNat ≤
        GasConstants.Gcallstipend) := by
    simpa [memoryGasState] using hChecks.sstoreStipend
  have hCreate : ¬ (op.isCreate = true ∧
      (⟨49152⟩ : Word) <
        state.stack.getD 2 (⟨0⟩ : Word)) := by
    simpa [memoryGasState] using hChecks.createSize
  have hReturnData' : ¬ (op = EvmYul.Operation.RETURNDATACOPY ∧
      state.returnData.size <
        (state.stack[1]?.getD (⟨0⟩ : Word)).toNat +
          (state.stack[2]?.getD (⟨0⟩ : Word)).toNat) := by
    simpa using hReturnData
  have hStatic' : ¬ (state.executionEnv.perm = false ∧
      ((op = EvmYul.Operation.CREATE ∨
          op = EvmYul.Operation.CREATE2 ∨
            op = EvmYul.Operation.SSTORE ∨
              op = EvmYul.Operation.SELFDESTRUCT ∨
                op = EvmYul.Operation.LOG0 ∨
                  op = EvmYul.Operation.LOG1 ∨
                    op = EvmYul.Operation.LOG2 ∨
                      op = EvmYul.Operation.LOG3 ∨
                        op = EvmYul.Operation.LOG4 ∨
                          op = EvmYul.Operation.TSTORE) ∨
        op = EvmYul.Operation.CALL ∧
          ¬ state.stack[2]? = some (⟨0⟩ : Word))) := by
    simpa using hStatic
  have hCreate' : ¬ (op.isCreate = true ∧
      (⟨49152⟩ : Word) < state.stack[2]?.getD (⟨0⟩ : Word)) := by
    simpa using hCreate
  have hStep' :
      EvmYul.EVM.step fuel
          (EvmYul.EVM.C'
            { state with
              gasAvailable :=
                state.gasAvailable -
                  EvmYul.UInt256.ofNat
                    (EvmYul.EVM.memoryExpansionCost state op) }
            op)
          (some (op, arg))
          { state with
            gasAvailable :=
              state.gasAvailable -
                EvmYul.UInt256.ofNat (EvmYul.EVM.memoryExpansionCost state op) } =
        .ok post := by
    simpa [memoryGasState] using hStep
  simp [EvmYul.EVM.X, hDecode, hChecks.memoryGas, hDynamic,
    hChecks.delta, hStack, hJump, hStackOverflow, hSstore] at hNoHalt ⊢
  rw [if_neg hJumpi]
  rw [if_neg hReturnData']
  rw [if_neg hStatic']
  rw [if_neg hCreate']
  change
    (do
      let evmState' ←
        EvmYul.EVM.step fuel
          (EvmYul.EVM.C'
            { state with
              gasAvailable :=
                state.gasAvailable -
                  EvmYul.UInt256.ofNat
                    (EvmYul.EVM.memoryExpansionCost state op) }
            op)
          (some (op, arg))
          { state with
            gasAvailable :=
              state.gasAvailable -
                EvmYul.UInt256.ofNat (EvmYul.EVM.memoryExpansionCost state op) }
      match
        if op = EvmYul.Operation.RETURN ∨ op = EvmYul.Operation.REVERT then
          some evmState'.H_return
        else if op = EvmYul.Operation.STOP ∨
            op = EvmYul.Operation.SELFDESTRUCT then
          some ByteArray.empty
        else
          none
      with
      | none => EvmYul.EVM.X fuel validJumps evmState'
      | some output =>
          if op = EvmYul.Operation.REVERT then
            .ok (EvmYul.EVM.ExecutionResult.revert evmState'.gasAvailable output)
          else
            .ok (EvmYul.EVM.ExecutionResult.success evmState' output)) =
      EvmYul.EVM.X fuel validJumps post
  rw [hStep']
  simp [XHaltOutput?] at hNoHalt
  change
    (match
        if op = EvmYul.Operation.RETURN ∨ op = EvmYul.Operation.REVERT then
          some post.H_return
        else if op = EvmYul.Operation.STOP ∨
            op = EvmYul.Operation.SELFDESTRUCT then
          some ByteArray.empty
        else
          none
      with
      | none => EvmYul.EVM.X fuel validJumps post
      | some output =>
          if op = EvmYul.Operation.REVERT then
            .ok (EvmYul.EVM.ExecutionResult.revert post.gasAvailable output)
          else
            .ok (EvmYul.EVM.ExecutionResult.success post output)) =
      EvmYul.EVM.X fuel validJumps post
  rw [hNoHalt]

theorem X_step_running_of_checks {fuel : Nat} {validJumps : Array Word}
    {state post : EVMState} {op : EVMOp} {arg : Option (Word × Nat)}
    (hDecode : EvmYul.EVM.decode state.executionEnv.code state.pc = some (op, arg))
    (hChecks : XStepChecksPass validJumps state op)
    (hStep : EvmYul.EVM.step fuel (EvmYul.EVM.C' (memoryGasState state op) op)
      (some (op, arg)) (memoryGasState state op) = .ok post)
    (hNoHalt : XHaltOutput? op post = none) :
    EvmYul.EVM.X fuel.succ validJumps state =
      EvmYul.EVM.X fuel validJumps post :=
  X_step_running_of_raw_checks hDecode
    (XStepRawChecksPass.of_step_checks hChecks) hStep hNoHalt

theorem X_step_success_of_raw_checks {fuel : Nat} {validJumps : Array Word}
    {state post : EVMState} {op : EVMOp} {arg : Option (Word × Nat)}
    {output : ByteArray}
    (hDecode : EvmYul.EVM.decode state.executionEnv.code state.pc = some (op, arg))
    (hChecks : XStepRawChecksPass validJumps state op)
    (hStep : EvmYul.EVM.step fuel (EvmYul.EVM.C' (memoryGasState state op) op)
      (some (op, arg)) (memoryGasState state op) = .ok post)
    (hHalt : XHaltOutput? op post = some output)
    (hNotRevert : op ≠ EvmYul.Operation.REVERT) :
    EvmYul.EVM.X fuel.succ validJumps state =
      .ok (EvmYul.EVM.ExecutionResult.success post output) := by
  rw [X_step_expand_of_raw_checks hDecode hChecks, hStep]
  have hHalt' : XStepHaltOutput? op post = some output := by
    simpa [XHaltOutput?_eq_XStepHaltOutput?] using hHalt
  change
    (match XStepHaltOutput? op post with
    | none => EvmYul.EVM.X fuel validJumps post
    | some output =>
        if op = EvmYul.Operation.REVERT then
          .ok (EvmYul.EVM.ExecutionResult.revert post.gasAvailable output)
        else
          .ok (EvmYul.EVM.ExecutionResult.success post output)) =
      .ok (EvmYul.EVM.ExecutionResult.success post output)
  rw [hHalt']
  simp [hNotRevert]

theorem X_step_success_of_checks {fuel : Nat} {validJumps : Array Word}
    {state post : EVMState} {op : EVMOp} {arg : Option (Word × Nat)}
    {output : ByteArray}
    (hDecode : EvmYul.EVM.decode state.executionEnv.code state.pc = some (op, arg))
    (hChecks : XStepChecksPass validJumps state op)
    (hStep : EvmYul.EVM.step fuel (EvmYul.EVM.C' (memoryGasState state op) op)
      (some (op, arg)) (memoryGasState state op) = .ok post)
    (hHalt : XHaltOutput? op post = some output)
    (hNotRevert : op ≠ EvmYul.Operation.REVERT) :
    EvmYul.EVM.X fuel.succ validJumps state =
      .ok (EvmYul.EVM.ExecutionResult.success post output) :=
  X_step_success_of_raw_checks hDecode
    (XStepRawChecksPass.of_step_checks hChecks) hStep hHalt hNotRevert

theorem X_step_revert_of_raw_checks {fuel : Nat} {validJumps : Array Word}
    {state post : EVMState} {op : EVMOp} {arg : Option (Word × Nat)}
    {output : ByteArray}
    (hDecode : EvmYul.EVM.decode state.executionEnv.code state.pc = some (op, arg))
    (hChecks : XStepRawChecksPass validJumps state op)
    (hStep : EvmYul.EVM.step fuel (EvmYul.EVM.C' (memoryGasState state op) op)
      (some (op, arg)) (memoryGasState state op) = .ok post)
    (hHalt : XHaltOutput? op post = some output)
    (hRevert : op = EvmYul.Operation.REVERT) :
    EvmYul.EVM.X fuel.succ validJumps state =
      .ok (EvmYul.EVM.ExecutionResult.revert post.gasAvailable output) := by
  rw [X_step_expand_of_raw_checks hDecode hChecks, hStep]
  have hHalt' : XStepHaltOutput? op post = some output := by
    simpa [XHaltOutput?_eq_XStepHaltOutput?] using hHalt
  change
    (match XStepHaltOutput? op post with
    | none => EvmYul.EVM.X fuel validJumps post
    | some output =>
        if op = EvmYul.Operation.REVERT then
          .ok (EvmYul.EVM.ExecutionResult.revert post.gasAvailable output)
        else
          .ok (EvmYul.EVM.ExecutionResult.success post output)) =
      .ok (EvmYul.EVM.ExecutionResult.revert post.gasAvailable output)
  rw [hHalt']
  simp [hRevert]

theorem X_step_revert_of_checks {fuel : Nat} {validJumps : Array Word}
    {state post : EVMState} {op : EVMOp} {arg : Option (Word × Nat)}
    {output : ByteArray}
    (hDecode : EvmYul.EVM.decode state.executionEnv.code state.pc = some (op, arg))
    (hChecks : XStepChecksPass validJumps state op)
    (hStep : EvmYul.EVM.step fuel (EvmYul.EVM.C' (memoryGasState state op) op)
      (some (op, arg)) (memoryGasState state op) = .ok post)
    (hHalt : XHaltOutput? op post = some output)
    (hRevert : op = EvmYul.Operation.REVERT) :
    EvmYul.EVM.X fuel.succ validJumps state =
      .ok (EvmYul.EVM.ExecutionResult.revert post.gasAvailable output) :=
  X_step_revert_of_raw_checks hDecode
    (XStepRawChecksPass.of_step_checks hChecks) hStep hHalt hRevert

theorem X_step_fallthrough_stop_success_of_raw_checks {fuel : Nat}
    {validJumps : Array Word} {state post : EVMState}
    {output : ByteArray}
    (hDecodeNone : EvmYul.EVM.decode state.executionEnv.code state.pc = none)
    (hChecks :
      XStepRawChecksPass validJumps state EvmYul.Operation.STOP)
    (hStep :
      EvmYul.EVM.step fuel
        (EvmYul.EVM.C'
          (memoryGasState state EvmYul.Operation.STOP)
          EvmYul.Operation.STOP)
        (some (EvmYul.Operation.STOP, none))
        (memoryGasState state EvmYul.Operation.STOP) = .ok post)
    (hHalt : XHaltOutput? EvmYul.Operation.STOP post = some output) :
    EvmYul.EVM.X fuel.succ validJumps state =
      .ok (EvmYul.EVM.ExecutionResult.success post output) := by
  rw [X_step_expand_default_stop_of_raw_checks hDecodeNone hChecks, hStep]
  have hHalt' :
      XStepHaltOutput? EvmYul.Operation.STOP post = some output := by
    simpa [XHaltOutput?_eq_XStepHaltOutput?] using hHalt
  dsimp
  change
    (match XStepHaltOutput? EvmYul.Operation.STOP post with
    | none => EvmYul.EVM.X fuel validJumps post
    | some output =>
        .ok (EvmYul.EVM.ExecutionResult.success post output)) =
      .ok (EvmYul.EVM.ExecutionResult.success post output)
  rw [hHalt']

theorem X_step_fallthrough_stop_success_of_checks {fuel : Nat}
    {validJumps : Array Word} {state post : EVMState}
    {output : ByteArray}
    (hDecodeNone : EvmYul.EVM.decode state.executionEnv.code state.pc = none)
    (hChecks :
      XStepChecksPass validJumps state EvmYul.Operation.STOP)
    (hStep :
      EvmYul.EVM.step fuel
        (EvmYul.EVM.C'
          (memoryGasState state EvmYul.Operation.STOP)
          EvmYul.Operation.STOP)
        (some (EvmYul.Operation.STOP, none))
        (memoryGasState state EvmYul.Operation.STOP) = .ok post)
    (hHalt : XHaltOutput? EvmYul.Operation.STOP post = some output) :
    EvmYul.EVM.X fuel.succ validJumps state =
      .ok (EvmYul.EVM.ExecutionResult.success post output) :=
  X_step_fallthrough_stop_success_of_raw_checks hDecodeNone
    (XStepRawChecksPass.of_step_checks hChecks) hStep hHalt

inductive XStepTrace (validJumps : Array Word) :
    Nat → EVMState → EvmYul.EVM.ExecutionResult EVMState → Prop where
  | success {fuel : Nat} {state post : EVMState} {op : EVMOp}
      {arg : Option (Word × Nat)} {output : ByteArray}
      (hDecode :
        EvmYul.EVM.decode state.executionEnv.code state.pc = some (op, arg))
      (hChecks : XStepChecksPass validJumps state op)
      (hStep :
        EvmYul.EVM.step fuel (EvmYul.EVM.C' (memoryGasState state op) op)
          (some (op, arg)) (memoryGasState state op) = .ok post)
      (hHalt : XHaltOutput? op post = some output)
      (hNotRevert : op ≠ EvmYul.Operation.REVERT) :
      XStepTrace validJumps fuel.succ state
        (EvmYul.EVM.ExecutionResult.success post output)
  | revert {fuel : Nat} {state post : EVMState} {op : EVMOp}
      {arg : Option (Word × Nat)} {output : ByteArray}
      (hDecode :
        EvmYul.EVM.decode state.executionEnv.code state.pc = some (op, arg))
      (hChecks : XStepChecksPass validJumps state op)
      (hStep :
        EvmYul.EVM.step fuel (EvmYul.EVM.C' (memoryGasState state op) op)
          (some (op, arg)) (memoryGasState state op) = .ok post)
      (hHalt : XHaltOutput? op post = some output)
      (hRevert : op = EvmYul.Operation.REVERT) :
      XStepTrace validJumps fuel.succ state
        (EvmYul.EVM.ExecutionResult.revert post.gasAvailable output)
  | running {fuel : Nat} {state post : EVMState} {op : EVMOp}
      {arg : Option (Word × Nat)}
      {result : EvmYul.EVM.ExecutionResult EVMState}
      (hDecode :
        EvmYul.EVM.decode state.executionEnv.code state.pc = some (op, arg))
      (hChecks : XStepChecksPass validJumps state op)
      (hStep :
        EvmYul.EVM.step fuel (EvmYul.EVM.C' (memoryGasState state op) op)
          (some (op, arg)) (memoryGasState state op) = .ok post)
      (hNoHalt : XHaltOutput? op post = none)
      (hRest : XStepTrace validJumps fuel post result) :
      XStepTrace validJumps fuel.succ state result
  | fallthroughStop {fuel : Nat} {state post : EVMState}
      {output : ByteArray}
      (hDecodeNone :
        EvmYul.EVM.decode state.executionEnv.code state.pc = none)
      (hChecks : XStepChecksPass validJumps state EvmYul.Operation.STOP)
      (hStep :
        EvmYul.EVM.step fuel
          (EvmYul.EVM.C'
            (memoryGasState state EvmYul.Operation.STOP)
            EvmYul.Operation.STOP)
          (some (EvmYul.Operation.STOP, none))
          (memoryGasState state EvmYul.Operation.STOP) = .ok post)
      (hHalt : XHaltOutput? EvmYul.Operation.STOP post = some output) :
      XStepTrace validJumps fuel.succ state
        (EvmYul.EVM.ExecutionResult.success post output)

namespace XStepTrace

theorem run {validJumps : Array Word} {fuel : Nat} {state : EVMState}
    {result : EvmYul.EVM.ExecutionResult EVMState}
    (hTrace : XStepTrace validJumps fuel state result) :
    EvmYul.EVM.X fuel validJumps state = .ok result := by
  induction hTrace with
  | success hDecode hChecks hStep hHalt hNotRevert =>
      exact X_step_success_of_checks hDecode hChecks hStep hHalt hNotRevert
  | revert hDecode hChecks hStep hHalt hRevert =>
      exact X_step_revert_of_checks hDecode hChecks hStep hHalt hRevert
  | running hDecode hChecks hStep hNoHalt _ ih =>
      rw [X_step_running_of_checks hDecode hChecks hStep hNoHalt]
      exact ih
  | fallthroughStop hDecodeNone hChecks hStep hHalt =>
      exact X_step_fallthrough_stop_success_of_checks
        hDecodeNone hChecks hStep hHalt

inductive XPrefixTrace (validJumps : Array Word) :
    Nat → EVMState → EVMState → Prop where
  | done (state : EVMState) :
      XPrefixTrace validJumps 0 state state
  | running {fuel : Nat} {state post final : EVMState} {op : EVMOp}
      {arg : Option (Word × Nat)}
      (hDecode :
        EvmYul.EVM.decode state.executionEnv.code state.pc = some (op, arg))
      (hChecks : XStepChecksPass validJumps state op)
      (hStep :
        ∀ tailFuel : Nat,
          EvmYul.EVM.step tailFuel.succ
            (EvmYul.EVM.C' (memoryGasState state op) op)
            (some (op, arg)) (memoryGasState state op) = .ok post)
      (hNoHalt : XHaltOutput? op post = none)
      (hRest : XPrefixTrace validJumps fuel post final) :
      XPrefixTrace validJumps fuel.succ state final

theorem XPrefixTrace.then_stepTrace {validJumps : Array Word}
    {prefixFuel restFuel : Nat} {state mid : EVMState}
    {result : EvmYul.EVM.ExecutionResult EVMState}
    (hPrefix : XPrefixTrace validJumps prefixFuel state mid)
    (hRest : XStepTrace validJumps restFuel.succ mid result) :
    ∃ fuel : Nat,
      XStepTrace validJumps fuel.succ state result := by
  induction hPrefix generalizing restFuel result with
  | done state =>
      exact ⟨restFuel, hRest⟩
  | running hDecode hChecks hStep hNoHalt _ ih =>
      obtain ⟨fuel, hTrace⟩ := ih hRest
      exact
        ⟨fuel.succ,
          XStepTrace.running hDecode hChecks (hStep fuel) hNoHalt
            hTrace⟩

theorem targetInstr_running
    {validJumps : Array Word} {fuel : Nat}
    {instr : TargetInstr}
    {full fullPost target targetPost : EVMState}
    {result : EvmYul.EVM.ExecutionResult EVMState}
    (hNoCallCreate : targetInstrUsesCallCreate instr = false)
    (hRel : GasExecRel full target)
    (hDecode :
      EvmYul.EVM.decode full.executionEnv.code full.pc =
        some (instr.op, instr.arg))
    (hChecks : XStepChecksPass validJumps full instr.op)
    (hTarget :
      Target.stepInstrResult instr target = .ok (.running targetPost))
    (hStep :
      EvmYul.EVM.step fuel
        (EvmYul.EVM.C' (memoryGasState full instr.op) instr.op)
        (some (instr.op, instr.arg)) (memoryGasState full instr.op) =
          .ok fullPost)
    (hNoHalt : XHaltOutput? instr.op fullPost = none)
    (hRest : XStepTrace validJumps fuel fullPost result) :
    GasExecRel fullPost targetPost ∧
      XStepTrace validJumps fuel.succ full result := by
  obtain ⟨hTargetStep, hKind⟩ :=
    Target.stepInstrResult_running_stepInstr hTarget
  have hRelPost :
      GasExecRel fullPost targetPost :=
    EVM_step_targetInstr_preserves_gasExecRel_of_ok
      (fuel := fuel)
      (gasCost := EvmYul.EVM.C' (memoryGasState full instr.op) instr.op)
      hNoCallCreate (hRel.memoryGasState_left (op := instr.op))
      hTargetStep hStep
  exact
    ⟨hRelPost,
      XStepTrace.running hDecode hChecks hStep hNoHalt hRest⟩

theorem targetInstr_success
    {validJumps : Array Word} {fuel : Nat}
    {instr : TargetInstr}
    {full fullPost target : EVMState} {halt : Halt}
    {output : ByteArray}
    (hNoCallCreate : targetInstrUsesCallCreate instr = false)
    (hRel : GasExecRel full target)
    (hDecode :
      EvmYul.EVM.decode full.executionEnv.code full.pc =
        some (instr.op, instr.arg))
    (hChecks : XStepChecksPass validJumps full instr.op)
    (hTarget :
      Target.stepInstrResult instr target = .ok (.halted halt))
    (hStep :
      EvmYul.EVM.step fuel
        (EvmYul.EVM.C' (memoryGasState full instr.op) instr.op)
        (some (instr.op, instr.arg)) (memoryGasState full instr.op) =
          .ok fullPost)
    (hHalt : XHaltOutput? instr.op fullPost = some output)
    (hNotRevert : instr.op ≠ EvmYul.Operation.REVERT) :
    GasExecRel fullPost halt.state ∧
      XStepTrace validJumps fuel.succ full
        (.success fullPost output) := by
  obtain ⟨hTargetStep, _hKind, _hOutputKind⟩ :=
    Target.stepInstrResult_halted_stepInstr hTarget
  have hRelPost :
      GasExecRel fullPost halt.state :=
    EVM_step_targetInstr_preserves_gasExecRel_of_ok
      (fuel := fuel)
      (gasCost := EvmYul.EVM.C' (memoryGasState full instr.op) instr.op)
      hNoCallCreate (hRel.memoryGasState_left (op := instr.op))
      hTargetStep hStep
  exact
    ⟨hRelPost,
      XStepTrace.success hDecode hChecks hStep hHalt hNotRevert⟩

theorem targetInstr_revert
    {validJumps : Array Word} {fuel : Nat}
    {instr : TargetInstr}
    {full fullPost target : EVMState} {halt : Halt}
    {output : ByteArray}
    (hNoCallCreate : targetInstrUsesCallCreate instr = false)
    (hRel : GasExecRel full target)
    (hDecode :
      EvmYul.EVM.decode full.executionEnv.code full.pc =
        some (instr.op, instr.arg))
    (hChecks : XStepChecksPass validJumps full instr.op)
    (hTarget :
      Target.stepInstrResult instr target = .ok (.halted halt))
    (hStep :
      EvmYul.EVM.step fuel
        (EvmYul.EVM.C' (memoryGasState full instr.op) instr.op)
        (some (instr.op, instr.arg)) (memoryGasState full instr.op) =
          .ok fullPost)
    (hHalt : XHaltOutput? instr.op fullPost = some output)
    (hRevert : instr.op = EvmYul.Operation.REVERT) :
    GasExecRel fullPost halt.state ∧
      XStepTrace validJumps fuel.succ full
        (.revert fullPost.gasAvailable output) := by
  obtain ⟨hTargetStep, _hKind, _hOutputKind⟩ :=
    Target.stepInstrResult_halted_stepInstr hTarget
  have hRelPost :
      GasExecRel fullPost halt.state :=
    EVM_step_targetInstr_preserves_gasExecRel_of_ok
      (fuel := fuel)
      (gasCost := EvmYul.EVM.C' (memoryGasState full instr.op) instr.op)
      hNoCallCreate (hRel.memoryGasState_left (op := instr.op))
      hTargetStep hStep
  exact
    ⟨hRelPost,
      XStepTrace.revert hDecode hChecks hStep hHalt hRevert⟩

theorem targetInstr_running_exists
    {validJumps : Array Word} {fuel : Nat}
    {instr : TargetInstr}
    {full target targetPost : EVMState}
    {result : EvmYul.EVM.ExecutionResult EVMState}
    (hNoCallCreate : targetInstrUsesCallCreate instr = false)
    (hRel : GasExecRel full target)
    (hDecode :
      EvmYul.EVM.decode full.executionEnv.code full.pc =
        some (instr.op, instr.arg))
    (hChecks : XStepChecksPass validJumps full instr.op)
    (hTarget :
      Target.stepInstrResult instr target = .ok (.running targetPost))
    (hRest :
      ∀ fullPost,
        GasExecRel fullPost targetPost →
          XStepTrace validJumps fuel.succ fullPost result) :
    ∃ fullPost,
      GasExecRel fullPost targetPost ∧
        XStepTrace validJumps fuel.succ.succ full result := by
  obtain ⟨hTargetStep, hKind⟩ :=
    Target.stepInstrResult_running_stepInstr hTarget
  obtain ⟨fullPost, hStep, hRelPost⟩ :=
    EVM_step_targetInstr_exists_gasExecRel
      (fuel := fuel)
      (gasCost := EvmYul.EVM.C' (memoryGasState full instr.op) instr.op)
      hNoCallCreate (hRel.memoryGasState_left (op := instr.op))
      hTargetStep
  have hNoHalt : XHaltOutput? instr.op fullPost = none :=
    XHaltOutput?_none_of_targetInstr_haltKind_none hKind
  exact
    ⟨fullPost, hRelPost,
      XStepTrace.running hDecode hChecks hStep hNoHalt
        (hRest fullPost hRelPost)⟩

theorem targetInstr_success_exists
    {validJumps : Array Word} {fuel : Nat}
    {instr : TargetInstr}
    {full target : EVMState} {halt : Halt}
    (hNoCallCreate : targetInstrUsesCallCreate instr = false)
    (hRel : GasExecRel full target)
    (hDecode :
      EvmYul.EVM.decode full.executionEnv.code full.pc =
        some (instr.op, instr.arg))
    (hChecks : XStepChecksPass validJumps full instr.op)
    (hTarget :
      Target.stepInstrResult instr target = .ok (.halted halt))
    (hNotRevert : halt.kind ≠ .revert) :
    ∃ fullPost,
      GasExecRel fullPost halt.state ∧
        XStepTrace validJumps fuel.succ.succ full
          (.success fullPost halt.output) := by
  obtain ⟨hTargetStep, hKind, hOutput⟩ :=
    Target.stepInstrResult_halted_stepInstr hTarget
  obtain ⟨fullPost, hStep, hRelPost⟩ :=
    EVM_step_targetInstr_exists_gasExecRel
      (fuel := fuel)
      (gasCost := EvmYul.EVM.C' (memoryGasState full instr.op) instr.op)
      hNoCallCreate (hRel.memoryGasState_left (op := instr.op))
      hTargetStep
  have hHalt : XHaltOutput? instr.op fullPost = some halt.output := by
    have hHaltFull :=
      XHaltOutput?_some_of_targetInstr_haltKind_some
        (instr := instr) (state := fullPost) hKind
    rw [HaltKind.output_eq_of_gasExecRel halt.kind hRelPost, ← hOutput] at hHaltFull
    exact hHaltFull
  have hNotRevertOp : instr.op ≠ EvmYul.Operation.REVERT :=
    targetInstr_op_ne_revert_of_haltKind_some_ne hKind hNotRevert
  exact
    ⟨fullPost, hRelPost,
      XStepTrace.success hDecode hChecks hStep hHalt hNotRevertOp⟩

theorem targetInstr_revert_exists
    {validJumps : Array Word} {fuel : Nat}
    {instr : TargetInstr}
    {full target : EVMState} {halt : Halt}
    (hNoCallCreate : targetInstrUsesCallCreate instr = false)
    (hRel : GasExecRel full target)
    (hDecode :
      EvmYul.EVM.decode full.executionEnv.code full.pc =
        some (instr.op, instr.arg))
    (hChecks : XStepChecksPass validJumps full instr.op)
    (hTarget :
      Target.stepInstrResult instr target = .ok (.halted halt))
    (hRevert : halt.kind = .revert) :
    ∃ fullPost,
      GasExecRel fullPost halt.state ∧
        XStepTrace validJumps fuel.succ.succ full
          (.revert fullPost.gasAvailable halt.output) := by
  obtain ⟨hTargetStep, hKind, hOutput⟩ :=
    Target.stepInstrResult_halted_stepInstr hTarget
  obtain ⟨fullPost, hStep, hRelPost⟩ :=
    EVM_step_targetInstr_exists_gasExecRel
      (fuel := fuel)
      (gasCost := EvmYul.EVM.C' (memoryGasState full instr.op) instr.op)
      hNoCallCreate (hRel.memoryGasState_left (op := instr.op))
      hTargetStep
  have hHalt : XHaltOutput? instr.op fullPost = some halt.output := by
    have hHaltFull :=
      XHaltOutput?_some_of_targetInstr_haltKind_some
        (instr := instr) (state := fullPost) hKind
    rw [HaltKind.output_eq_of_gasExecRel halt.kind hRelPost, ← hOutput] at hHaltFull
    exact hHaltFull
  have hRevertOp : instr.op = EvmYul.Operation.REVERT := by
    exact targetInstr_op_eq_revert_of_haltKind_revert (by simpa [hRevert] using hKind)
  exact
    ⟨fullPost, hRelPost,
      XStepTrace.revert hDecode hChecks hStep hHalt hRevertOp⟩

end XStepTrace

/--
Successful `X` results preserve the same non-gas final state as the gasless
source run.  Revert needs a separate output/projection theorem because
EVMYulLean's `ExecutionResult.revert` does not carry the final `EVM.State`.
-/
def XSuccessErasesTo (sourceFinal : EVMState) :
    EvmYul.EVM.ExecutionResult EVMState → Prop
  | .success evmFinal _output => eraseGas evmFinal = eraseGas sourceFinal
  | .revert _gas _output => False

def XRunsSuccessfullyAbove (target : TargetProgram) (initial sourceFinal : EVMState)
    (evmFuel gasBound : Nat) : Prop :=
  ∀ gas,
    gasBound ≤ gas →
      gas < EvmYul.UInt256.size →
        ∃ result,
          EvmYul.EVM.X evmFuel (validJumps target)
              (installCodeAndGas target gas initial) =
            .ok result ∧
            XSuccessErasesTo sourceFinal result

/--
Result-level agreement for the gas-aware `X` runner.

The running case compares gas-erased states and requires the eventual EVM
success output to be empty, matching ordinary non-terminal completion as seen by
message-call return data. Terminal success compares both the gas-erased halted
state and output. Revert in EVMYulLean does not carry the final state, so the
result-level contract compares the revert output and halt kind only.
-/
def XResultAgrees (targetResult : StepResult) :
    EvmYul.EVM.ExecutionResult EVMState → Prop
  | .success evmFinal output =>
      match targetResult with
      | .running state =>
          eraseGas evmFinal = eraseGas state ∧ output = ByteArray.empty
      | .halted halt =>
          halt.kind ≠ .revert ∧
            eraseGas evmFinal = eraseGas halt.state ∧
              output = halt.output
  | .revert _gas output =>
      match targetResult with
      | .running _ => False
      | .halted halt => halt.kind = .revert ∧ output = halt.output

theorem XResultAgrees_running_success_of_gasExecRel
    {full target : EVMState}
    (hRel : GasExecRel full target) :
    XResultAgrees (.running target)
      (.success full ByteArray.empty) := by
  exact ⟨hRel.eraseGas_eq, rfl⟩

theorem XResultAgrees_halted_success_of_gasExecRel
    {full : EVMState} {halt : Halt} {output : ByteArray}
    (hKind : halt.kind ≠ .revert)
    (hRel : GasExecRel full halt.state)
    (hOutput : output = halt.output) :
    XResultAgrees (.halted halt) (.success full output) := by
  exact ⟨hKind, hRel.eraseGas_eq, hOutput⟩

theorem XResultAgrees_halted_revert
    {halt : Halt} {gas : Word} {output : ByteArray}
    (hKind : halt.kind = .revert)
    (hOutput : output = halt.output) :
    XResultAgrees (.halted halt) (.revert gas output) := by
  exact ⟨hKind, hOutput⟩

namespace XStepTrace

theorem targetInstr_running_exists_agrees
    {validJumps : Array Word} {fuel : Nat}
    {instr : TargetInstr}
    {full target targetPost : EVMState}
    {result : EvmYul.EVM.ExecutionResult EVMState}
    {targetResult : StepResult}
    (hNoCallCreate : targetInstrUsesCallCreate instr = false)
    (hRel : GasExecRel full target)
    (hDecode :
      EvmYul.EVM.decode full.executionEnv.code full.pc =
        some (instr.op, instr.arg))
    (hChecks : XStepChecksPass validJumps full instr.op)
    (hTarget :
      Target.stepInstrResult instr target = .ok (.running targetPost))
    (hRest :
      ∀ fullPost,
        GasExecRel fullPost targetPost →
          XStepTrace validJumps fuel.succ fullPost result)
    (hAgree :
      ∀ fullPost,
        GasExecRel fullPost targetPost →
          XResultAgrees targetResult result) :
    ∃ fullPost,
      GasExecRel fullPost targetPost ∧
        XStepTrace validJumps fuel.succ.succ full result ∧
          XResultAgrees targetResult result := by
  obtain ⟨fullPost, hRelPost, hTrace⟩ :=
    targetInstr_running_exists
      (fuel := fuel)
      (instr := instr)
      (full := full)
      (target := target)
      (targetPost := targetPost)
      (result := result)
      hNoCallCreate hRel hDecode hChecks hTarget hRest
  exact ⟨fullPost, hRelPost, hTrace, hAgree fullPost hRelPost⟩

theorem targetInstr_success_exists_agrees
    {validJumps : Array Word} {fuel : Nat}
    {instr : TargetInstr}
    {full target : EVMState} {halt : Halt}
    (hNoCallCreate : targetInstrUsesCallCreate instr = false)
    (hRel : GasExecRel full target)
    (hDecode :
      EvmYul.EVM.decode full.executionEnv.code full.pc =
        some (instr.op, instr.arg))
    (hChecks : XStepChecksPass validJumps full instr.op)
    (hTarget :
      Target.stepInstrResult instr target = .ok (.halted halt))
    (hNotRevert : halt.kind ≠ .revert) :
    ∃ fullPost,
      GasExecRel fullPost halt.state ∧
        XStepTrace validJumps fuel.succ.succ full
          (.success fullPost halt.output) ∧
          XResultAgrees (.halted halt) (.success fullPost halt.output) := by
  obtain ⟨fullPost, hRelPost, hTrace⟩ :=
    targetInstr_success_exists
      (fuel := fuel)
      (instr := instr)
      (full := full)
      (target := target)
      (halt := halt)
      hNoCallCreate hRel hDecode hChecks hTarget hNotRevert
  exact
    ⟨fullPost, hRelPost, hTrace,
      XResultAgrees_halted_success_of_gasExecRel
        hNotRevert hRelPost rfl⟩

theorem targetInstr_revert_exists_agrees
    {validJumps : Array Word} {fuel : Nat}
    {instr : TargetInstr}
    {full target : EVMState} {halt : Halt}
    (hNoCallCreate : targetInstrUsesCallCreate instr = false)
    (hRel : GasExecRel full target)
    (hDecode :
      EvmYul.EVM.decode full.executionEnv.code full.pc =
        some (instr.op, instr.arg))
    (hChecks : XStepChecksPass validJumps full instr.op)
    (hTarget :
      Target.stepInstrResult instr target = .ok (.halted halt))
    (hRevert : halt.kind = .revert) :
    ∃ fullPost,
      GasExecRel fullPost halt.state ∧
        XStepTrace validJumps fuel.succ.succ full
          (.revert fullPost.gasAvailable halt.output) ∧
          XResultAgrees (.halted halt)
            (.revert fullPost.gasAvailable halt.output) := by
  obtain ⟨fullPost, hRelPost, hTrace⟩ :=
    targetInstr_revert_exists
      (fuel := fuel)
      (instr := instr)
      (full := full)
      (target := target)
      (halt := halt)
      hNoCallCreate hRel hDecode hChecks hTarget hRevert
  exact
    ⟨fullPost, hRelPost, hTrace,
      XResultAgrees_halted_revert hRevert rfl⟩

theorem runListResult_cons_exists_agrees
    {validJumps : Array Word}
    {instr : TargetInstr} {rest : List TargetInstr}
    {full target : EVMState} {targetResult : StepResult}
    (hRun :
      Target.runListResult (instr :: rest) target = .ok targetResult)
    (hNoCallCreate : targetInstrUsesCallCreate instr = false)
    (hRel : GasExecRel full target)
    (hDecode :
      EvmYul.EVM.decode full.executionEnv.code full.pc =
        some (instr.op, instr.arg))
    (hChecks : XStepChecksPass validJumps full instr.op)
    (hContinue :
      ∀ targetPost,
        Target.stepInstrResult instr target = .ok (.running targetPost) →
          Target.runListResult rest targetPost = .ok targetResult →
            ∃ fuel : Nat,
              ∀ fullPost,
                GasExecRel fullPost targetPost →
                  ∃ evmResult,
                    XStepTrace validJumps fuel.succ fullPost evmResult ∧
                      XResultAgrees targetResult evmResult) :
    ∃ fuel : Nat, ∃ evmResult,
      XStepTrace validJumps fuel.succ full evmResult ∧
        XResultAgrees targetResult evmResult := by
  rcases Target.runListResult_cons_ok_cases hRun with
    ⟨targetPost, hStepResult, hRunRest⟩ | ⟨halt, hStepResult, hResult⟩
  · obtain ⟨hTargetStep, hKind⟩ :=
      Target.stepInstrResult_running_stepInstr hStepResult
    obtain ⟨fuelRest, hContinueAtFuel⟩ :=
      hContinue targetPost hStepResult hRunRest
    obtain ⟨fullPost, hStep, hRelPost⟩ :=
      EVM_step_targetInstr_exists_gasExecRel
        (fuel := fuelRest)
        (gasCost := EvmYul.EVM.C' (memoryGasState full instr.op) instr.op)
        hNoCallCreate (hRel.memoryGasState_left (op := instr.op))
        hTargetStep
    obtain ⟨evmResult, hRestTrace, hAgree⟩ :=
      hContinueAtFuel fullPost hRelPost
    have hNoHalt : XHaltOutput? instr.op fullPost = none :=
      XHaltOutput?_none_of_targetInstr_haltKind_none hKind
    exact
      ⟨fuelRest.succ, evmResult,
        XStepTrace.running hDecode hChecks hStep hNoHalt hRestTrace,
        hAgree⟩
  · subst targetResult
    by_cases hRevert : halt.kind = .revert
    · obtain ⟨fullPost, _hRelPost, hTrace, hAgree⟩ :=
        targetInstr_revert_exists_agrees
          (fuel := 0)
          (instr := instr)
          (full := full)
          (target := target)
          (halt := halt)
          hNoCallCreate hRel hDecode hChecks hStepResult hRevert
      exact ⟨1, .revert fullPost.gasAvailable halt.output, hTrace, hAgree⟩
    · obtain ⟨fullPost, _hRelPost, hTrace, hAgree⟩ :=
        targetInstr_success_exists_agrees
          (fuel := 0)
          (instr := instr)
          (full := full)
          (target := target)
          (halt := halt)
          hNoCallCreate hRel hDecode hChecks hStepResult hRevert
      exact ⟨1, .success fullPost halt.output, hTrace, hAgree⟩

def XRunListSuffixReady (validJumps : Array Word)
    (code : List TargetInstr) : Prop :=
  ∀ {instr : TargetInstr} {rest : List TargetInstr}
      {targetState : EVMState} {blockResult : StepResult},
    (∃ pre : List TargetInstr, code = pre ++ (instr :: rest)) →
      Target.runListResult (instr :: rest) targetState = .ok blockResult →
        ∀ {fullState : EVMState},
          GasExecRel fullState targetState →
            EvmYul.EVM.decode fullState.executionEnv.code fullState.pc =
                some (instr.op, instr.arg) ∧
              XNonGasChecksPass validJumps fullState instr.op ∧
                XGasRequiredAt fullState instr.op ≤
                  fullState.gasAvailable.toNat ∧
                  targetInstrUsesCallCreate instr = false

def XRunListSuffixNonGasReady (validJumps : Array Word)
    (code : List TargetInstr) : Prop :=
  ∀ {instr : TargetInstr} {rest : List TargetInstr}
      {targetState : EVMState} {blockResult : StepResult},
    (∃ pre : List TargetInstr, code = pre ++ (instr :: rest)) →
      Target.runListResult (instr :: rest) targetState = .ok blockResult →
        ∀ {fullState : EVMState},
          GasExecRel fullState targetState →
            EvmYul.EVM.decode fullState.executionEnv.code fullState.pc =
                some (instr.op, instr.arg) ∧
              XNonGasChecksPass validJumps fullState instr.op ∧
                targetInstrUsesCallCreate instr = false

def XRunListSuffixGasReady (code : List TargetInstr) : Prop :=
  ∀ {instr : TargetInstr} {rest : List TargetInstr}
      {targetState : EVMState} {blockResult : StepResult},
    (∃ pre : List TargetInstr, code = pre ++ (instr :: rest)) →
      Target.runListResult (instr :: rest) targetState = .ok blockResult →
        ∀ {fullState : EVMState},
          GasExecRel fullState targetState →
            XGasRequiredAt fullState instr.op ≤
              fullState.gasAvailable.toNat

def TargetInstrBodyPreservesGas (instr : TargetInstr) : Prop :=
  ∀ {state post : EVMState},
    EvmYul.step instr.op instr.arg state = .ok post →
      post.gasAvailable = state.gasAvailable

theorem TargetInstrBodyPreservesGas.of_no_call_create
    {instr : TargetInstr}
    (hNoCallCreate : targetInstrUsesCallCreate instr = false) :
    TargetInstrBodyPreservesGas instr := by
  intro state post hRun
  cases instr with
  | push32 value =>
      change
        Except.ok (EvmYul.EVM.State.replaceStackAndIncrPC state
          (state.stack.push value) (pcΔ := 33)) = .ok post at hRun
      cases hRun
      simp [EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]
  | jump =>
      simp only [TargetInstr.op, TargetInstr.arg] at hRun
      cases hPop : state.stack.pop with
      | none =>
          cases state with
          | mk shared pc stack execLength =>
              cases stack with
              | nil =>
                  change
                    (Except.error EvmYul.EVM.ExecutionException.StackUnderflow :
                      Except EvmYul.EVM.ExecutionException EVMState) =
                      .ok post at hRun
                  cases hRun
              | cons hd tl =>
                  simp [EvmYul.Stack.pop] at hPop
      | some popped =>
          rcases popped with ⟨stack, dest⟩
          have hStack : state.stack = dest :: stack :=
            stack_eq_cons_of_pop hPop
          rw [EvmYul_step_jump_of_stack state stack dest hStack] at hRun
          cases hRun
          rfl
  | jumpi =>
      simp only [TargetInstr.op, TargetInstr.arg] at hRun
      cases hPop : state.stack.pop2 with
      | none =>
          cases state with
          | mk shared pc stack execLength =>
              cases stack with
              | nil =>
                  change
                    (Except.error EvmYul.EVM.ExecutionException.StackUnderflow :
                      Except EvmYul.EVM.ExecutionException EVMState) =
                      .ok post at hRun
                  cases hRun
              | cons first rest =>
                  cases rest with
                  | nil =>
                      change
                        (Except.error
                            EvmYul.EVM.ExecutionException.StackUnderflow :
                          Except EvmYul.EVM.ExecutionException EVMState) =
                          .ok post at hRun
                      cases hRun
                  | cons second rest =>
                      simp [EvmYul.Stack.pop2] at hPop
      | some popped =>
          rcases popped with ⟨stack, dest, cond⟩
          have hStack : state.stack = dest :: cond :: stack :=
            stack_eq_cons_cons_of_pop2 hPop
          rw [EvmYul_step_jumpi_of_stack state stack dest cond hStack]
            at hRun
          cases hRun
          rfl
  | jumpdest =>
      simp only [TargetInstr.op, TargetInstr.arg] at hRun
      rw [EvmYul_step_jumpdest_eq state] at hRun
      cases hRun
      simp [EvmYul.EVM.State.incrPC]
  | prim op =>
      change EvmYul.step op.toEVM none state = .ok post at hRun
      cases hStep : op.continuingStep? with
      | none =>
          exact EvmYul_step_noncontinuing_prim_gasAvailable_eq hStep
            (by simpa [targetInstrUsesCallCreate] using hNoCallCreate) hRun
      | some step =>
          exact EvmYul_step_continuing_prim_gasAvailable_eq hStep hRun

def XRunListBodyPreservesGas : List TargetInstr → Prop
  | [] => True
  | instr :: rest =>
      TargetInstrBodyPreservesGas instr ∧
        XRunListBodyPreservesGas rest

theorem XRunListBodyPreservesGas.of_all_no_call_create :
    ∀ {code : List TargetInstr},
      (∀ instr ∈ code, targetInstrUsesCallCreate instr = false) →
      XRunListBodyPreservesGas code := by
  intro code
  induction code with
  | nil =>
      intro _hAll
      trivial
  | cons instr rest ih =>
      intro hAll
      exact
        ⟨TargetInstrBodyPreservesGas.of_no_call_create
            (hAll instr (by simp)),
          ih (by
            intro instr' hMem
            exact hAll instr' (by simp [hMem]))⟩

def XRunListGasBudget : List TargetInstr → EVMState → Nat
  | [], _target => 0
  | instr :: rest, target =>
      XGasRequiredAt target instr.op +
        match Target.stepInstrResult instr target with
        | .ok (.running targetPost) =>
            XRunListGasBudget rest targetPost
        | .ok (.halted _halt) | .error _ =>
            0

theorem XRunListSuffixReady.of_parts {validJumps : Array Word}
    {code : List TargetInstr}
    (hNonGas : XRunListSuffixNonGasReady validJumps code)
    (hGas : XRunListSuffixGasReady code) :
    XRunListSuffixReady validJumps code := by
  intro instr rest targetState blockResult hSuffix hRun fullState hRel
  obtain ⟨hDecode, hChecks, hNoCallCreate⟩ :=
    hNonGas hSuffix hRun hRel
  exact ⟨hDecode, hChecks, hGas hSuffix hRun hRel, hNoCallCreate⟩

theorem XRunListSuffixReady.nonGas {validJumps : Array Word}
    {code : List TargetInstr}
    (hReady : XRunListSuffixReady validJumps code) :
    XRunListSuffixNonGasReady validJumps code := by
  intro instr rest targetState blockResult hSuffix hRun fullState hRel
  obtain ⟨hDecode, hChecks, _hGas, hNoCallCreate⟩ :=
    hReady hSuffix hRun hRel
  exact ⟨hDecode, hChecks, hNoCallCreate⟩

theorem XRunListSuffixReady.gas {validJumps : Array Word}
    {code : List TargetInstr}
    (hReady : XRunListSuffixReady validJumps code) :
    XRunListSuffixGasReady code := by
  intro instr rest targetState blockResult hSuffix hRun fullState hRel
  exact (hReady hSuffix hRun hRel).2.2.1

def XRunListPathReady (validJumps : Array Word) :
    List TargetInstr → EVMState → EVMState → StepResult → Prop
  | [], target, full, result =>
      result = .running target ∧ GasExecRel full target
  | instr :: rest, target, full, result =>
      GasExecRel full target ∧
        EvmYul.EVM.decode full.executionEnv.code full.pc =
          some (instr.op, instr.arg) ∧
        XNonGasChecksPass validJumps full instr.op ∧
        XGasRequiredAt full instr.op ≤ full.gasAvailable.toNat ∧
        targetInstrUsesCallCreate instr = false ∧
        match Target.stepInstrResult instr target with
        | .ok (.running targetPost) =>
            ∀ {stepFuel : Nat} {fullPost : EVMState},
              EvmYul.EVM.step stepFuel.succ
                  (EvmYul.EVM.C' (memoryGasState full instr.op) instr.op)
                  (some (instr.op, instr.arg))
                  (memoryGasState full instr.op) =
                .ok fullPost →
              XRunListPathReady validJumps rest targetPost fullPost result
        | .ok (.halted halt) =>
            result = .halted halt
        | .error _ =>
            False

theorem XRunListPathReady.of_suffix_ready {validJumps : Array Word} :
    ∀ {code : List TargetInstr} {target full : EVMState}
      {targetResult : StepResult},
      Target.runListResult code target = .ok targetResult →
      XRunListSuffixReady validJumps code →
      GasExecRel full target →
      XRunListPathReady validJumps code target full targetResult := by
  intro code
  induction code with
  | nil =>
      intro target full targetResult hRun _hReady hRel
      simp [Target.runListResult] at hRun
      subst targetResult
      exact ⟨rfl, hRel⟩
  | cons instr rest ih =>
      intro target full targetResult hRun hReady hRel
      obtain ⟨hDecode, hNonGas, hGas, hNoCallCreate⟩ :=
        hReady
          (instr := instr) (rest := rest)
          (targetState := target) (blockResult := targetResult)
          ⟨[], by simp⟩ hRun hRel
      simp [XRunListPathReady, hRel, hDecode, hNonGas, hGas,
        hNoCallCreate]
      cases hStepResult : Target.stepInstrResult instr target with
      | error err =>
          simp [Target.runListResult, hStepResult] at hRun
          change
            (Except.error err : Except EVMException StepResult) =
              .ok targetResult at hRun
          cases hRun
      | ok stepResult =>
          cases stepResult with
          | halted halt =>
              simp [Target.runListResult, hStepResult] at hRun
              change
                (Except.ok (StepResult.halted halt) :
                    Except EVMException StepResult) =
                  .ok targetResult at hRun
              cases hRun
              rfl
          | running targetPost =>
              simp [Target.runListResult, hStepResult] at hRun
              intro stepFuel fullPost hStep
              have hRelPost :
                  GasExecRel fullPost targetPost :=
                EVM_step_targetInstr_preserves_gasExecRel_of_ok
                  (fuel := stepFuel.succ)
                  (gasCost :=
                    EvmYul.EVM.C' (memoryGasState full instr.op) instr.op)
                  hNoCallCreate (hRel.memoryGasState_left (op := instr.op))
                  (Target.stepInstrResult_running_stepInstr
                    hStepResult).1 hStep
              have hReadyRest :
                  XRunListSuffixReady validJumps rest := by
                intro instr' rest' targetState blockResult hSuffix hRunSuffix
                intro fullState hRelState
                rcases hSuffix with ⟨pre, hPrefix⟩
                exact
                  hReady
                    (instr := instr') (rest := rest')
                    (targetState := targetState)
                    (blockResult := blockResult)
                    ⟨instr :: pre, by simp [hPrefix]⟩
                    hRunSuffix hRelState
              exact ih hRun hReadyRest hRelPost

theorem XRunListPathReady.of_nonGas_and_budget {validJumps : Array Word} :
    ∀ {code : List TargetInstr} {target full : EVMState}
      {targetResult : StepResult},
      Target.runListResult code target = .ok targetResult →
      XRunListSuffixNonGasReady validJumps code →
      XRunListBodyPreservesGas code →
      XRunListGasBudget code target ≤ full.gasAvailable.toNat →
      GasExecRel full target →
      XRunListPathReady validJumps code target full targetResult := by
  intro code
  induction code with
  | nil =>
      intro target full targetResult hRun _hNonGas _hBody _hBudget hRel
      simp [Target.runListResult] at hRun
      subst targetResult
      exact ⟨rfl, hRel⟩
  | cons instr rest ih =>
      intro target full targetResult hRun hNonGas hBody hBudget hRel
      rcases hBody with ⟨hBodyInstr, hBodyRest⟩
      obtain ⟨hDecode, hNonGasStep, hNoCallCreate⟩ :=
        hNonGas
          (instr := instr) (rest := rest)
          (targetState := target) (blockResult := targetResult)
          ⟨[], by simp⟩ hRun hRel
      have hReqBudget :
          XGasRequiredAt target instr.op ≤
            XRunListGasBudget (instr :: rest) target := by
        simp [XRunListGasBudget]
      have hRequired :
          XGasRequiredAt full instr.op ≤ full.gasAvailable.toNat := by
        rw [XGasRequiredAt_eq_of_gasExecRel_of_targetInstr_no_call_create
          hNoCallCreate hRel]
        exact le_trans hReqBudget hBudget
      simp only [XRunListPathReady]
      refine
        ⟨hRel, hDecode, hNonGasStep, hRequired, hNoCallCreate, ?_⟩
      cases hStepResult : Target.stepInstrResult instr target with
      | error err =>
          simp [Target.runListResult, hStepResult] at hRun
          change
            (Except.error err : Except EVMException StepResult) =
              .ok targetResult at hRun
          cases hRun
      | ok stepResult =>
          cases stepResult with
          | halted halt =>
              simp [Target.runListResult, hStepResult] at hRun
              cases hRun
              rfl
          | running targetPost =>
              simp [Target.runListResult, hStepResult] at hRun
              intro stepFuel fullPost hStep
              obtain ⟨hTargetStep, _hKind⟩ :=
                Target.stepInstrResult_running_stepInstr hStepResult
              have hRelPost :
                  GasExecRel fullPost targetPost :=
                EVM_step_targetInstr_preserves_gasExecRel_of_ok
                  (fuel := stepFuel.succ)
                  (gasCost :=
                    EvmYul.EVM.C' (memoryGasState full instr.op) instr.op)
                  hNoCallCreate (hRel.memoryGasState_left (op := instr.op))
                  hTargetStep hStep
              have hStepBody :
                  EvmYul.step instr.op instr.arg
                      (xBodyState full instr.op) =
                    .ok fullPost := by
                rw [← EVM_step_targetInstr_eq_xBodyState
                  (fuel := stepFuel) (state := full) (instr := instr)
                  hNoCallCreate]
                exact hStep
              have hBudgetStep :
                  XGasRequiredAt full instr.op +
                      XRunListGasBudget rest targetPost ≤
                    full.gasAvailable.toNat := by
                have hBudgetRun :
                    XRunListGasBudget (instr :: rest) target =
                      XGasRequiredAt target instr.op +
                        XRunListGasBudget rest targetPost := by
                  simp [XRunListGasBudget, hStepResult]
                rw [hBudgetRun] at hBudget
                rw [←
                  XGasRequiredAt_eq_of_gasExecRel_of_targetInstr_no_call_create
                    hNoCallCreate hRel] at hBudget
                exact hBudget
              have hRestBudgetBody :
                  XRunListGasBudget rest targetPost ≤
                    (xBodyState full instr.op).gasAvailable.toNat :=
                xBodyState_gasAvailable_toNat_of_required hBudgetStep
              have hRestBudget :
                  XRunListGasBudget rest targetPost ≤
                    fullPost.gasAvailable.toNat := by
                rw [hBodyInstr hStepBody]
                exact hRestBudgetBody
              have hNonGasRest :
                  XRunListSuffixNonGasReady validJumps rest := by
                intro instr' rest' targetState blockResult hSuffix hRunSuffix
                  fullState hRelState
                rcases hSuffix with ⟨pre, hPrefix⟩
                exact
                  hNonGas
                    (instr := instr') (rest := rest')
                    (targetState := targetState)
                    (blockResult := blockResult)
                    ⟨instr :: pre, by simp [hPrefix]⟩
                    hRunSuffix hRelState
              exact
                ih hRun hNonGasRest hBodyRest hRestBudget hRelPost

theorem XRunListPathReady.of_nonGas_no_call_create_and_budget
    {validJumps : Array Word}
    {code : List TargetInstr} {target full : EVMState}
    {targetResult : StepResult}
    (hRun : Target.runListResult code target = .ok targetResult)
    (hNonGas : XRunListSuffixNonGasReady validJumps code)
    (hNoCallCreate :
      ∀ instr ∈ code, targetInstrUsesCallCreate instr = false)
    (hBudget : XRunListGasBudget code target ≤ full.gasAvailable.toNat)
    (hRel : GasExecRel full target) :
    XRunListPathReady validJumps code target full targetResult := by
  exact XRunListPathReady.of_nonGas_and_budget hRun hNonGas
    (XRunListBodyPreservesGas.of_all_no_call_create hNoCallCreate)
    hBudget hRel

theorem XRunListPathReady.running_prefix_of_nonGas_no_call_create_and_budget
    {validJumps : Array Word} :
    ∀ {code : List TargetInstr} {target full targetFinal : EVMState}
      {restBudget : Nat},
      Target.runListResult code target = .ok (.running targetFinal) →
      XRunListSuffixNonGasReady validJumps code →
      (∀ instr ∈ code, targetInstrUsesCallCreate instr = false) →
      XRunListGasBudget code target + restBudget ≤
        full.gasAvailable.toNat →
      GasExecRel full target →
      ∃ prefixFuel fullFinal,
        GasExecRel fullFinal targetFinal ∧
          XPrefixTrace validJumps prefixFuel full fullFinal ∧
          restBudget ≤ fullFinal.gasAvailable.toNat := by
  intro code
  induction code with
  | nil =>
      intro target full targetFinal restBudget hRun _hNonGas _hNoCall
        hBudget hRel
      simp [Target.runListResult] at hRun
      subst targetFinal
      simp [XRunListGasBudget] at hBudget
      exact ⟨0, full, hRel, XPrefixTrace.done full, by simpa using hBudget⟩
  | cons instr rest ih =>
      intro target full targetFinal restBudget hRun hNonGas hNoCall hBudget
        hRel
      have hNoCallInstr : targetInstrUsesCallCreate instr = false :=
        hNoCall instr (by simp)
      obtain ⟨hDecode, hNonGasStep, _hNoCallFromReady⟩ :=
        hNonGas
          (instr := instr) (rest := rest)
          (targetState := target) (blockResult := .running targetFinal)
          ⟨[], by simp⟩ hRun hRel
      cases hStepResult : Target.stepInstrResult instr target with
      | error err =>
          rw [Target.runListResult, hStepResult] at hRun
          change
            (Except.error err : Except EVMException StepResult) =
              .ok (.running targetFinal) at hRun
          cases hRun
      | ok stepResult =>
          cases stepResult with
          | halted halt =>
              rw [Target.runListResult, hStepResult] at hRun
              change
                (Except.ok (StepResult.halted halt) :
                    Except EVMException StepResult) =
                  .ok (.running targetFinal) at hRun
              cases hRun
          | running targetPost =>
              simp [Target.runListResult, hStepResult] at hRun
              have hBudgetRun :
                  XRunListGasBudget (instr :: rest) target =
                    XGasRequiredAt target instr.op +
                      XRunListGasBudget rest targetPost := by
                simp [XRunListGasBudget, hStepResult]
              have hBudgetStep :
                  XGasRequiredAt full instr.op +
                      (XRunListGasBudget rest targetPost + restBudget) ≤
                    full.gasAvailable.toNat := by
                rw [hBudgetRun] at hBudget
                rw [←
                  XGasRequiredAt_eq_of_gasExecRel_of_targetInstr_no_call_create
                    hNoCallInstr hRel] at hBudget
                omega
              have hRequired :
                  XGasRequiredAt full instr.op ≤ full.gasAvailable.toNat := by
                omega
              have hChecks :
                  XStepChecksPass validJumps full instr.op :=
                XStepChecksPass.of_nonGas_required_le hNonGasStep hRequired
              obtain ⟨hTargetStep, hKind⟩ :=
                Target.stepInstrResult_running_stepInstr hStepResult
              obtain ⟨fullPost, hStep, hRelPost⟩ :=
                EVM_step_targetInstr_exists_gasExecRel
                  (fuel := 0)
                  (gasCost :=
                    EvmYul.EVM.C' (memoryGasState full instr.op)
                      instr.op)
                  hNoCallInstr
                  (hRel.memoryGasState_left (op := instr.op))
                  hTargetStep
              have hStepBody :
                  EvmYul.step instr.op instr.arg
                      (xBodyState full instr.op) =
                    .ok fullPost := by
                rw [← EVM_step_targetInstr_eq_xBodyState
                  (fuel := 0) (state := full) (instr := instr)
                  hNoCallInstr]
                exact hStep
              have hRestBudgetBody :
                  XRunListGasBudget rest targetPost + restBudget ≤
                    (xBodyState full instr.op).gasAvailable.toNat :=
                xBodyState_gasAvailable_toNat_of_required hBudgetStep
              have hRestBudget :
                  XRunListGasBudget rest targetPost + restBudget ≤
                    fullPost.gasAvailable.toNat := by
                rw [TargetInstrBodyPreservesGas.of_no_call_create
                  hNoCallInstr hStepBody]
                exact hRestBudgetBody
              have hNonGasRest :
                  XRunListSuffixNonGasReady validJumps rest := by
                intro instr' rest' targetState blockResult hSuffix hRunSuffix
                  fullState hRelState
                rcases hSuffix with ⟨pre, hPrefix⟩
                exact
                  hNonGas
                    (instr := instr') (rest := rest')
                    (targetState := targetState)
                    (blockResult := blockResult)
                    ⟨instr :: pre, by simp [hPrefix]⟩
                    hRunSuffix hRelState
              have hNoCallRest :
                  ∀ instr' ∈ rest,
                    targetInstrUsesCallCreate instr' = false := by
                intro instr' hMem
                exact hNoCall instr' (by simp [hMem])
              obtain
                ⟨fuelTail, fullFinal, hRelFinal, hPrefixTail,
                  hRestFinal⟩ :=
                ih hRun hNonGasRest hNoCallRest hRestBudget hRelPost
              have hStepAll :
                  ∀ tailFuel : Nat,
                    EvmYul.EVM.step tailFuel.succ
                        (EvmYul.EVM.C' (memoryGasState full instr.op)
                          instr.op)
                        (some (instr.op, instr.arg))
                        (memoryGasState full instr.op) =
                      .ok fullPost := by
                intro tailFuel
                rw [EVM_step_targetInstr_eq_of_no_call_create
                  (fuel := tailFuel)
                  (gasCost :=
                    EvmYul.EVM.C' (memoryGasState full instr.op)
                      instr.op)
                  (state := memoryGasState full instr.op)
                  (instr := instr) hNoCallInstr]
                rw [EVM_step_targetInstr_eq_of_no_call_create
                  (fuel := 0)
                  (gasCost :=
                    EvmYul.EVM.C' (memoryGasState full instr.op)
                      instr.op)
                  (state := memoryGasState full instr.op)
                  (instr := instr) hNoCallInstr] at hStep
                exact hStep
              have hNoHalt : XHaltOutput? instr.op fullPost = none :=
                XHaltOutput?_none_of_targetInstr_haltKind_none hKind
              exact
                ⟨fuelTail.succ, fullFinal, hRelFinal,
                  XPrefixTrace.running hDecode hChecks hStepAll hNoHalt
                    hPrefixTail,
                  hRestFinal⟩

theorem XRunListPathReady.running_prefix {validJumps : Array Word} :
    ∀ {code : List TargetInstr} {target full targetFinal : EVMState},
      XRunListPathReady validJumps code target full (.running targetFinal) →
      ∃ fuel fullFinal,
        GasExecRel fullFinal targetFinal ∧
          XPrefixTrace validJumps fuel full fullFinal := by
  intro code
  induction code with
  | nil =>
      intro target full targetFinal hReady
      rcases hReady with ⟨hResult, hRel⟩
      cases hResult
      exact ⟨0, full, hRel, XPrefixTrace.done full⟩
  | cons instr rest ih =>
      intro target full targetFinal hReady
      rcases hReady with
        ⟨hRel, hDecode, hNonGas, hGas, hNoCallCreate, hStepReady⟩
      have hChecks :
          XStepChecksPass validJumps full instr.op :=
        XStepChecksPass.of_nonGas_required_le hNonGas hGas
      cases hStepResult : Target.stepInstrResult instr target with
      | error err =>
          simp [hStepResult] at hStepReady
      | ok stepResult =>
          cases stepResult with
          | halted halt =>
              simp [hStepResult] at hStepReady
          | running targetPost =>
              simp [hStepResult] at hStepReady
              obtain ⟨hTargetStep, hKind⟩ :=
                Target.stepInstrResult_running_stepInstr hStepResult
              obtain ⟨fullPost, hStep, hRelPost⟩ :=
                EVM_step_targetInstr_exists_gasExecRel
                  (fuel := 0)
                  (gasCost :=
                    EvmYul.EVM.C' (memoryGasState full instr.op)
                      instr.op)
                  hNoCallCreate
                  (hRel.memoryGasState_left (op := instr.op))
                  hTargetStep
              obtain ⟨fuelTail, fullFinal, hRelFinal, hPrefixTail⟩ :=
                ih (hStepReady hStep)
              have hStepAll :
                  ∀ tailFuel : Nat,
                    EvmYul.EVM.step tailFuel.succ
                        (EvmYul.EVM.C' (memoryGasState full instr.op)
                          instr.op)
                        (some (instr.op, instr.arg))
                        (memoryGasState full instr.op) =
                      .ok fullPost := by
                intro tailFuel
                rw [EVM_step_targetInstr_eq_of_no_call_create
                  (fuel := tailFuel)
                  (gasCost :=
                    EvmYul.EVM.C' (memoryGasState full instr.op)
                      instr.op)
                  (state := memoryGasState full instr.op)
                  (instr := instr) hNoCallCreate]
                rw [EVM_step_targetInstr_eq_of_no_call_create
                  (fuel := 0)
                  (gasCost :=
                    EvmYul.EVM.C' (memoryGasState full instr.op)
                      instr.op)
                  (state := memoryGasState full instr.op)
                  (instr := instr) hNoCallCreate] at hStep
                exact hStep
              have hNoHalt : XHaltOutput? instr.op fullPost = none :=
                XHaltOutput?_none_of_targetInstr_haltKind_none hKind
              exact
                ⟨fuelTail.succ, fullFinal, hRelFinal,
                  XPrefixTrace.running hDecode hChecks hStepAll hNoHalt
                    hPrefixTail⟩

theorem runListResult_with_continuation_exists_agrees_of_path_ready
    {validJumps : Array Word} :
    ∀ {code : List TargetInstr} {target full : EVMState}
      {blockResult finalResult : StepResult},
      XRunListPathReady validJumps code target full blockResult →
      (∀ halt, blockResult = .halted halt → finalResult = .halted halt) →
      (∀ targetFinal,
        blockResult = .running targetFinal →
          ∃ fuel : Nat,
            ∀ fullFinal,
              GasExecRel fullFinal targetFinal →
                ∃ evmResult,
                  XStepTrace validJumps fuel.succ fullFinal evmResult ∧
                    XResultAgrees finalResult evmResult) →
      ∃ fuel : Nat, ∃ evmResult,
        XStepTrace validJumps fuel.succ full evmResult ∧
          XResultAgrees finalResult evmResult := by
  intro code
  induction code with
  | nil =>
      intro target full blockResult finalResult hReady _hHalted hContinue
      rcases hReady with ⟨hResult, hRel⟩
      subst blockResult
      obtain ⟨fuel, hReplay⟩ := hContinue target rfl
      obtain ⟨evmResult, hTrace, hAgree⟩ := hReplay full hRel
      exact ⟨fuel, evmResult, hTrace, hAgree⟩
  | cons instr rest ih =>
      intro target full blockResult finalResult hReady hHalted hContinue
      rcases hReady with
        ⟨hRel, hDecode, hNonGas, hGas, hNoCallCreate, hStepReady⟩
      have hChecks :
          XStepChecksPass validJumps full instr.op :=
        XStepChecksPass.of_nonGas_required_le hNonGas hGas
      cases hStepResult : Target.stepInstrResult instr target with
      | error err =>
          simp [hStepResult] at hStepReady
      | ok stepResult =>
          cases stepResult with
          | running targetPost =>
              simp [hStepResult] at hStepReady
              obtain ⟨hTargetStep, hKind⟩ :=
                Target.stepInstrResult_running_stepInstr hStepResult
              obtain ⟨fullPost, hStep, hRelPost⟩ :=
                EVM_step_targetInstr_exists_gasExecRel
                  (fuel := 0)
                  (gasCost :=
                    EvmYul.EVM.C' (memoryGasState full instr.op)
                      instr.op)
                  hNoCallCreate
                  (hRel.memoryGasState_left (op := instr.op))
                  hTargetStep
              obtain ⟨fuelRest, evmResult, hRestTrace, hAgree⟩ :=
                ih (hStepReady hStep) hHalted hContinue
              have hStepFuel :
                  EvmYul.EVM.step fuelRest.succ
                      (EvmYul.EVM.C' (memoryGasState full instr.op)
                        instr.op)
                      (some (instr.op, instr.arg))
                      (memoryGasState full instr.op) =
                    .ok fullPost := by
                rw [EVM_step_targetInstr_eq_of_no_call_create
                  (fuel := fuelRest)
                  (gasCost :=
                    EvmYul.EVM.C' (memoryGasState full instr.op)
                      instr.op)
                  (state := memoryGasState full instr.op)
                  (instr := instr) hNoCallCreate]
                rw [EVM_step_targetInstr_eq_of_no_call_create
                  (fuel := 0)
                  (gasCost :=
                    EvmYul.EVM.C' (memoryGasState full instr.op)
                      instr.op)
                  (state := memoryGasState full instr.op)
                  (instr := instr) hNoCallCreate] at hStep
                exact hStep
              have hNoHalt : XHaltOutput? instr.op fullPost = none :=
                XHaltOutput?_none_of_targetInstr_haltKind_none hKind
              exact
                ⟨fuelRest.succ, evmResult,
                  XStepTrace.running hDecode hChecks hStepFuel hNoHalt
                    hRestTrace,
                  hAgree⟩
          | halted halt =>
              simp [hStepResult] at hStepReady
              subst blockResult
              have hFinal : finalResult = .halted halt :=
                hHalted halt rfl
              subst finalResult
              by_cases hRevert : halt.kind = .revert
              · obtain ⟨fullPost, _hRelPost, hTrace, hAgree⟩ :=
                  targetInstr_revert_exists_agrees
                    (fuel := 0)
                    (instr := instr)
                    (full := full)
                    (target := target)
                    (halt := halt)
                    hNoCallCreate hRel hDecode hChecks hStepResult hRevert
                exact
                  ⟨1, .revert fullPost.gasAvailable halt.output, hTrace,
                    hAgree⟩
              · obtain ⟨fullPost, _hRelPost, hTrace, hAgree⟩ :=
                  targetInstr_success_exists_agrees
                    (fuel := 0)
                    (instr := instr)
                    (full := full)
                    (target := target)
                    (halt := halt)
                    hNoCallCreate hRel hDecode hChecks hStepResult hRevert
                exact
                  ⟨1, .success fullPost halt.output, hTrace, hAgree⟩

theorem runListResult_with_path_continuation_exists_agrees_of_path_ready
    {validJumps : Array Word} :
    ∀ {code : List TargetInstr} {target full : EVMState}
      {blockResult finalResult : StepResult},
      XRunListPathReady validJumps code target full blockResult →
      (∀ halt, blockResult = .halted halt → finalResult = .halted halt) →
      (∀ targetFinal fullFinal,
        blockResult = .running targetFinal →
          GasExecRel fullFinal targetFinal →
            ∃ fuel : Nat, ∃ evmResult,
              XStepTrace validJumps fuel.succ fullFinal evmResult ∧
                XResultAgrees finalResult evmResult) →
      ∃ fuel : Nat, ∃ evmResult,
        XStepTrace validJumps fuel.succ full evmResult ∧
          XResultAgrees finalResult evmResult := by
  intro code
  induction code with
  | nil =>
      intro target full blockResult finalResult hReady _hHalted hContinue
      rcases hReady with ⟨hResult, hRel⟩
      subst blockResult
      exact hContinue target full rfl hRel
  | cons instr rest ih =>
      intro target full blockResult finalResult hReady hHalted hContinue
      rcases hReady with
        ⟨hRel, hDecode, hNonGas, hGas, hNoCallCreate, hStepReady⟩
      have hChecks :
          XStepChecksPass validJumps full instr.op :=
        XStepChecksPass.of_nonGas_required_le hNonGas hGas
      cases hStepResult : Target.stepInstrResult instr target with
      | error err =>
          simp [hStepResult] at hStepReady
      | ok stepResult =>
          cases stepResult with
          | running targetPost =>
              simp [hStepResult] at hStepReady
              obtain ⟨hTargetStep, hKind⟩ :=
                Target.stepInstrResult_running_stepInstr hStepResult
              obtain ⟨fullPost, hStep, hRelPost⟩ :=
                EVM_step_targetInstr_exists_gasExecRel
                  (fuel := 0)
                  (gasCost :=
                    EvmYul.EVM.C' (memoryGasState full instr.op)
                      instr.op)
                  hNoCallCreate
                  (hRel.memoryGasState_left (op := instr.op))
                  hTargetStep
              obtain ⟨fuelRest, evmResult, hRestTrace, hAgree⟩ :=
                ih (hStepReady hStep) hHalted hContinue
              have hStepFuel :
                  EvmYul.EVM.step fuelRest.succ
                      (EvmYul.EVM.C' (memoryGasState full instr.op)
                        instr.op)
                      (some (instr.op, instr.arg))
                      (memoryGasState full instr.op) =
                    .ok fullPost := by
                rw [EVM_step_targetInstr_eq_of_no_call_create
                  (fuel := fuelRest)
                  (gasCost :=
                    EvmYul.EVM.C' (memoryGasState full instr.op)
                      instr.op)
                  (state := memoryGasState full instr.op)
                  (instr := instr) hNoCallCreate]
                rw [EVM_step_targetInstr_eq_of_no_call_create
                  (fuel := 0)
                  (gasCost :=
                    EvmYul.EVM.C' (memoryGasState full instr.op)
                      instr.op)
                  (state := memoryGasState full instr.op)
                  (instr := instr) hNoCallCreate] at hStep
                exact hStep
              have hNoHalt : XHaltOutput? instr.op fullPost = none :=
                XHaltOutput?_none_of_targetInstr_haltKind_none hKind
              exact
                ⟨fuelRest.succ, evmResult,
                  XStepTrace.running hDecode hChecks hStepFuel hNoHalt
                    hRestTrace,
                  hAgree⟩
          | halted halt =>
              simp [hStepResult] at hStepReady
              subst blockResult
              have hFinal : finalResult = .halted halt :=
                hHalted halt rfl
              subst finalResult
              by_cases hRevert : halt.kind = .revert
              · obtain ⟨fullPost, _hRelPost, hTrace, hAgree⟩ :=
                  targetInstr_revert_exists_agrees
                    (fuel := 0)
                    (instr := instr)
                    (full := full)
                    (target := target)
                    (halt := halt)
                    hNoCallCreate hRel hDecode hChecks hStepResult hRevert
                exact
                  ⟨1, .revert fullPost.gasAvailable halt.output, hTrace,
                    hAgree⟩
              · obtain ⟨fullPost, _hRelPost, hTrace, hAgree⟩ :=
                  targetInstr_success_exists_agrees
                    (fuel := 0)
                    (instr := instr)
                    (full := full)
                    (target := target)
                    (halt := halt)
                    hNoCallCreate hRel hDecode hChecks hStepResult hRevert
                exact
                  ⟨1, .success fullPost halt.output, hTrace, hAgree⟩

theorem runListResult_exists_agrees_of_instr_ready
    {validJumps : Array Word} :
    ∀ {code : List TargetInstr} {target : EVMState}
      {targetResult : StepResult},
      Target.runListResult code target = .ok targetResult →
      XRunListSuffixReady validJumps code →
      (∀ targetFinal,
        targetResult = .running targetFinal →
          ∃ fuel : Nat,
            ∀ fullFinal,
              GasExecRel fullFinal targetFinal →
                ∃ evmResult,
                  XStepTrace validJumps fuel.succ fullFinal evmResult ∧
                    XResultAgrees targetResult evmResult) →
      ∃ fuel : Nat,
        ∀ full,
          GasExecRel full target →
            ∃ evmResult,
              XStepTrace validJumps fuel.succ full evmResult ∧
                XResultAgrees targetResult evmResult := by
  intro code
  induction code with
  | nil =>
      intro target targetResult hRun _hReady hContinue
      simp [Target.runListResult] at hRun
      subst targetResult
      exact hContinue target rfl
  | cons instr rest ih =>
      intro target targetResult hRun hReady hContinue
      rcases Target.runListResult_cons_ok_cases hRun with
        ⟨targetPost, hStepResult, hRunRest⟩ | ⟨halt, hStepResult, hResult⟩
      · have hReadyRest :
            XRunListSuffixReady validJumps rest := by
          intro instr' rest' targetState blockResult hSuffix hRunSuffix
          intro fullState hRel
          rcases hSuffix with ⟨pre, hPrefix⟩
          exact
            hReady
              (instr := instr') (rest := rest')
              (targetState := targetState) (blockResult := blockResult)
              ⟨instr :: pre, by simp [hPrefix]⟩ hRunSuffix hRel
        obtain ⟨fuelRest, hRestAll⟩ :=
          ih hRunRest hReadyRest hContinue
        refine ⟨fuelRest.succ, ?_⟩
        intro full hRel
        obtain ⟨hDecode, hNonGas, hRequired, hNoCallCreate⟩ :=
          hReady
            (instr := instr) (rest := rest)
            (targetState := target) (blockResult := targetResult)
            ⟨[], by simp⟩ hRun hRel
        have hChecks :
            XStepChecksPass validJumps full instr.op :=
          XStepChecksPass.of_nonGas_required_le hNonGas hRequired
        obtain ⟨hTargetStep, hKind⟩ :=
          Target.stepInstrResult_running_stepInstr hStepResult
        obtain ⟨fullPost, hStep, hRelPost⟩ :=
          EVM_step_targetInstr_exists_gasExecRel
            (fuel := fuelRest)
            (gasCost := EvmYul.EVM.C' (memoryGasState full instr.op) instr.op)
            hNoCallCreate (hRel.memoryGasState_left (op := instr.op))
            hTargetStep
        obtain ⟨evmResult, hRestTrace, hAgree⟩ :=
          hRestAll fullPost hRelPost
        have hNoHalt : XHaltOutput? instr.op fullPost = none :=
          XHaltOutput?_none_of_targetInstr_haltKind_none hKind
        exact
          ⟨evmResult,
            XStepTrace.running hDecode hChecks hStep hNoHalt hRestTrace,
            hAgree⟩
      · subst targetResult
        refine ⟨1, ?_⟩
        intro full hRel
        obtain ⟨hDecode, hNonGas, hRequired, hNoCallCreate⟩ :=
          hReady
            (instr := instr) (rest := rest)
            (targetState := target) (blockResult := .halted halt)
            ⟨[], by simp⟩ (by simpa using hRun) hRel
        have hChecks :
            XStepChecksPass validJumps full instr.op :=
          XStepChecksPass.of_nonGas_required_le hNonGas hRequired
        by_cases hRevert : halt.kind = .revert
        · obtain ⟨fullPost, _hRelPost, hTrace, hAgree⟩ :=
            targetInstr_revert_exists_agrees
              (fuel := 0)
              (instr := instr)
              (full := full)
              (target := target)
              (halt := halt)
              hNoCallCreate hRel hDecode hChecks hStepResult hRevert
          exact
            ⟨.revert fullPost.gasAvailable halt.output, hTrace, hAgree⟩
        · obtain ⟨fullPost, _hRelPost, hTrace, hAgree⟩ :=
            targetInstr_success_exists_agrees
              (fuel := 0)
              (instr := instr)
              (full := full)
              (target := target)
              (halt := halt)
              hNoCallCreate hRel hDecode hChecks hStepResult hRevert
          exact ⟨.success fullPost halt.output, hTrace, hAgree⟩

theorem runListResult_with_continuation_exists_agrees_of_instr_ready
    {validJumps : Array Word} :
    ∀ {code : List TargetInstr} {target : EVMState}
      {blockResult finalResult : StepResult},
      Target.runListResult code target = .ok blockResult →
      XRunListSuffixReady validJumps code →
      (∀ halt, blockResult = .halted halt → finalResult = .halted halt) →
      (∀ targetFinal,
        blockResult = .running targetFinal →
          ∃ fuel : Nat,
            ∀ fullFinal,
              GasExecRel fullFinal targetFinal →
                ∃ evmResult,
                  XStepTrace validJumps fuel.succ fullFinal evmResult ∧
                    XResultAgrees finalResult evmResult) →
      ∃ fuel : Nat,
        ∀ full,
          GasExecRel full target →
            ∃ evmResult,
              XStepTrace validJumps fuel.succ full evmResult ∧
                XResultAgrees finalResult evmResult := by
  intro code
  induction code with
  | nil =>
      intro target blockResult finalResult hRun _hReady _hHalted hContinue
      simp [Target.runListResult] at hRun
      subst blockResult
      exact hContinue target rfl
  | cons instr rest ih =>
      intro target blockResult finalResult hRun hReady hHalted hContinue
      rcases Target.runListResult_cons_ok_cases hRun with
        ⟨targetPost, hStepResult, hRunRest⟩ | ⟨halt, hStepResult, hBlockResult⟩
      · have hReadyRest :
            XRunListSuffixReady validJumps rest := by
          intro instr' rest' targetState blockResult' hSuffix hRunSuffix
          intro fullState hRel
          rcases hSuffix with ⟨pre, hPrefix⟩
          exact
            hReady
              (instr := instr') (rest := rest')
              (targetState := targetState) (blockResult := blockResult')
              ⟨instr :: pre, by simp [hPrefix]⟩ hRunSuffix hRel
        obtain ⟨fuelRest, hRestAll⟩ :=
          ih hRunRest hReadyRest hHalted hContinue
        refine ⟨fuelRest.succ, ?_⟩
        intro full hRel
        obtain ⟨hDecode, hNonGas, hRequired, hNoCallCreate⟩ :=
          hReady
            (instr := instr) (rest := rest)
            (targetState := target) (blockResult := blockResult)
            ⟨[], by simp⟩ hRun hRel
        have hChecks :
            XStepChecksPass validJumps full instr.op :=
          XStepChecksPass.of_nonGas_required_le hNonGas hRequired
        obtain ⟨hTargetStep, hKind⟩ :=
          Target.stepInstrResult_running_stepInstr hStepResult
        obtain ⟨fullPost, hStep, hRelPost⟩ :=
          EVM_step_targetInstr_exists_gasExecRel
            (fuel := fuelRest)
            (gasCost := EvmYul.EVM.C' (memoryGasState full instr.op) instr.op)
            hNoCallCreate (hRel.memoryGasState_left (op := instr.op))
            hTargetStep
        obtain ⟨evmResult, hRestTrace, hAgree⟩ :=
          hRestAll fullPost hRelPost
        have hNoHalt : XHaltOutput? instr.op fullPost = none :=
          XHaltOutput?_none_of_targetInstr_haltKind_none hKind
        exact
          ⟨evmResult,
            XStepTrace.running hDecode hChecks hStep hNoHalt hRestTrace,
            hAgree⟩
      · subst blockResult
        have hFinal : finalResult = .halted halt :=
          hHalted halt rfl
        subst finalResult
        refine ⟨1, ?_⟩
        intro full hRel
        obtain ⟨hDecode, hNonGas, hRequired, hNoCallCreate⟩ :=
          hReady
            (instr := instr) (rest := rest)
            (targetState := target) (blockResult := .halted halt)
            ⟨[], by simp⟩ (by simpa using hRun) hRel
        have hChecks :
            XStepChecksPass validJumps full instr.op :=
          XStepChecksPass.of_nonGas_required_le hNonGas hRequired
        by_cases hRevert : halt.kind = .revert
        · obtain ⟨fullPost, _hRelPost, hTrace, hAgree⟩ :=
            targetInstr_revert_exists_agrees
              (fuel := 0)
              (instr := instr)
              (full := full)
              (target := target)
              (halt := halt)
              hNoCallCreate hRel hDecode hChecks hStepResult hRevert
          exact
            ⟨.revert fullPost.gasAvailable halt.output, hTrace, hAgree⟩
        · obtain ⟨fullPost, _hRelPost, hTrace, hAgree⟩ :=
            targetInstr_success_exists_agrees
              (fuel := 0)
              (instr := instr)
              (full := full)
              (target := target)
              (halt := halt)
              hNoCallCreate hRel hDecode hChecks hStepResult hRevert
          exact ⟨.success fullPost halt.output, hTrace, hAgree⟩

def XBlockReplayReady
    (program : Program) (target : TargetProgram)
    (validJumps : Array Word) : Prop :=
  ∀ {pc : Nat} {instr : Instr}
      {emitted before after : List LocatedTarget}
      {blockState : EVMState} {blockResult : StepResult},
    Program.instrAtPc program blockState.pc.toNat = some (pc, instr) →
      emitInstr? program pc instr = some emitted →
        target.code = before ++ emitted ++ after →
          Target.runListResult (emitted.map LocatedTarget.instr) blockState =
            .ok blockResult →
          XRunListSuffixReady validJumps (emitted.map LocatedTarget.instr)

def XBlockReplayNonGasReady
    (program : Program) (target : TargetProgram)
    (validJumps : Array Word) : Prop :=
  ∀ {pc : Nat} {instr : Instr}
      {emitted before after : List LocatedTarget}
      {blockState : EVMState} {blockResult : StepResult},
    Program.instrAtPc program blockState.pc.toNat = some (pc, instr) →
      emitInstr? program pc instr = some emitted →
        target.code = before ++ emitted ++ after →
          Target.runListResult (emitted.map LocatedTarget.instr) blockState =
            .ok blockResult →
          XRunListSuffixNonGasReady validJumps
            (emitted.map LocatedTarget.instr)

def XBlockReplayGasReady
    (program : Program) (target : TargetProgram) : Prop :=
  ∀ {pc : Nat} {instr : Instr}
      {emitted before after : List LocatedTarget}
      {blockState : EVMState} {blockResult : StepResult},
    Program.instrAtPc program blockState.pc.toNat = some (pc, instr) →
      emitInstr? program pc instr = some emitted →
        target.code = before ++ emitted ++ after →
          Target.runListResult (emitted.map LocatedTarget.instr) blockState =
            .ok blockResult →
          XRunListSuffixGasReady (emitted.map LocatedTarget.instr)

def XBlockReplayNoCallCreate
    (program : Program) (target : TargetProgram) : Prop :=
  ∀ {pc : Nat} {instr : Instr}
      {emitted before after : List LocatedTarget}
      {blockState : EVMState} {blockResult : StepResult},
    Program.instrAtPc program blockState.pc.toNat = some (pc, instr) →
      emitInstr? program pc instr = some emitted →
        target.code = before ++ emitted ++ after →
          Target.runListResult (emitted.map LocatedTarget.instr) blockState =
            .ok blockResult →
          ∀ targetInstr ∈ emitted.map LocatedTarget.instr,
            targetInstrUsesCallCreate targetInstr = false

theorem XBlockReplayNoCallCreate.of_program_no_call_create
    {program : Program} {target : TargetProgram}
    (hNoCallCreate : Program.usesCallCreate program = false) :
    XBlockReplayNoCallCreate program target := by
  intro pc instr emitted before after blockState blockResult hAt hEmit
    _hTargetBlock _hRun targetInstr hMem
  rcases List.mem_map.mp hMem with ⟨located, hLocatedMem, hEq⟩
  subst targetInstr
  exact targetInstr_usesCallCreate_false_of_program_noCall_emit_mem
    hNoCallCreate hAt hEmit hLocatedMem

def XBlockTraceGasBudget (program : Program) :
    Nat → EVMState → StepResult → Nat
  | 0, _state, _result => 0
  | fuel + 1, state, result =>
      match Program.instrAtPc program state.pc.toNat with
      | none => 0
      | some (pc, instr) =>
          match emitInstr? program pc instr with
          | none => 0
          | some emitted =>
              let code := emitted.map LocatedTarget.instr
              match Target.runListResult code state with
              | .ok (.running mid) =>
                  XRunListGasBudget code state +
                    XBlockTraceGasBudget program fuel mid result
              | .ok (.halted _halt) =>
                  XRunListGasBudget code state
              | .error _ => 0

theorem XBlockReplayReady.of_parts {program : Program}
    {target : TargetProgram} {validJumps : Array Word}
    (hNonGas : XBlockReplayNonGasReady program target validJumps)
    (hGas : XBlockReplayGasReady program target) :
    XBlockReplayReady program target validJumps := by
  intro pc instr emitted before after blockState blockResult
    hAt hEmit hTargetBlock hRun
  exact
    XRunListSuffixReady.of_parts
      (hNonGas hAt hEmit hTargetBlock hRun)
      (hGas hAt hEmit hTargetBlock hRun)

theorem XBlockReplayReady.nonGas {program : Program}
    {target : TargetProgram} {validJumps : Array Word}
    (hReady : XBlockReplayReady program target validJumps) :
    XBlockReplayNonGasReady program target validJumps := by
  intro pc instr emitted before after blockState blockResult
    hAt hEmit hTargetBlock hRun
  exact XRunListSuffixReady.nonGas
    (hReady hAt hEmit hTargetBlock hRun)

theorem XBlockReplayReady.gas {program : Program}
    {target : TargetProgram} {validJumps : Array Word}
    (hReady : XBlockReplayReady program target validJumps) :
    XBlockReplayGasReady program target := by
  intro pc instr emitted before after blockState blockResult
    hAt hEmit hTargetBlock hRun
  exact XRunListSuffixReady.gas
    (hReady hAt hEmit hTargetBlock hRun)

def XTraceDoneContinuation
    (validJumps : Array Word) (result : StepResult) : Prop :=
  ∀ finalState,
    result = .running finalState →
      ∃ fuel : Nat,
        ∀ fullFinal,
          GasExecRel fullFinal finalState →
            ∃ evmResult,
              XStepTrace validJumps fuel.succ fullFinal evmResult ∧
                XResultAgrees result evmResult

def XTracePathDoneContinuation
    (validJumps : Array Word) (result : StepResult) : Prop :=
  ∀ finalState fullFinal,
    result = .running finalState →
      GasExecRel fullFinal finalState →
        ∃ fuel : Nat, ∃ evmResult,
          XStepTrace validJumps fuel.succ fullFinal evmResult ∧
            XResultAgrees result evmResult

theorem XTraceDoneContinuation.to_path {validJumps : Array Word}
    {result : StepResult}
    (hDone : XTraceDoneContinuation validJumps result) :
    XTracePathDoneContinuation validJumps result := by
  intro finalState fullFinal hResult hRel
  obtain ⟨fuel, hAll⟩ := hDone finalState hResult
  obtain ⟨evmResult, hTrace, hAgree⟩ := hAll fullFinal hRel
  exact ⟨fuel, evmResult, hTrace, hAgree⟩

inductive XBlockTracePathReady
    (program : Program) (target : TargetProgram)
    (validJumps : Array Word) :
    Nat → EVMState → EVMState → StepResult → Prop where
  | done {state full : EVMState}
      (hRel : GasExecRel full state) :
      XBlockTracePathReady program target validJumps 0 state full
        (.running state)
  | stepRunning {fuel : Nat} {state full mid : EVMState}
      {result : StepResult}
      {pc : Nat} {instr : Instr}
      {emitted before after : List LocatedTarget}
      (hAt : Program.instrAtPc program state.pc.toNat = some (pc, instr))
      (hEmit : emitInstr? program pc instr = some emitted)
      (hTargetBlock : target.code = before ++ emitted ++ after)
      (hRun :
        Target.runListResult (emitted.map LocatedTarget.instr) state =
          .ok (.running mid))
      (hBlockPath :
        XRunListPathReady validJumps (emitted.map LocatedTarget.instr)
          state full (.running mid))
      (hRest :
        ∀ {prefixFuel : Nat} {fullMid : EVMState},
          XPrefixTrace validJumps prefixFuel full fullMid →
            GasExecRel fullMid mid →
              XBlockTracePathReady program target validJumps fuel mid
                fullMid result) :
      XBlockTracePathReady program target validJumps fuel.succ state full
        result
  | stepHalted {fuel : Nat} {state full : EVMState}
      {halt : Halt}
      {pc : Nat} {instr : Instr}
      {emitted before after : List LocatedTarget}
      (hAt : Program.instrAtPc program state.pc.toNat = some (pc, instr))
      (hEmit : emitInstr? program pc instr = some emitted)
      (hTargetBlock : target.code = before ++ emitted ++ after)
      (hRun :
        Target.runListResult (emitted.map LocatedTarget.instr) state =
          .ok (.halted halt))
      (hBlockPath :
        XRunListPathReady validJumps (emitted.map LocatedTarget.instr)
          state full (.halted halt)) :
      XBlockTracePathReady program target validJumps fuel.succ state full
        (.halted halt)

theorem XBlockTracePathReady.exists_agrees
    {program : Program} {target : TargetProgram}
    {validJumps : Array Word} {fuel : Nat}
    {state full : EVMState} {result : StepResult}
    (hReady :
      XBlockTracePathReady program target validJumps fuel state full result)
    (hDoneContinue : XTracePathDoneContinuation validJumps result) :
    ∃ fuel : Nat, ∃ evmResult,
      XStepTrace validJumps fuel.succ full evmResult ∧
        XResultAgrees result evmResult := by
  induction hReady with
  | done hRel =>
      exact hDoneContinue _ _ rfl hRel
  | stepRunning hAt hEmit hTargetBlock hRun hBlockPath hRest ih =>
      obtain ⟨prefixFuel, fullMid, hRelMid, hPrefix⟩ :=
        XRunListPathReady.running_prefix hBlockPath
      obtain ⟨restFuel, evmResult, hRestTrace, hAgree⟩ :=
        ih hPrefix hRelMid hDoneContinue
      obtain ⟨fuel, hTrace⟩ :=
        XPrefixTrace.then_stepTrace hPrefix hRestTrace
      exact ⟨fuel, evmResult, hTrace, hAgree⟩
  | stepHalted hAt hEmit hTargetBlock hRun hBlockPath =>
      refine
        runListResult_with_path_continuation_exists_agrees_of_path_ready
          hBlockPath ?_ ?_
      · intro halt hEq
        cases hEq
        rfl
      · intro targetFinal fullFinal hImpossible _hRel
        cases hImpossible

theorem blockTraceResult_exists_agrees_of_nonGas_no_call_create_and_budget
    {program : Program} {target : TargetProgram}
    {validJumps : Array Word} :
    ∀ {targetFuel : Nat} {state full : EVMState}
      {targetResult : StepResult},
      Preservation.BlockTraceResult program target targetFuel state
        targetResult →
      XBlockReplayNonGasReady program target validJumps →
      XBlockReplayNoCallCreate program target →
      XBlockTraceGasBudget program targetFuel state targetResult ≤
        full.gasAvailable.toNat →
      GasExecRel full state →
      XTracePathDoneContinuation validJumps targetResult →
      ∃ fuel : Nat, ∃ evmResult,
        XStepTrace validJumps fuel.succ full evmResult ∧
          XResultAgrees targetResult evmResult := by
  intro targetFuel state full targetResult hTrace
  induction hTrace generalizing full with
  | done state =>
      intro _hNonGas _hNoCall _hBudget hRel hDoneContinue
      exact hDoneContinue state full rfl hRel
  | stepRunning hAt hEmit hTargetBlock hRun hRest ih =>
      intro hNonGas hNoCall hBudget hRel hDoneContinue
      rename_i fuel state mid result pc instr emitted before after
      let code := emitted.map LocatedTarget.instr
      have hNonGasCode : XRunListSuffixNonGasReady validJumps code := by
        dsimp [code]
        exact hNonGas hAt hEmit hTargetBlock hRun
      have hNoCallCode :
          ∀ targetInstr ∈ code,
            targetInstrUsesCallCreate targetInstr = false := by
        dsimp [code]
        exact hNoCall hAt hEmit hTargetBlock hRun
      have hBudgetBlock :
          XRunListGasBudget code state +
              XBlockTraceGasBudget program fuel mid result ≤
            full.gasAvailable.toNat := by
        simpa [XBlockTraceGasBudget, hAt, hEmit, hRun, code,
          Nat.add_comm] using hBudget
      obtain ⟨prefixFuel, fullMid, hRelMid, hPrefix, hRestBudget⟩ :=
        XRunListPathReady.running_prefix_of_nonGas_no_call_create_and_budget
          (validJumps := validJumps)
          (code := code)
          (target := state)
          (full := full)
          (targetFinal := mid)
          (restBudget := XBlockTraceGasBudget program fuel mid result)
          (by simpa [code] using hRun)
          hNonGasCode
          hNoCallCode
          hBudgetBlock hRel
      obtain ⟨restFuel, evmResult, hRestTrace, hAgree⟩ :=
        ih hNonGas hNoCall hRestBudget hRelMid hDoneContinue
      obtain ⟨fuelAll, hTraceAll⟩ :=
        XPrefixTrace.then_stepTrace hPrefix hRestTrace
      exact ⟨fuelAll, evmResult, hTraceAll, hAgree⟩
  | stepHalted hAt hEmit hTargetBlock hRun =>
      intro hNonGas hNoCall hBudget hRel _hDoneContinue
      rename_i fuel state halt pc instr emitted before after
      let code := emitted.map LocatedTarget.instr
      have hNonGasCode : XRunListSuffixNonGasReady validJumps code := by
        dsimp [code]
        exact hNonGas hAt hEmit hTargetBlock hRun
      have hNoCallCode :
          ∀ targetInstr ∈ code,
            targetInstrUsesCallCreate targetInstr = false := by
        dsimp [code]
        exact hNoCall hAt hEmit hTargetBlock hRun
      have hBudgetBlock :
          XRunListGasBudget code state ≤ full.gasAvailable.toNat := by
        simpa [XBlockTraceGasBudget, hAt, hEmit, hRun, code,
          Nat.add_comm] using hBudget
      have hBlockPath :
          XRunListPathReady validJumps code state full (.halted halt) :=
        XRunListPathReady.of_nonGas_no_call_create_and_budget
          (validJumps := validJumps)
          (code := code)
          (target := state)
          (full := full)
          (targetResult := .halted halt)
          (by simpa [code] using hRun)
          hNonGasCode
          hNoCallCode
          hBudgetBlock hRel
      refine
        runListResult_with_path_continuation_exists_agrees_of_path_ready
          hBlockPath ?_ ?_
      · intro halt' hEq
        cases hEq
        rfl
      · intro targetFinal fullFinal hImpossible _hRelFinal
        cases hImpossible

theorem blockTraceResult_concrete_gas_of_nonGas_no_call_create_and_budget
    {program : Program} {target : TargetProgram}
    {targetFuel : Nat} {initial : EVMState} {targetResult : StepResult}
    (hCode : initial.executionEnv.code = Bytecode.encodeTarget target)
    (hTrace :
      Preservation.BlockTraceResult program target targetFuel initial
        targetResult)
    (hGasBoundFits :
      XBlockTraceGasBudget program targetFuel initial targetResult <
        EvmYul.UInt256.size)
    (hNonGas :
      XBlockReplayNonGasReady program target (validJumps target))
    (hNoCallCreate : XBlockReplayNoCallCreate program target)
    (hDoneContinue :
      XTracePathDoneContinuation (validJumps target) targetResult) :
    ∃ evmFuel gasValue evmResult,
      gasValue < EvmYul.UInt256.size ∧
        EvmYul.EVM.X evmFuel (validJumps target)
            (installCodeAndGas target gasValue initial) =
          .ok evmResult ∧
        XResultAgrees targetResult evmResult := by
  let gasBound := XBlockTraceGasBudget program targetFuel initial targetResult
  have hBudget :
      gasBound ≤
        (installCodeAndGas target gasBound initial).gasAvailable.toNat := by
    rw [installCodeAndGas_gasAvailable_toNat hGasBoundFits]
  obtain ⟨fuel, evmResult, hTraceX, hAgree⟩ :=
    blockTraceResult_exists_agrees_of_nonGas_no_call_create_and_budget
      (program := program)
      (target := target)
      (validJumps := validJumps target)
      hTrace hNonGas hNoCallCreate hBudget
      (GasExecRel.installCodeAndGas_of_code_eq hCode)
      hDoneContinue
  exact ⟨fuel.succ, gasBound, evmResult, hGasBoundFits, hTraceX.run, hAgree⟩

theorem blockTraceResult_with_continuation_exists_agrees_of_block_ready
    {program : Program} {target : TargetProgram}
    {validJumps : Array Word} :
    ∀ {targetFuel : Nat} {state : EVMState} {result : StepResult},
      Preservation.BlockTraceResult program target targetFuel state result →
      (∀ {pc : Nat} {instr : Instr}
          {emitted before after : List LocatedTarget}
          {blockState : EVMState} {blockResult : StepResult},
        Program.instrAtPc program blockState.pc.toNat = some (pc, instr) →
          emitInstr? program pc instr = some emitted →
            target.code = before ++ emitted ++ after →
              Target.runListResult (emitted.map LocatedTarget.instr)
                  blockState =
                .ok blockResult →
              XRunListSuffixReady validJumps
                (emitted.map LocatedTarget.instr)) →
      (∀ finalState,
        result = .running finalState →
          ∃ fuel : Nat,
            ∀ fullFinal,
              GasExecRel fullFinal finalState →
                ∃ evmResult,
                  XStepTrace validJumps fuel.succ fullFinal evmResult ∧
                    XResultAgrees result evmResult) →
      ∃ fuel : Nat,
        ∀ full,
          GasExecRel full state →
            ∃ evmResult,
              XStepTrace validJumps fuel.succ full evmResult ∧
                XResultAgrees result evmResult := by
  intro targetFuel state result hTrace
  induction hTrace with
  | done state =>
      intro _hBlockReady hDoneContinue
      exact hDoneContinue state rfl
  | stepRunning hAt hEmit hTargetBlock hRun hRest ih =>
      intro hBlockReady hDoneContinue
      obtain ⟨fuelRest, hRestAll⟩ :=
        ih hBlockReady hDoneContinue
      refine
        runListResult_with_continuation_exists_agrees_of_instr_ready
          (validJumps := validJumps)
          hRun
          ?_
          ?_
          ?_
      · exact hBlockReady hAt hEmit hTargetBlock hRun
      · intro halt hImpossible
        cases hImpossible
      · intro targetFinal hRunning
        cases hRunning
        exact ⟨fuelRest, hRestAll⟩
  | stepHalted hAt hEmit hTargetBlock hRun =>
      intro hBlockReady _hDoneContinue
      refine
        runListResult_with_continuation_exists_agrees_of_instr_ready
          (validJumps := validJumps)
          hRun
          ?_
          ?_
          ?_
      · exact hBlockReady hAt hEmit hTargetBlock hRun
      · intro halt hEq
        cases hEq
        rfl
      · intro targetFinal hImpossible
        cases hImpossible

theorem blockTraceResult_concrete_gas_of_replay_ready
    {program : Program} {target : TargetProgram}
    {targetFuel : Nat} {initial : EVMState} {targetResult : StepResult}
    {gas : Nat}
    (hCode : initial.executionEnv.code = Bytecode.encodeTarget target)
    (hTrace :
      Preservation.BlockTraceResult program target targetFuel initial
        targetResult)
    (hGasFits : gas < EvmYul.UInt256.size)
    (hBlockReady :
      XBlockReplayReady program target (validJumps target))
    (hDoneContinue :
      XTraceDoneContinuation (validJumps target) targetResult) :
    ∃ evmFuel gasValue evmResult,
      gasValue < EvmYul.UInt256.size ∧
        EvmYul.EVM.X evmFuel (validJumps target)
            (installCodeAndGas target gasValue initial) =
          .ok evmResult ∧
        XResultAgrees targetResult evmResult := by
  obtain ⟨fuel, hReplay⟩ :=
    blockTraceResult_with_continuation_exists_agrees_of_block_ready
      (validJumps := validJumps target)
      hTrace hBlockReady hDoneContinue
  obtain ⟨evmResult, hTraceX, hAgree⟩ :=
    hReplay (installCodeAndGas target gas initial)
      (GasExecRel.installCodeAndGas_of_code_eq hCode)
  exact ⟨fuel.succ, gas, evmResult, hGasFits, hTraceX.run, hAgree⟩

end XStepTrace

def XRunsResultSuccessfullyAbove (target : TargetProgram) (initial : EVMState)
    (targetResult : StepResult) (evmFuel gasBound : Nat) : Prop :=
  ∀ gas,
    gasBound ≤ gas →
      gas < EvmYul.UInt256.size →
        ∃ result,
          EvmYul.EVM.X evmFuel (validJumps target)
              (installCodeAndGas target gas initial) =
            .ok result ∧
            XResultAgrees targetResult result

/--
The gas-analysis certificate needed to move from the gasless block trace to
EVMYulLean's gas-aware `X` runner.

This is intentionally an assumption interface, not a trusted constant.  A later
proof can replace a caller-provided value of this structure with a computed
bound derived from the finite block trace and EVMYulLean's gas cost functions.
-/
structure SufficientGasForX
    (target : TargetProgram) (initial sourceFinal : EVMState) where
  evmFuel : Nat
  gasBound : Nat
  gasBoundFits : gasBound < EvmYul.UInt256.size
  runsAboveBound : XRunsSuccessfullyAbove target initial sourceFinal evmFuel gasBound

/--
Alias used at theorem boundaries: these are the explicit gas-aware preconditions
not yet derived from the gasless block trace.
-/
abbrev XPreconditionAssumptions :=
  SufficientGasForX

/--
Result-level gas-analysis certificate for the theorem path whose source
semantics can halt.  This is the explicit gas/resource boundary for connecting
the gasless result trace to EVMYulLean's gas-aware `X` runner.
-/
structure SufficientGasForXResult
    (target : TargetProgram) (initial : EVMState)
    (targetResult : StepResult) where
  evmFuel : Nat
  gasBound : Nat
  gasBoundFits : gasBound < EvmYul.UInt256.size
  runsAboveBound :
    XRunsResultSuccessfullyAbove target initial targetResult evmFuel gasBound

abbrev XResultPreconditionAssumptions :=
  SufficientGasForXResult

def ConcreteGasForXResult
    (target : TargetProgram) (initial : EVMState)
    (targetResult : StepResult) : Prop :=
  ∃ evmFuel gas result,
    gas < EvmYul.UInt256.size ∧
      EvmYul.EVM.X evmFuel (validJumps target)
          (installCodeAndGas target gas initial) =
        .ok result ∧
      XResultAgrees targetResult result

abbrev XResultConcreteWitness :=
  ConcreteGasForXResult

structure XConcretePathForResult
    (target : TargetProgram) (initial : EVMState)
    (targetResult : StepResult) where
  evmFuel : Nat
  gas : Nat
  result : EvmYul.EVM.ExecutionResult EVMState
  gasFits : gas < EvmYul.UInt256.size
  path :
    XStepTrace (validJumps target) evmFuel
      (installCodeAndGas target gas initial) result
  agrees : XResultAgrees targetResult result

theorem XConcretePathForResult.toConcrete {target : TargetProgram}
    {initial : EVMState} {targetResult : StepResult}
    (hPath : XConcretePathForResult target initial targetResult) :
    ConcreteGasForXResult target initial targetResult := by
  exact
    ⟨hPath.evmFuel, hPath.gas, hPath.result, hPath.gasFits,
      hPath.path.run, hPath.agrees⟩

theorem SufficientGasForX.runsAtGasBound {target : TargetProgram}
    {initial sourceFinal : EVMState}
    (hGasForX : SufficientGasForX target initial sourceFinal) :
    ∃ result,
      EvmYul.EVM.X hGasForX.evmFuel (validJumps target)
          (installCodeAndGas target hGasForX.gasBound initial) =
        .ok result ∧
      XSuccessErasesTo sourceFinal result :=
  hGasForX.runsAboveBound hGasForX.gasBound (Nat.le_refl _)
    hGasForX.gasBoundFits

theorem SufficientGasForX.exists_concrete_gas {target : TargetProgram}
    {initial sourceFinal : EVMState}
    (hGasForX : SufficientGasForX target initial sourceFinal) :
    ∃ evmFuel gas result,
      gas < EvmYul.UInt256.size ∧
        EvmYul.EVM.X evmFuel (validJumps target)
            (installCodeAndGas target gas initial) =
          .ok result ∧
        XSuccessErasesTo sourceFinal result := by
  obtain ⟨result, hRun, hAgrees⟩ := hGasForX.runsAtGasBound
  exact
    ⟨hGasForX.evmFuel, hGasForX.gasBound, result,
      hGasForX.gasBoundFits, hRun, hAgrees⟩

theorem SufficientGasForXResult.runsAtGasBound {target : TargetProgram}
    {initial : EVMState} {targetResult : StepResult}
    (hGasForX : SufficientGasForXResult target initial targetResult) :
    ∃ result,
      EvmYul.EVM.X hGasForX.evmFuel (validJumps target)
          (installCodeAndGas target hGasForX.gasBound initial) =
        .ok result ∧
      XResultAgrees targetResult result :=
  hGasForX.runsAboveBound hGasForX.gasBound (Nat.le_refl _)
    hGasForX.gasBoundFits

theorem SufficientGasForXResult.exists_concrete_gas {target : TargetProgram}
    {initial : EVMState} {targetResult : StepResult}
    (hGasForX : SufficientGasForXResult target initial targetResult) :
    ∃ evmFuel gas result,
      gas < EvmYul.UInt256.size ∧
        EvmYul.EVM.X evmFuel (validJumps target)
            (installCodeAndGas target gas initial) =
          .ok result ∧
        XResultAgrees targetResult result := by
  obtain ⟨result, hRun, hAgrees⟩ := hGasForX.runsAtGasBound
  exact
    ⟨hGasForX.evmFuel, hGasForX.gasBound, result,
      hGasForX.gasBoundFits, hRun, hAgrees⟩

theorem SufficientGasForXResult.toConcrete {target : TargetProgram}
    {initial : EVMState} {targetResult : StepResult}
    (hGasForX : SufficientGasForXResult target initial targetResult) :
    ConcreteGasForXResult target initial targetResult :=
  hGasForX.exists_concrete_gas

theorem SufficientGasForXResult.runsAtInstalledGas {target : TargetProgram}
    {initial : EVMState} {targetResult : StepResult} {gas : Nat}
    (hGasForX :
      SufficientGasForXResult target (installCodeAndGas target gas initial)
        targetResult)
    (hGas : hGasForX.gasBound ≤ gas)
    (hUInt256 : gas < EvmYul.UInt256.size) :
    ∃ result,
      EvmYul.EVM.X hGasForX.evmFuel (validJumps target)
          (installCodeAndGas target gas initial) =
        .ok result ∧
      XResultAgrees targetResult result := by
  simpa [installCodeAndGas_idempotent] using
    hGasForX.runsAboveBound gas hGas hUInt256

theorem XRunsSuccessfullyAbove.not_out_of_gas {target : TargetProgram}
    {initial sourceFinal : EVMState} {evmFuel gasBound gas : Nat}
    (hRuns : XRunsSuccessfullyAbove target initial sourceFinal evmFuel gasBound)
    (hGas : gasBound ≤ gas)
    (hUInt256 : gas < EvmYul.UInt256.size) :
    EvmYul.EVM.X evmFuel (validJumps target)
        (installCodeAndGas target gas initial) ≠
      .error EvmYul.EVM.ExecutionException.OutOfGass := by
  obtain ⟨result, hRun, _hProject⟩ := hRuns gas hGas hUInt256
  rw [hRun]
  intro hImpossible
  cases hImpossible

theorem XRunsResultSuccessfullyAbove.not_out_of_gas {target : TargetProgram}
    {initial : EVMState} {targetResult : StepResult}
    {evmFuel gasBound gas : Nat}
    (hRuns :
      XRunsResultSuccessfullyAbove target initial targetResult evmFuel
        gasBound)
    (hGas : gasBound ≤ gas)
    (hUInt256 : gas < EvmYul.UInt256.size) :
    EvmYul.EVM.X evmFuel (validJumps target)
        (installCodeAndGas target gas initial) ≠
      .error EvmYul.EVM.ExecutionException.OutOfGass := by
  obtain ⟨result, hRun, _hProject⟩ := hRuns gas hGas hUInt256
  rw [hRun]
  intro hImpossible
  cases hImpossible

/--
Reusable package produced by the gas-aware bridge theorem.

Higher compiler layers should depend on this structure rather than destructing
large conjunctions: it names the bytecode facts, runtime-boundary facts,
gasless block trace, and sufficient-gas `X` behavior that the bridge provides.
-/
structure XBridgeCertificate
    (program : Program) (target : TargetProgram) (fuel : Nat)
    (initial sourceFinal : EVMState) : Prop where
  accepted : Accepted program
  compileBytes_eq : Bytecode.compileBytes? program = some (Bytecode.encodeTarget target)
  encodingCorrect : Bytecode.EncodingCorrect target (Bytecode.encodeTarget target)
  outOfGasPolicy : OutOfGasPolicyAssumption program initial
  currentContractProjection : CurrentContractProjectionAssumption program initial
  externalInteraction : ExternalInteractionAssumption program target initial
  blockTrace :
    ∃ targetFinal,
      Preservation.BlockTrace program target fuel initial targetFinal ∧
        eraseGas targetFinal = eraseGas sourceFinal
  sufficientGas :
    ∃ evmFuel gasBound,
      gasBound < EvmYul.UInt256.size ∧
      XRunsSuccessfullyAbove target initial sourceFinal evmFuel gasBound

namespace XBridgeCertificate

theorem exists_sufficient_gas {program : Program} {target : TargetProgram}
    {fuel : Nat} {initial sourceFinal : EVMState}
    (cert : XBridgeCertificate program target fuel initial sourceFinal) :
    ∃ evmFuel gasBound,
      gasBound < EvmYul.UInt256.size ∧
      ∀ gas,
        gasBound ≤ gas →
        gas < EvmYul.UInt256.size →
            ∃ result,
              EvmYul.EVM.X evmFuel (validJumps target)
                  (installCodeAndGas target gas initial) =
                .ok result ∧
                XSuccessErasesTo sourceFinal result :=
  cert.sufficientGas

theorem exists_concrete_gas {program : Program}
    {target : TargetProgram} {fuel : Nat} {initial sourceFinal : EVMState}
    (cert : XBridgeCertificate program target fuel initial sourceFinal) :
    ∃ evmFuel gas result,
      gas < EvmYul.UInt256.size ∧
        EvmYul.EVM.X evmFuel (validJumps target)
            (installCodeAndGas target gas initial) =
          .ok result ∧
        XSuccessErasesTo sourceFinal result := by
  obtain ⟨evmFuel, gasBound, hFits, hRuns⟩ := cert.sufficientGas
  obtain ⟨result, hRun, hAgrees⟩ := hRuns gasBound (Nat.le_refl _) hFits
  exact ⟨evmFuel, gasBound, result, hFits, hRun, hAgrees⟩

theorem not_out_of_gas_above_bound {program : Program} {target : TargetProgram}
    {fuel : Nat} {initial sourceFinal : EVMState}
    (cert : XBridgeCertificate program target fuel initial sourceFinal) :
    ∃ evmFuel gasBound,
      gasBound < EvmYul.UInt256.size ∧
      ∀ gas,
        gasBound ≤ gas →
        gas < EvmYul.UInt256.size →
            EvmYul.EVM.X evmFuel (validJumps target)
                (installCodeAndGas target gas initial) ≠
              .error EvmYul.EVM.ExecutionException.OutOfGass := by
  obtain ⟨evmFuel, gasBound, hFits, hRuns⟩ := cert.sufficientGas
  exact
    ⟨evmFuel, gasBound, hFits, fun gas hGas hUInt256 =>
      hRuns.not_out_of_gas hGas hUInt256⟩

end XBridgeCertificate

/--
Primary gas-aware bridge theorem.

This theorem packages the existing compiler-correctness theorem together with
the explicit `XPreconditionAssumptions` certificate into a single named
artifact for higher compiler layers.
-/
theorem compile_whole_program_X_bridge {program : Program}
    {target : TargetProgram} {fuel : Nat} {initial sourceFinal : EVMState}
    (hCompile : compile? program = some target)
    (hRuntime : RuntimeAssumptions program target initial)
    (hRun : Source.runN program fuel initial = .ok sourceFinal)
    (hPreconditions : XPreconditionAssumptions target initial sourceFinal) :
    XBridgeCertificate program target fuel initial sourceFinal := by
  obtain
    ⟨hAccepted, hBytes, hEncoding, hOutOfGas, hProjection,
      targetFinal, hTrace, hErase⟩ :=
    compile_whole_program_sound hCompile hRuntime hRun
  exact
    { accepted := hAccepted
      compileBytes_eq := hBytes
      encodingCorrect := hEncoding
      outOfGasPolicy := hOutOfGas
      currentContractProjection := hProjection
      externalInteraction := hRuntime.externalInteraction
      blockTrace := ⟨targetFinal, hTrace, hErase⟩
      sufficientGas :=
        ⟨hPreconditions.evmFuel, hPreconditions.gasBound,
          hPreconditions.gasBoundFits,
          hPreconditions.runsAboveBound⟩ }

/--
Gas-aware whole-program bridge to EVMYulLean `X`.

The compiler proof supplies the accepted-program, bytecode, and gas-erased
block-trace facts.  `SufficientGasForX` supplies the remaining gas-aware runner
analysis: an EVM fuel amount and a gas bound such that every larger UInt256 gas
input makes `X` return successfully and project to the same non-gas result.
-/
theorem compile_whole_program_X_sufficient_gas {program : Program}
    {target : TargetProgram} {fuel : Nat} {initial sourceFinal : EVMState}
    (hCompile : compile? program = some target)
    (hRuntime : RuntimeAssumptions program target initial)
    (hRun : Source.runN program fuel initial = .ok sourceFinal)
    (hSufficientGas : SufficientGasForX target initial sourceFinal) :
    Accepted program ∧
      Bytecode.EncodingCorrect target (Bytecode.encodeTarget target) ∧
        ∃ targetFinal evmFuel gasBound,
          Preservation.BlockTrace program target fuel initial targetFinal ∧
            eraseGas targetFinal = eraseGas sourceFinal ∧
              gasBound < EvmYul.UInt256.size ∧
              XRunsSuccessfullyAbove target initial sourceFinal evmFuel gasBound ∧
                ∀ gas,
                  gasBound ≤ gas →
                  gas < EvmYul.UInt256.size →
                      EvmYul.EVM.X evmFuel (validJumps target)
                          (installCodeAndGas target gas initial) ≠
                        .error EvmYul.EVM.ExecutionException.OutOfGass := by
  let cert :=
    compile_whole_program_X_bridge hCompile hRuntime hRun hSufficientGas
  obtain ⟨targetFinal, hTrace, hErase⟩ := cert.blockTrace
  obtain ⟨evmFuel, gasBound, hFits, hRuns⟩ := cert.sufficientGas
  refine
    ⟨cert.accepted, cert.encodingCorrect, targetFinal, evmFuel,
      gasBound, hTrace, hErase, hFits, hRuns, ?_⟩
  intro gas hGas hUInt256
  exact hRuns.not_out_of_gas hGas hUInt256

/--
Direct existential sufficient-gas statement for EVMYulLean `X`.

Under the bytecode/runtime assumptions and the explicit gas-aware `X`
preconditions, successful source execution implies that there is an EVM fuel
and gas bound such that every larger UInt256 gas input makes `X` return
successfully and preserve the gas-erased final state.
-/
theorem compile_whole_program_X_exists_sufficient_gas {program : Program}
    {target : TargetProgram} {fuel : Nat} {initial sourceFinal : EVMState}
    (hCompile : compile? program = some target)
    (hRuntime : RuntimeAssumptions program target initial)
    (hRun : Source.runN program fuel initial = .ok sourceFinal)
    (hPreconditions : XPreconditionAssumptions target initial sourceFinal) :
    Accepted program ∧
      Bytecode.EncodingCorrect target (Bytecode.encodeTarget target) ∧
        ∃ evmFuel gasBound,
          gasBound < EvmYul.UInt256.size ∧
          ∀ gas,
            gasBound ≤ gas →
              gas < EvmYul.UInt256.size →
                ∃ result,
                  EvmYul.EVM.X evmFuel (validJumps target)
                      (installCodeAndGas target gas initial) =
                    .ok result ∧
                    XSuccessErasesTo sourceFinal result := by
  let cert := compile_whole_program_X_bridge hCompile hRuntime hRun hPreconditions
  obtain ⟨evmFuel, gasBound, hFits, hRuns⟩ := cert.exists_sufficient_gas
  exact ⟨cert.accepted, cert.encodingCorrect, evmFuel, gasBound, hFits, hRuns⟩

/--
No-out-of-gas corollary for callers that only need the gas safety part of the
`X` bridge.  The stronger theorem above additionally returns a successful
`ExecutionResult` with the gas-erased projection.
-/
theorem compile_whole_program_X_no_out_of_gas_above_bound {program : Program}
    {target : TargetProgram} {fuel : Nat} {initial sourceFinal : EVMState}
    (hCompile : compile? program = some target)
    (hRuntime : RuntimeAssumptions program target initial)
    (hRun : Source.runN program fuel initial = .ok sourceFinal)
    (hPreconditions : XPreconditionAssumptions target initial sourceFinal) :
    Accepted program ∧
      Bytecode.EncodingCorrect target (Bytecode.encodeTarget target) ∧
        ∃ evmFuel gasBound,
          gasBound < EvmYul.UInt256.size ∧
          ∀ gas,
            gasBound ≤ gas →
              gas < EvmYul.UInt256.size →
                EvmYul.EVM.X evmFuel (validJumps target)
                    (installCodeAndGas target gas initial) ≠
                  .error EvmYul.EVM.ExecutionException.OutOfGass := by
  let cert := compile_whole_program_X_bridge hCompile hRuntime hRun hPreconditions
  obtain ⟨evmFuel, gasBound, hFits, hNoOutOfGas⟩ :=
    cert.not_out_of_gas_above_bound
  exact
    ⟨cert.accepted, cert.encodingCorrect, evmFuel, gasBound, hFits,
      hNoOutOfGas⟩

end GasAware

end Assembly
end EvmCompiler
