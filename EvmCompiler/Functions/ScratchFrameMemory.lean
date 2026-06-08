import EvmCompiler.Functions.ScratchFrameSpill
import EvmCompiler.Locals.SourceLowering

/-!
Semantic memory adapters for the scratch-frame stack-too-deep fallback.

`ScratchFrameSpill` computes frame addresses as a hidden base word plus a
compiler slot offset.  The older locals spill proof already has strong memory
facts for `ScratchRange.word`; this module pins the arithmetic bridge so future
scratch-frame preservation proofs can reuse those facts against the actual
generated address expression.
-/

namespace EvmCompiler
namespace Functions
namespace ScratchFrameSpill

namespace FrameMemory

abbrev ScratchRange :=
  Locals.SourceLowering.StateRel.SpillScratch.ScratchRange

abbrev ScratchRegionReady :=
  Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady

abbrev ZeroPaddingSpec :=
  Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec

abbrev WordByteEncodingSpec :=
  Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec

def range (base : Word) (words : Nat) : ScratchRange :=
  { base := base.toNat, words := words }

def preallocMachineFromBase (base : Word) (words : Nat)
    (machine : EvmYul.MachineState) : EvmYul.MachineState :=
  match words with
  | 0 => machine
  | slot + 1 => machine.mstore (base + slotOffset slot) zeroWord

def frameBumpMachine (words : Nat)
    (machine : EvmYul.MachineState) : EvmYul.MachineState :=
  let loaded := machine.mload freePtrWord
  loaded.2.mstore freePtrWord (loaded.1 + frameBytes words)

def frameInitMachine (words : Nat)
    (machine : EvmYul.MachineState) : EvmYul.MachineState :=
  let loaded := machine.mload freePtrWord
  preallocMachineFromBase loaded.1 words (frameBumpMachine words machine)

private theorem word_add_comm (left right : Word) :
    left + right = right + left := by
  cases left with
  | mk leftVal =>
      cases right with
      | mk rightVal =>
          change EvmYul.UInt256.mk (leftVal + rightVal) =
            EvmYul.UInt256.mk (rightVal + leftVal)
          rw [add_comm]

theorem frameBytes_eq_slotOffset (words : Nat) :
    frameBytes words = slotOffset words := rfl

theorem frameEndAddress_eq_base_add_frameBytes
    (base : Word) (words : Nat) :
    base + frameBytes words =
      EvmYul.UInt256.ofNat (base.toNat + 32 * words) := by
  change
    base + EvmYul.UInt256.ofNat (32 * words) =
      EvmYul.UInt256.ofNat (base.toNat + 32 * words)
  have hBaseWord : EvmYul.UInt256.ofNat base.toNat = base :=
    Locals.SourceLowering.StateRel.SpillScratch.word_ofNat_toNat base
  conv_lhs => rw [← hBaseWord]
  rw [Assembly.UInt256_ofNat_add]

theorem generatedAddress_eq_range_word
    (base : Word) (words slot : Nat) :
    base + slotOffset slot = (range base words).word slot := by
  change
    base + EvmYul.UInt256.ofNat (32 * slot) =
      EvmYul.UInt256.ofNat (base.toNat + 32 * slot)
  have hBaseWord : EvmYul.UInt256.ofNat base.toNat = base :=
    Locals.SourceLowering.StateRel.SpillScratch.word_ofNat_toNat base
  conv_lhs => rw [← hBaseWord]
  rw [Assembly.UInt256_ofNat_add]

theorem preallocMachineFromBase_eq_preallocMachine
    (base : Word) (words : Nat) (machine : EvmYul.MachineState) :
    preallocMachineFromBase base words machine =
      (range base words).preallocMachine machine := by
  cases words with
  | zero =>
      rfl
  | succ slot =>
      change
        machine.mstore (base + slotOffset slot) zeroWord =
          machine.mstore ((range base (slot + 1)).word slot)
            (EvmYul.UInt256.ofNat 0)
      rw [generatedAddress_eq_range_word base (slot + 1) slot]
      rfl

theorem preallocMachineFromBase_ready_succ
    (hSpec : ZeroPaddingSpec)
    (hWordBytes : WordByteEncodingSpec)
    {machine : EvmYul.MachineState} {base : Word} {slot : Nat}
    (hOffsetLtUInt :
      base.toNat + 32 * slot < EvmYul.UInt256.size)
    (hPadNoOverflow :
      base.toNat + 32 * slot - machine.memory.size < USize.size)
    (hWithinAfter :
      base.toNat + 32 * (slot + 1) ≤
        EvmYul.MachineState.M machine.activeWords.toNat
          (base.toNat + 32 * slot) 32 * 32)
    (hActiveAfter :
      EvmYul.MachineState.M machine.activeWords.toNat
          (base.toNat + 32 * slot) 32 * 32 <
        EvmYul.UInt256.size) :
    ScratchRegionReady
      (preallocMachineFromBase base (slot + 1) machine)
      (range base (slot + 1)).base
      (range base (slot + 1)).words := by
  let offset : Word := base + slotOffset slot
  have hOffsetToNat :
      offset.toNat = base.toNat + 32 * slot := by
    simp [offset, generatedAddress_eq_range_word base (slot + 1) slot,
      range, Locals.SourceLowering.StateRel.SpillScratch.ScratchRange.word,
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRange.slot,
      EvmYul.UInt256.toNat_ofNat_of_lt hOffsetLtUInt]
  have hMemorySize :
      (machine.mstore offset zeroWord).memory.size =
        max machine.memory.size (base.toNat + 32 * slot + 32) := by
    have hWriteSize :
        (zeroWord.toByteArray.write 0 machine.memory offset.toNat 32).size =
          max machine.memory.size (offset.toNat + 32) :=
      Locals.SourceLowering.StateRel.SpillScratch.byteArray_write32_size_general
        hSpec (hWordBytes zeroWord) (by
          simpa [hOffsetToNat] using hPadNoOverflow)
    simpa [EvmYul.MachineState.mstore, EvmYul.MachineState.writeWord,
      EvmYul.writeBytes, hOffsetToNat, zeroWord] using hWriteSize
  have hMLtUInt :
      EvmYul.MachineState.M machine.activeWords.toNat
          (base.toNat + 32 * slot) 32 <
        EvmYul.UInt256.size := by
    have hPos : 0 < (32 : Nat) := by decide
    omega
  have hActiveWordsToNat :
      (machine.mstore offset zeroWord).activeWords.toNat =
        EvmYul.MachineState.M machine.activeWords.toNat
          (base.toNat + 32 * slot) 32 := by
    change
      (EvmYul.UInt256.ofNat
          (EvmYul.MachineState.M machine.activeWords.toNat
            offset.toNat 32)).toNat =
        EvmYul.MachineState.M machine.activeWords.toNat
          (base.toNat + 32 * slot) 32
    rw [hOffsetToNat]
    exact EvmYul.UInt256.toNat_ofNat_of_lt hMLtUInt
  change
    ScratchRegionReady
      (machine.mstore (base + slotOffset slot) zeroWord)
      base.toNat (slot + 1)
  exact
    { allocated := by
        unfold Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionAllocatedNat
        simp [offset, hMemorySize]
        omega
      withinActive := by
        unfold Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionWithinActiveNat
        simp [offset, hActiveWordsToNat]
        exact hWithinAfter
      activeNoOverflow := by
        unfold Locals.SourceLowering.StateRel.SpillScratch.ScratchActiveBytesNoOverflow
        simp [offset, hActiveWordsToNat]
        exact hActiveAfter }

theorem run_frameBumpCode (state : EVMState) (words : Nat) :
    ∃ final,
      Structured.Code.run (frameBumpCode words) state = .ok final ∧
      final.stack =
        (state.toMachineState.mload freePtrWord).1 :: state.stack ∧
      final.toMachineState =
        frameBumpMachine words state.toMachineState := by
  let loaded : Word × EvmYul.MachineState :=
    state.toMachineState.mload freePtrWord
  let newFree : Word := loaded.1 + frameBytes words
  let state1 : EVMState :=
    state.replaceStackAndIncrPC (freePtrWord :: state.stack) (pcΔ := 33)
  let state2 : EVMState :=
    ({ state1 with toMachineState := loaded.2 } :
      EVMState).replaceStackAndIncrPC (loaded.1 :: state.stack)
  let state3 : EVMState :=
    state2.replaceStackAndIncrPC (loaded.1 :: loaded.1 :: state.stack)
  let state4 : EVMState :=
    state3.replaceStackAndIncrPC
      (frameBytes words :: loaded.1 :: loaded.1 :: state.stack)
      (pcΔ := 33)
  let state5 : EVMState :=
    state4.replaceStackAndIncrPC (newFree :: loaded.1 :: state.stack)
  let state6 : EVMState :=
    state5.replaceStackAndIncrPC
      (freePtrWord :: newFree :: loaded.1 :: state.stack) (pcΔ := 33)
  let final : EVMState :=
    ({ state6 with
      toMachineState := loaded.2.mstore freePtrWord newFree } :
      EVMState).replaceStackAndIncrPC (loaded.1 :: state.stack)
  refine ⟨final, ?_, ?_, ?_⟩
  · simp [frameBumpCode, Structured.Code.run, Structured.BasicInstr.step,
      Structured.BasicOp.step, Structured.BasicOp.toPrimOp,
      Assembly.Target.stepInstr, Assembly.PrimOp.step,
      Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
      EvmYul.EVM.execBinOp, EvmYul.EVM.binaryMachineStateOp,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, EvmYul.Stack.push, EvmYul.Stack.pop,
      EvmYul.Stack.pop2, EvmYul.dup, Id.run, loaded, newFree, state1,
      state2, state3, state4, state5, state6, final]
    rw [word_add_comm]
    rfl
  · cases state
    simp [EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, loaded, newFree, state1, state2, state3,
      state4, state5, state6, final]
  · cases state
    simp [frameBumpMachine, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, loaded, newFree, state1, state2, state3,
      state4, state5, state6, final]

theorem run_framePreallocCode (state : EVMState)
    (base : Word) (rest : EvmYul.Stack Word) (words : Nat) :
    ∃ final,
      Structured.Code.run (framePreallocCode words)
        { state with stack := base :: rest } = .ok final ∧
      final.stack = base :: rest ∧
      final.toMachineState =
        preallocMachineFromBase base words state.toMachineState := by
  cases words with
  | zero =>
      exact
        ⟨{ state with stack := base :: rest },
          by simp [framePreallocCode, Structured.Code.run],
          rfl, rfl⟩
  | succ slot =>
      let start : EVMState := { state with stack := base :: rest }
      let state1 : EVMState :=
        start.replaceStackAndIncrPC (zeroWord :: base :: rest) (pcΔ := 33)
      let state2 : EVMState :=
        state1.replaceStackAndIncrPC (base :: zeroWord :: base :: rest)
      let state3 : EVMState :=
        state2.replaceStackAndIncrPC
          (slotOffset slot :: base :: zeroWord :: base :: rest)
          (pcΔ := 33)
      let addr : Word := base + slotOffset slot
      let state4 : EVMState :=
        state3.replaceStackAndIncrPC (addr :: zeroWord :: base :: rest)
      let final : EVMState :=
        ({ state4 with
          toMachineState := state.toMachineState.mstore addr zeroWord } :
          EVMState).replaceStackAndIncrPC (base :: rest)
      refine ⟨final, ?_, ?_, ?_⟩
      · simp [framePreallocCode, Structured.Code.run,
          Structured.BasicInstr.step, Structured.BasicOp.step,
          Structured.BasicOp.toPrimOp, Assembly.Target.stepInstr,
          Assembly.PrimOp.step, Assembly.PrimOp.continuingStep?,
          Assembly.PrimStep.run, EvmYul.EVM.execBinOp,
          EvmYul.EVM.binaryMachineStateOp,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, EvmYul.Stack.push,
          EvmYul.Stack.pop2, EvmYul.dup, Id.run,
          start, state1, state2, state3, state4, addr, final]
        rw [word_add_comm]
        rfl
      · cases state
        simp [EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, start, state1, state2, state3, state4,
          addr, final]
      · cases state
        simp [preallocMachineFromBase,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, start, state1, state2, state3, state4,
          addr, final]

theorem run_frameInitCode (state : EVMState) (words : Nat) :
    ∃ final,
      Structured.Code.run (frameInitCode words) state = .ok final ∧
      final.stack =
        (state.toMachineState.mload freePtrWord).1 :: state.stack ∧
      final.toMachineState =
        frameInitMachine words state.toMachineState := by
  rcases run_frameBumpCode state words with
    ⟨mid, hBumpRun, hMidStack, hMidMachine⟩
  let base : Word := (state.toMachineState.mload freePtrWord).1
  rcases run_framePreallocCode mid base state.stack words with
    ⟨final, hPreallocRun, hFinalStack, hFinalMachine⟩
  have hMidUpdate : ({ mid with stack := base :: state.stack } : EVMState) = mid := by
    cases mid
    simp [base] at hMidStack ⊢
    exact hMidStack.symm
  refine ⟨final, ?_, ?_, ?_⟩
  · rw [frameInitCode, Structured.Preservation.Code.run_append, hBumpRun]
    simpa [hMidUpdate] using hPreallocRun
  · exact hFinalStack
  · rw [hFinalMachine, hMidMachine]
    rfl

theorem frameInitMachine_ready_succ
    (hSpec : ZeroPaddingSpec)
    (hWordBytes : WordByteEncodingSpec)
    {machine : EvmYul.MachineState} {slot : Nat}
    (hOffsetLtUInt :
      (machine.mload freePtrWord).1.toNat + 32 * slot <
        EvmYul.UInt256.size)
    (hPadNoOverflow :
      (machine.mload freePtrWord).1.toNat + 32 * slot -
          (frameBumpMachine (slot + 1) machine).memory.size <
        USize.size)
    (hWithinAfter :
      (machine.mload freePtrWord).1.toNat + 32 * (slot + 1) ≤
        EvmYul.MachineState.M
          (frameBumpMachine (slot + 1) machine).activeWords.toNat
          ((machine.mload freePtrWord).1.toNat + 32 * slot) 32 * 32)
    (hActiveAfter :
      EvmYul.MachineState.M
          (frameBumpMachine (slot + 1) machine).activeWords.toNat
          ((machine.mload freePtrWord).1.toNat + 32 * slot) 32 * 32 <
        EvmYul.UInt256.size) :
    ScratchRegionReady
      (frameInitMachine (slot + 1) machine)
      (range (machine.mload freePtrWord).1 (slot + 1)).base
      (range (machine.mload freePtrWord).1 (slot + 1)).words := by
  simpa [frameInitMachine] using
    preallocMachineFromBase_ready_succ hSpec hWordBytes
      (machine := frameBumpMachine (slot + 1) machine)
      (base := (machine.mload freePtrWord).1)
      (slot := slot)
      hOffsetLtUInt hPadNoOverflow hWithinAfter hActiveAfter

theorem run_frameInitCode_ready_succ
    (hSpec : ZeroPaddingSpec)
    (hWordBytes : WordByteEncodingSpec)
    (state : EVMState) (slot : Nat)
    (hOffsetLtUInt :
      (state.toMachineState.mload freePtrWord).1.toNat + 32 * slot <
        EvmYul.UInt256.size)
    (hPadNoOverflow :
      (state.toMachineState.mload freePtrWord).1.toNat + 32 * slot -
          (frameBumpMachine (slot + 1) state.toMachineState).memory.size <
        USize.size)
    (hWithinAfter :
      (state.toMachineState.mload freePtrWord).1.toNat +
          32 * (slot + 1) ≤
        EvmYul.MachineState.M
          (frameBumpMachine (slot + 1)
            state.toMachineState).activeWords.toNat
          ((state.toMachineState.mload freePtrWord).1.toNat +
            32 * slot) 32 * 32)
    (hActiveAfter :
      EvmYul.MachineState.M
          (frameBumpMachine (slot + 1)
            state.toMachineState).activeWords.toNat
          ((state.toMachineState.mload freePtrWord).1.toNat +
            32 * slot) 32 * 32 <
        EvmYul.UInt256.size) :
    ∃ final,
      Structured.Code.run (frameInitCode (slot + 1)) state = .ok final ∧
      final.stack =
        (state.toMachineState.mload freePtrWord).1 :: state.stack ∧
      final.toMachineState =
        frameInitMachine (slot + 1) state.toMachineState ∧
      ScratchRegionReady final.toMachineState
        (range (state.toMachineState.mload freePtrWord).1
          (slot + 1)).base
        (range (state.toMachineState.mload freePtrWord).1
          (slot + 1)).words := by
  rcases run_frameInitCode state (slot + 1) with
    ⟨final, hRun, hStack, hMachine⟩
  refine ⟨final, hRun, hStack, hMachine, ?_⟩
  rw [hMachine]
  exact
    frameInitMachine_ready_succ hSpec hWordBytes
      hOffsetLtUInt hPadNoOverflow hWithinAfter hActiveAfter

theorem run_dupCode?_copyBase
    {depth : Nat} {code : Structured.Code}
    (hCode : dupCode? depth = some code)
    (state : EVMState) (front rest : EvmYul.Stack Word) (base : Word)
    (hDepth : depth = front.length + 1) :
    ∃ final,
      Structured.Code.run code
          { state with stack := front ++ base :: rest } = .ok final ∧
      final.stack = base :: front ++ base :: rest ∧
      final.toMachineState = state.toMachineState := by
  subst depth
  rcases dupCode?_eq_some_inv hCode with ⟨op, hDup, rfl⟩
  let start : EVMState := { state with stack := front ++ base :: rest }
  let final : EVMState :=
    start.replaceStackAndIncrPC (base :: front ++ base :: rest)
  have hStackAt : start.stack[front.length]? = some base := by
    simp [start]
  have hBounds :=
    Locals.SourceLowering.StateRel.SpillScratch.stackOp_dup?_some_bound hDup
  rcases Locals.Direct.stackOp_dup?_step_eq_dup
      (n := front.length + 1) hBounds.1 hBounds.2 start with
    ⟨derivedOp, hDerivedDup, hDerivedStep⟩
  rw [hDup] at hDerivedDup
  cases hDerivedDup
  have hDupValue :
      EvmYul.dup (front.length + 1) start = .ok final := by
    have hDupValue' :=
      Locals.Direct.evm_dup_succ_get? (state := start)
        (idx := front.length) hStackAt
    simpa [final, start] using hDupValue'
  have hOpStep :
      Structured.BasicOp.step op start = .ok final := by
    rw [hDerivedStep, hDupValue]
  have hRun :
      Structured.Code.run [Structured.BasicInstr.op op] start =
        .ok final := by
    simp [Structured.Code.run, Structured.BasicInstr.step, hOpStep]
  refine ⟨final, ?_, ?_, ?_⟩
  · simpa [start] using hRun
  · simp [final, start, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC]
  · cases state
    simp [final, start, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC]

theorem run_slotAddressCode?
    {valuesAboveBase slot : Nat} {code : Structured.Code}
    (hCode : slotAddressCode? valuesAboveBase slot = some code)
    (state : EVMState) (values rest : EvmYul.Stack Word) (base : Word)
    (hValues : values.length = valuesAboveBase) :
    ∃ final,
      Structured.Code.run code
          { state with stack := values ++ base :: rest } = .ok final ∧
      final.stack = (base + slotOffset slot) :: values ++ base :: rest ∧
      final.toMachineState = state.toMachineState := by
  rcases slotAddressCode?_eq_some_inv hCode with
    ⟨dup, hDup, hCodeEq⟩
  rcases run_dupCode?_copyBase hDup state values rest base
      (by omega) with
    ⟨mid, hDupRun, hMidStack, hMidMachine⟩
  let offset : Word := slotOffset slot
  let addr : Word := base + offset
  let state1 : EVMState :=
    mid.replaceStackAndIncrPC (offset :: base :: values ++ base :: rest)
      (pcΔ := 33)
  let final : EVMState :=
    state1.replaceStackAndIncrPC (addr :: values ++ base :: rest)
  have hTailRun :
      Structured.Code.run
          [Structured.BasicInstr.push offset,
            Structured.BasicInstr.op .add] mid = .ok final := by
    simp [Structured.Code.run, Structured.BasicInstr.step,
      Structured.BasicOp.step, Structured.BasicOp.toPrimOp,
      Assembly.Target.stepInstr, Assembly.PrimOp.step,
      Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
      EvmYul.EVM.execBinOp,
      EvmYul.EVM.State.replaceStackAndIncrPC, EvmYul.EVM.State.incrPC,
      EvmYul.Stack.push, EvmYul.Stack.pop2, Id.run,
      hMidStack, offset, addr, state1, final]
    rw [word_add_comm]
    rfl
  refine ⟨final, ?_, ?_, ?_⟩
  · rw [hCodeEq, Structured.Preservation.Code.run_append, hDupRun]
    simpa [offset] using hTailRun
  · simp [final, state1, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, addr, offset]
  · simpa [final, state1, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, addr, offset] using hMidMachine

theorem run_loadSlotCode?
    {valuesAboveBase slot : Nat} {code : Structured.Code}
    (hCode : loadSlotCode? valuesAboveBase slot = some code)
    (state : EVMState) (values rest : EvmYul.Stack Word) (base : Word)
    (hValues : values.length = valuesAboveBase) :
    ∃ final,
      Structured.Code.run code
          { state with stack := values ++ base :: rest } = .ok final ∧
      final.stack =
        (state.toMachineState.mload (base + slotOffset slot)).1 ::
          values ++ base :: rest ∧
      final.toMachineState =
        (state.toMachineState.mload (base + slotOffset slot)).2 := by
  rcases loadSlotCode?_eq_some_inv hCode with
    ⟨addrCode, hAddrCode, hCodeEq⟩
  rcases run_slotAddressCode? hAddrCode state values rest base hValues with
    ⟨addrState, hAddrRun, hAddrStack, hAddrMachine⟩
  let addr : Word := base + slotOffset slot
  let loaded : Word × EvmYul.MachineState :=
    state.toMachineState.mload addr
  let final : EVMState :=
    ({ addrState with toMachineState := loaded.2 } :
      EVMState).replaceStackAndIncrPC
        (loaded.1 :: values ++ base :: rest)
  have hTailRun :
      Structured.Code.run [Structured.BasicInstr.op .mload] addrState =
        .ok final := by
    simp [Structured.Code.run, Structured.BasicInstr.step,
      Structured.BasicOp.step, Structured.BasicOp.toPrimOp,
      Assembly.Target.stepInstr, Assembly.PrimOp.step,
      Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, EvmYul.Stack.push, EvmYul.Stack.pop,
      hAddrStack, hAddrMachine, addr, loaded, final]
  refine ⟨final, ?_, ?_, ?_⟩
  · rw [hCodeEq, Structured.Preservation.Code.run_append, hAddrRun]
    simpa [addr] using hTailRun
  · simp [final, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, loaded, addr]
  · simp [final, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, loaded, addr]

theorem run_storeTopSlotCode?
    {valuesAboveBase slot : Nat} {code : Structured.Code}
    (hCode : storeTopSlotCode? valuesAboveBase slot = some code)
    (state : EVMState) (value : Word)
    (tail rest : EvmYul.Stack Word) (base : Word)
    (hValues : (value :: tail).length = valuesAboveBase) :
    ∃ final,
      Structured.Code.run code
          { state with stack := (value :: tail) ++ base :: rest } =
        .ok final ∧
      final.stack = tail ++ base :: rest ∧
      final.toMachineState =
        state.toMachineState.mstore (base + slotOffset slot) value := by
  rcases storeTopSlotCode?_eq_some_inv hCode with
    ⟨addrCode, hAddrCode, hCodeEq⟩
  rcases run_slotAddressCode? hAddrCode state (value :: tail) rest base
      hValues with
    ⟨addrState, hAddrRun, hAddrStack, hAddrMachine⟩
  let addr : Word := base + slotOffset slot
  let final : EVMState :=
    ({ addrState with
      toMachineState := state.toMachineState.mstore addr value } :
      EVMState).replaceStackAndIncrPC (tail ++ base :: rest)
  have hTailRun :
      Structured.Code.run [Structured.BasicInstr.op .mstore] addrState =
        .ok final := by
    simp [Structured.Code.run, Structured.BasicInstr.step,
      Structured.BasicOp.step, Structured.BasicOp.toPrimOp,
      Assembly.Target.stepInstr, Assembly.PrimOp.step,
      Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
      EvmYul.EVM.binaryMachineStateOp,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC,
      EvmYul.Stack.pop2, Id.run, hAddrStack, hAddrMachine, addr, final]
  refine ⟨final, ?_, ?_, ?_⟩
  · rw [hCodeEq, Structured.Preservation.Code.run_append, hAddrRun]
    simpa [addr] using hTailRun
  · simp [final, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC]
  · simp [final, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, addr]

theorem generatedAddress_toNat_of_ready
    {machine : EvmYul.MachineState} {base : Word} {words slot : Nat}
    (hReady : ScratchRegionReady machine (range base words).base
      (range base words).words)
    (hSlot : slot < words) :
    (base + slotOffset slot).toNat = base.toNat + 32 * slot := by
  rw [generatedAddress_eq_range_word base words slot]
  simpa [range,
    Locals.SourceLowering.StateRel.SpillScratch.ScratchRange.slot] using
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRange.word_toNat_of_ready
        hReady (by simpa [range] using hSlot)

theorem mstore_generated_slot_ready
    (hSpec : ZeroPaddingSpec)
    (hWordBytes : WordByteEncodingSpec)
    {machine : EvmYul.MachineState} {base : Word} {words slot : Nat}
    {value : Word}
    (hReady : ScratchRegionReady machine (range base words).base
      (range base words).words)
    (hSlot : slot < words) :
    ScratchRegionReady
      (machine.mstore (base + slotOffset slot) value)
      (range base words).base (range base words).words := by
  rw [generatedAddress_eq_range_word base words slot]
  exact
    Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady.mstore_slot
      hSpec hWordBytes hReady (by simpa [range] using hSlot)

theorem mload_generated_slot_ready
    {machine : EvmYul.MachineState} {base : Word} {words slot : Nat}
    (hReady : ScratchRegionReady machine (range base words).base
      (range base words).words)
    (hSlot : slot < words) :
    ScratchRegionReady
      (machine.mload (base + slotOffset slot)).2
      (range base words).base (range base words).words := by
  rw [generatedAddress_eq_range_word base words slot]
  exact
    Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady.mload_slot
      hReady (by simpa [range] using hSlot)

theorem lookupMemory_mstore_generated_slot_same
    (hSpec : ZeroPaddingSpec)
    (hWordBytes : WordByteEncodingSpec)
    {machine : EvmYul.MachineState} {base : Word} {words slot : Nat}
    {value : Word}
    (hReady : ScratchRegionReady machine (range base words).base
      (range base words).words)
    (hSlot : slot < words) :
    (machine.mstore (base + slotOffset slot) value).lookupMemory
        (base + slotOffset slot) = value := by
  rw [generatedAddress_eq_range_word base words slot]
  exact
    Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady.lookupMemory_mstore_range_slot_same
      hSpec hWordBytes hReady
        (by simpa [range] using hSlot)

theorem mload_mstore_generated_slot_value
    (hSpec : ZeroPaddingSpec)
    (hWordBytes : WordByteEncodingSpec)
    {machine : EvmYul.MachineState} {base : Word} {words slot : Nat}
    {value : Word}
    (hReady : ScratchRegionReady machine (range base words).base
      (range base words).words)
    (hSlot : slot < words) :
    ((machine.mstore (base + slotOffset slot) value).mload
        (base + slotOffset slot)).1 = value := by
  rw [generatedAddress_eq_range_word base words slot]
  exact
    Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady.mload_mstore_range_slot_value
      hSpec hWordBytes hReady
        (by simpa [range] using hSlot)

def FrameStoreRel (env : SlotEnv) (store : Locals.Source.Store)
    (machine : EvmYul.MachineState) (base : Word) : Prop :=
  ∀ {name slot},
    lookupSlot? name env = some slot →
      ∃ value,
        store name = some value ∧
          (machine.mload (base + slotOffset slot)).1 = value

theorem mload_generated_slot_machine_eq
    {machine : EvmYul.MachineState} {base : Word} {words slot : Nat}
    (hReady : ScratchRegionReady machine (range base words).base
      (range base words).words)
    (hSlot : slot < words) :
    (machine.mload (base + slotOffset slot)).2 = machine := by
  have hReserved :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchWordReserved
        machine (base + slotOffset slot) := by
    rw [generatedAddress_eq_range_word base words slot]
    exact
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady.scratchWordReserved
        hReady (by simpa [range] using hSlot)
  exact
    Locals.SourceLowering.StateRel.SpillScratch.mload_machine_eq hReserved

theorem FrameStoreRel.load_lookup
    {env : SlotEnv} {store : Locals.Source.Store}
    {machine : EvmYul.MachineState} {base : Word}
    (hRel : FrameStoreRel env store machine base)
    {name : Name} {slot : Nat}
    (hLookup : lookupSlot? name env = some slot) :
    ∃ value,
      store name = some value ∧
        (machine.mload (base + slotOffset slot)).1 = value := by
  exact hRel hLookup

theorem envSlotsBounded_of_stateSlotsBounded_le
    {compileState : CompileState} {words : Nat}
    (hBound : StateSlotsBounded compileState)
    (hLe : compileState.nextSlot ≤ words) :
    EnvSlotsBounded compileState.env words := by
  intro entry hMem
  exact Nat.lt_of_lt_of_le (hBound entry hMem) hLe

theorem slotList_nodup_of_stateSlotsNodup
    {compileState : CompileState}
    (hNodup : StateSlotsNodup compileState) :
    (slotList compileState.env).Nodup := hNodup

theorem slotList_mem_of_mem
    {env : SlotEnv} {name : Name} {slot : Nat}
    (hMem : (name, slot) ∈ env) :
    slot ∈ slotList env := by
  simpa [slotList] using List.mem_map_of_mem (f := Prod.snd) hMem

theorem slotList_nodup_name_eq_of_mem :
    ∀ {env : SlotEnv} {name other : Name} {slot : Nat},
      (slotList env).Nodup →
      (name, slot) ∈ env →
      (other, slot) ∈ env →
        other = name
  | [], name, other, slot, _hNoDup, hNameMem, _hOtherMem => by
      simp at hNameMem
  | (headName, headSlot) :: tail, name, other, slot,
      hNoDup, hNameMem, hOtherMem => by
      change (headSlot :: slotList tail).Nodup at hNoDup
      cases hNoDup with
      | cons hHeadFresh hTailNoDup =>
          change (name, slot) ∈ (headName, headSlot) :: tail at hNameMem
          change (other, slot) ∈ (headName, headSlot) :: tail at hOtherMem
          rw [List.mem_cons] at hNameMem
          rw [List.mem_cons] at hOtherMem
          rcases hNameMem with hNameHead | hNameTail
          · cases hNameHead
            rcases hOtherMem with hOtherHead | hOtherTail
            · cases hOtherHead
              rfl
            · have hTailSlot : headSlot ∈ slotList tail :=
                slotList_mem_of_mem hOtherTail
              exact False.elim (hHeadFresh headSlot hTailSlot rfl)
          · rcases hOtherMem with hOtherHead | hOtherTail
            · cases hOtherHead
              have hTailSlot : headSlot ∈ slotList tail :=
                slotList_mem_of_mem hNameTail
              exact False.elim (hHeadFresh headSlot hTailSlot rfl)
            · exact
                slotList_nodup_name_eq_of_mem
                  hTailNoDup hNameTail hOtherTail

theorem lookupSlot?_noAlias_of_slotList_nodup
    {env : SlotEnv} {name other : Name} {slot : Nat}
    (hNoDup : (slotList env).Nodup)
    (hLookup : lookupSlot? name env = some slot)
    (hOtherLookup : lookupSlot? other env = some slot) :
    other = name := by
  exact
    slotList_nodup_name_eq_of_mem hNoDup
      (lookupSlot?_some_mem hLookup)
      (lookupSlot?_some_mem hOtherLookup)

theorem FrameStoreRel.mstore_insert
    (hSpec : ZeroPaddingSpec)
    (hWordBytes : WordByteEncodingSpec)
    {env : SlotEnv} {store : Locals.Source.Store}
    {machine : EvmYul.MachineState} {base : Word} {words : Nat}
    {name : Name} {slot : Nat} {value : Word}
    (hBound : EnvSlotsBounded env words)
    (hReady : ScratchRegionReady machine (range base words).base
      (range base words).words)
    (hRel : FrameStoreRel env store machine base)
    (hLookup : lookupSlot? name env = some slot)
    (hNoAlias :
      ∀ {other : Name},
        lookupSlot? other env = some slot → other = name) :
    FrameStoreRel env
      (Locals.Source.Store.insert store name value)
      (machine.mstore (base + slotOffset slot) value) base := by
  intro other readSlot hReadLookup
  have hWriteSlot : slot < words :=
    lookupSlot?_lt_of_bounded hBound hLookup
  have hReadSlot : readSlot < words :=
    lookupSlot?_lt_of_bounded hBound hReadLookup
  by_cases hSlotEq : readSlot = slot
  · subst readSlot
    have hOther : other = name := hNoAlias hReadLookup
    subst other
    refine ⟨value, ?_, ?_⟩
    · exact Locals.Source.Store.insert_self store name value
    · exact mload_mstore_generated_slot_value hSpec hWordBytes hReady
        hWriteSlot
  · rcases hRel hReadLookup with ⟨storedValue, hStore, hLoad⟩
    have hOtherNe : other ≠ name := by
      intro hOther
      subst other
      rw [hLookup] at hReadLookup
      cases hReadLookup
      exact hSlotEq rfl
    refine ⟨storedValue, ?_, ?_⟩
    · simpa [Locals.Source.Store.insert_of_ne hOtherNe] using hStore
    · rw [generatedAddress_eq_range_word base words slot]
      rw [generatedAddress_eq_range_word base words readSlot]
      rw [
        Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady.mload_mstore_range_other_slot_value
          hSpec hWordBytes hReady
          (by simpa [range] using hWriteSlot)
          (by simpa [range] using hReadSlot)
          (by
            intro hEq
            exact hSlotEq (by
              simpa [range,
                Locals.SourceLowering.StateRel.SpillScratch.ScratchRange.word,
                Locals.SourceLowering.StateRel.SpillScratch.ScratchRange.slot]
                using hEq))]
      simpa [generatedAddress_eq_range_word base words readSlot] using hLoad

theorem run_loadSlotCode?_frameStore_lookup
    {env : SlotEnv} {store : Locals.Source.Store}
    {machine : EvmYul.MachineState} {base : Word} {words : Nat}
    {name : Name} {valuesAboveBase slot : Nat} {code : Structured.Code}
    (hCode : loadSlotCode? valuesAboveBase slot = some code)
    (hReady : ScratchRegionReady machine (range base words).base
      (range base words).words)
    (hRel : FrameStoreRel env store machine base)
    (hLookup : lookupSlot? name env = some slot)
    (hSlot : slot < words)
    (state : EVMState) (values rest : EvmYul.Stack Word)
    (hMachine : state.toMachineState = machine)
    (hValues : values.length = valuesAboveBase) :
    ∃ value final,
      store name = some value ∧
      Structured.Code.run code
          { state with stack := values ++ base :: rest } = .ok final ∧
      final.toMachineState = machine ∧
      final.stack = value :: values ++ base :: rest ∧
      FrameStoreRel env store final.toMachineState base := by
  rcases hRel hLookup with ⟨value, hStore, hLoad⟩
  rcases run_loadSlotCode? hCode state values rest base hValues with
    ⟨final, hRun, hStack, hFinalMachine⟩
  have hMloadMachine :
      (state.toMachineState.mload (base + slotOffset slot)).2 =
        machine := by
    rw [hMachine]
    exact mload_generated_slot_machine_eq hReady hSlot
  refine ⟨value, final, hStore, hRun, ?_, ?_, ?_⟩
  · simpa [hFinalMachine] using hMloadMachine
  · rw [hStack, hMachine, hLoad]
  · rw [hFinalMachine, hMloadMachine]
    exact hRel

theorem run_loadSlotCode?_frameStore_lookup_of_stateSlots
    {compileState : CompileState} {store : Locals.Source.Store}
    {machine : EvmYul.MachineState} {base : Word} {words : Nat}
    {name : Name} {valuesAboveBase slot : Nat} {code : Structured.Code}
    (hCode : loadSlotCode? valuesAboveBase slot = some code)
    (hStateBound : StateSlotsBounded compileState)
    (hFrameWords : compileState.nextSlot ≤ words)
    (hReady : ScratchRegionReady machine (range base words).base
      (range base words).words)
    (hRel : FrameStoreRel compileState.env store machine base)
    (hLookup : lookupSlot? name compileState.env = some slot)
    (state : EVMState) (values rest : EvmYul.Stack Word)
    (hMachine : state.toMachineState = machine)
    (hValues : values.length = valuesAboveBase) :
    ∃ value final,
      store name = some value ∧
      Structured.Code.run code
          { state with stack := values ++ base :: rest } = .ok final ∧
      final.toMachineState = machine ∧
      final.stack = value :: values ++ base :: rest ∧
      FrameStoreRel compileState.env store final.toMachineState base := by
  have hEnvBound : EnvSlotsBounded compileState.env words :=
    envSlotsBounded_of_stateSlotsBounded_le hStateBound hFrameWords
  exact
    run_loadSlotCode?_frameStore_lookup
      hCode hReady hRel hLookup
      (lookupSlot?_lt_of_bounded hEnvBound hLookup)
      state values rest hMachine hValues

theorem run_compileExprCode?_var_frameStore_lookup_of_stateSlots
    {compileState : CompileState} {store : Locals.Source.Store}
    {machine : EvmYul.MachineState} {base : Word} {words : Nat}
    {name : Name} {valuesAboveBase : Nat} {code : Structured.Code}
    (hCompile :
      compileExprCode? compileState.env valuesAboveBase (.var name) =
        some code)
    (hStateBound : StateSlotsBounded compileState)
    (hFrameWords : compileState.nextSlot ≤ words)
    (hReady : ScratchRegionReady machine (range base words).base
      (range base words).words)
    (hRel : FrameStoreRel compileState.env store machine base)
    (state : EVMState) (values rest : EvmYul.Stack Word)
    (hMachine : state.toMachineState = machine)
    (hValues : values.length = valuesAboveBase) :
    ∃ value final,
      store name = some value ∧
      Structured.Code.run code
          { state with stack := values ++ base :: rest } = .ok final ∧
      final.toMachineState = machine ∧
      final.stack = value :: values ++ base :: rest ∧
      FrameStoreRel compileState.env store final.toMachineState base := by
  have hEnvBound : EnvSlotsBounded compileState.env words :=
    envSlotsBounded_of_stateSlotsBounded_le hStateBound hFrameWords
  rcases
      compileExprCode?_var_load_slot_bounded hEnvBound hCompile with
    ⟨slot, hLookup, _hSlot, hLoadCode⟩
  exact
    run_loadSlotCode?_frameStore_lookup_of_stateSlots
      hLoadCode hStateBound hFrameWords hReady hRel hLookup
      state values rest hMachine hValues

theorem run_compileExprCode?_lit_frameStore
    {compileState : CompileState} {store : Locals.Source.Store}
    {machine : EvmYul.MachineState} {base value : Word}
    {valuesAboveBase : Nat} {code : Structured.Code}
    (hCompile :
      compileExprCode? compileState.env valuesAboveBase (.lit value) =
        some code)
    (hRel : FrameStoreRel compileState.env store machine base)
    (state : EVMState) (values rest : EvmYul.Stack Word)
    (hMachine : state.toMachineState = machine)
    (_hValues : values.length = valuesAboveBase) :
    ∃ final,
      Structured.Code.run code
          { state with stack := values ++ base :: rest } = .ok final ∧
      final.toMachineState = machine ∧
      final.stack = value :: values ++ base :: rest ∧
      FrameStoreRel compileState.env store final.toMachineState base := by
  simp [compileExprCode?] at hCompile
  cases hCompile
  let start : EVMState := { state with stack := values ++ base :: rest }
  let final : EVMState :=
    start.replaceStackAndIncrPC (value :: values ++ base :: rest)
      (pcΔ := 33)
  refine ⟨final, ?_, ?_, ?_, ?_⟩
  · simp [Structured.Code.run, Structured.BasicInstr.step,
      Assembly.Target.stepInstr, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, EvmYul.Stack.push, start, final]
  · simpa [start, final, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC] using hMachine
  · simp [start, final, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC]
  · have hFinalMachine : final.toMachineState = machine := by
      simpa [start, final, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC] using hMachine
    rw [hFinalMachine]
    intro query slot hLookup
    exact hRel hLookup

theorem run_compileExprSeqCode?_nil_frameStore
    {compileState : CompileState} {store : Locals.Source.Store}
    {machine : EvmYul.MachineState} {base : Word}
    {valuesAboveBase : Nat} {code : Structured.Code}
    (hCompile :
      compileExprSeqCode? compileState.env valuesAboveBase
          (Locals.ExprSeq.nil : Locals.ExprSeq 0) =
        some code)
    (hRel : FrameStoreRel compileState.env store machine base)
    (state : EVMState) (values rest : EvmYul.Stack Word)
    (hMachine : state.toMachineState = machine)
    (_hValues : values.length = valuesAboveBase) :
    ∃ final,
      Structured.Code.run code
          { state with stack := values ++ base :: rest } = .ok final ∧
      final.toMachineState = machine ∧
      final.stack = values ++ base :: rest ∧
      FrameStoreRel compileState.env store final.toMachineState base := by
  simp [compileExprSeqCode?] at hCompile
  cases hCompile
  let final : EVMState := { state with stack := values ++ base :: rest }
  refine ⟨final, ?_, ?_, ?_, ?_⟩
  · simp [Structured.Code.run, final]
  · simpa [final] using hMachine
  · simp [final]
  · have hFinalMachine : final.toMachineState = machine := by
      simpa [final] using hMachine
    rw [hFinalMachine]
    intro query slot hLookup
    exact hRel hLookup

theorem run_storeTopSlotCode?_frameStore_assign
    (hSpec : ZeroPaddingSpec)
    (hWordBytes : WordByteEncodingSpec)
    {env : SlotEnv} {store : Locals.Source.Store}
    {machine : EvmYul.MachineState} {base : Word} {words : Nat}
    {name : Name} {slot valuesAboveBase : Nat}
    {code : Structured.Code} {value : Word}
    (hCode : storeTopSlotCode? valuesAboveBase slot = some code)
    (hBound : EnvSlotsBounded env words)
    (hReady : ScratchRegionReady machine (range base words).base
      (range base words).words)
    (hRel : FrameStoreRel env store machine base)
    (hLookup : lookupSlot? name env = some slot)
    (hNoAlias :
      ∀ {other : Name},
        lookupSlot? other env = some slot → other = name)
    (state : EVMState) (tail rest : EvmYul.Stack Word)
    (hMachine : state.toMachineState = machine)
    (hValues : (value :: tail).length = valuesAboveBase) :
    ∃ final,
      Structured.Code.run code
          { state with stack := (value :: tail) ++ base :: rest } =
        .ok final ∧
      final.stack = tail ++ base :: rest ∧
      ScratchRegionReady final.toMachineState
        (range base words).base (range base words).words ∧
      FrameStoreRel env
        (Locals.Source.Store.insert store name value)
        final.toMachineState base := by
  rcases run_storeTopSlotCode? hCode state value tail rest base hValues with
    ⟨final, hRun, hStack, hFinalMachine⟩
  have hSlot : slot < words :=
    lookupSlot?_lt_of_bounded hBound hLookup
  have hReadyStored :
      ScratchRegionReady
        (machine.mstore (base + slotOffset slot) value)
        (range base words).base (range base words).words :=
    mstore_generated_slot_ready hSpec hWordBytes hReady hSlot
  have hRelStored :
      FrameStoreRel env
        (Locals.Source.Store.insert store name value)
        (machine.mstore (base + slotOffset slot) value) base :=
    FrameStoreRel.mstore_insert hSpec hWordBytes hBound hReady hRel
      hLookup hNoAlias
  refine ⟨final, hRun, hStack, ?_, ?_⟩
  · rw [hFinalMachine, hMachine]
    exact hReadyStored
  · rw [hFinalMachine, hMachine]
    exact hRelStored

theorem FrameStoreRel.mstore_insert_of_slotList_nodup
    (hSpec : ZeroPaddingSpec)
    (hWordBytes : WordByteEncodingSpec)
    {env : SlotEnv} {store : Locals.Source.Store}
    {machine : EvmYul.MachineState} {base : Word} {words : Nat}
    {name : Name} {slot : Nat} {value : Word}
    (hBound : EnvSlotsBounded env words)
    (hNoDup : (slotList env).Nodup)
    (hReady : ScratchRegionReady machine (range base words).base
      (range base words).words)
    (hRel : FrameStoreRel env store machine base)
    (hLookup : lookupSlot? name env = some slot) :
    FrameStoreRel env
      (Locals.Source.Store.insert store name value)
      (machine.mstore (base + slotOffset slot) value) base :=
  FrameStoreRel.mstore_insert hSpec hWordBytes hBound hReady hRel hLookup
    (fun hOtherLookup =>
      lookupSlot?_noAlias_of_slotList_nodup hNoDup hLookup hOtherLookup)

theorem run_storeTopSlotCode?_frameStore_assign_of_slotList_nodup
    (hSpec : ZeroPaddingSpec)
    (hWordBytes : WordByteEncodingSpec)
    {env : SlotEnv} {store : Locals.Source.Store}
    {machine : EvmYul.MachineState} {base : Word} {words : Nat}
    {name : Name} {slot valuesAboveBase : Nat}
    {code : Structured.Code} {value : Word}
    (hCode : storeTopSlotCode? valuesAboveBase slot = some code)
    (hBound : EnvSlotsBounded env words)
    (hNoDup : (slotList env).Nodup)
    (hReady : ScratchRegionReady machine (range base words).base
      (range base words).words)
    (hRel : FrameStoreRel env store machine base)
    (hLookup : lookupSlot? name env = some slot)
    (state : EVMState) (tail rest : EvmYul.Stack Word)
    (hMachine : state.toMachineState = machine)
    (hValues : (value :: tail).length = valuesAboveBase) :
    ∃ final,
      Structured.Code.run code
          { state with stack := (value :: tail) ++ base :: rest } =
        .ok final ∧
      final.stack = tail ++ base :: rest ∧
      ScratchRegionReady final.toMachineState
        (range base words).base (range base words).words ∧
      FrameStoreRel env
        (Locals.Source.Store.insert store name value)
        final.toMachineState base := by
  exact
    run_storeTopSlotCode?_frameStore_assign hSpec hWordBytes hCode hBound
      hReady hRel hLookup
      (fun hOtherLookup =>
        lookupSlot?_noAlias_of_slotList_nodup hNoDup hLookup hOtherLookup)
      state tail rest hMachine hValues

theorem run_storeTopSlotCode?_frameStore_assign_of_stateSlots
    (hSpec : ZeroPaddingSpec)
    (hWordBytes : WordByteEncodingSpec)
    {compileState : CompileState} {store : Locals.Source.Store}
    {machine : EvmYul.MachineState} {base : Word} {words : Nat}
    {name : Name} {slot valuesAboveBase : Nat}
    {code : Structured.Code} {value : Word}
    (hCode : storeTopSlotCode? valuesAboveBase slot = some code)
    (hStateBound : StateSlotsBounded compileState)
    (hStateNodup : StateSlotsNodup compileState)
    (hFrameWords : compileState.nextSlot ≤ words)
    (hReady : ScratchRegionReady machine (range base words).base
      (range base words).words)
    (hRel : FrameStoreRel compileState.env store machine base)
    (hLookup : lookupSlot? name compileState.env = some slot)
    (state : EVMState) (tail rest : EvmYul.Stack Word)
    (hMachine : state.toMachineState = machine)
    (hValues : (value :: tail).length = valuesAboveBase) :
    ∃ final,
      Structured.Code.run code
          { state with stack := (value :: tail) ++ base :: rest } =
        .ok final ∧
      final.stack = tail ++ base :: rest ∧
      ScratchRegionReady final.toMachineState
        (range base words).base (range base words).words ∧
      FrameStoreRel compileState.env
        (Locals.Source.Store.insert store name value)
        final.toMachineState base := by
  exact
    run_storeTopSlotCode?_frameStore_assign_of_slotList_nodup
      hSpec hWordBytes hCode
      (envSlotsBounded_of_stateSlotsBounded_le hStateBound hFrameWords)
      (slotList_nodup_of_stateSlotsNodup hStateNodup)
      hReady hRel hLookup state tail rest hMachine hValues

end FrameMemory

end ScratchFrameSpill
end Functions
end EvmCompiler
