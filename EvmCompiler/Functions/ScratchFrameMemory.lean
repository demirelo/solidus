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

end FrameMemory

end ScratchFrameSpill
end Functions
end EvmCompiler
