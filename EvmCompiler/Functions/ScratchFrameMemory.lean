import EvmCompiler.Functions.ScratchFrameSpill
import EvmCompiler.Functions.SourceSemantics
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

abbrev SharedStateEqOutsideScratch :=
  Locals.SourceLowering.StateRel.SpillScratch.SharedStateEqOutsideScratch

abbrev SourceExprSafe {results : Nat} (expr : Expr results) : Prop :=
  Locals.SourceLowering.StateRel.SpillScratch.SourceNoMemoryTouch.ExprSafe expr

abbrev SourceExprSeqSafe {results : Nat}
    (exprs : Locals.ExprSeq results) : Prop :=
  Locals.SourceLowering.StateRel.SpillScratch.SourceNoMemoryTouch.ExprSeqSafe
    exprs

def AtomicStmtSafe : Stmt → Prop
  | .expr expr => SourceExprSafe expr
  | .let_ _name value => SourceExprSafe value
  | .assign _name value => SourceExprSafe value
  | _ => False

def AtomicStmtListSafe : List Stmt → Prop
  | [] => True
  | stmt :: rest => AtomicStmtSafe stmt ∧ AtomicStmtListSafe rest

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
      final.toMachineState = state.toMachineState ∧
      final.toSharedState = state.toSharedState := by
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
  refine ⟨final, ?_, ?_, ?_, ?_⟩
  · simpa [start] using hRun
  · simp [final, start, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC]
  · cases state
    simp [final, start, EvmYul.EVM.State.replaceStackAndIncrPC,
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
      final.toMachineState = state.toMachineState ∧
      final.toSharedState = state.toSharedState := by
  rcases slotAddressCode?_eq_some_inv hCode with
    ⟨dup, hDup, hCodeEq⟩
  rcases run_dupCode?_copyBase hDup state values rest base
      (by omega) with
    ⟨mid, hDupRun, hMidStack, hMidMachine, hMidShared⟩
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
  refine ⟨final, ?_, ?_, ?_, ?_⟩
  · rw [hCodeEq, Structured.Preservation.Code.run_append, hDupRun]
    simpa [offset] using hTailRun
  · simp [final, state1, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, addr, offset]
  · simpa [final, state1, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, addr, offset] using hMidMachine
  · simpa [final, state1, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, addr, offset] using hMidShared

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
        (state.toMachineState.mload (base + slotOffset slot)).2 ∧
      final.toSharedState =
        ({ state with
          toMachineState :=
            (state.toMachineState.mload (base + slotOffset slot)).2 } :
          EVMState).toSharedState := by
  rcases loadSlotCode?_eq_some_inv hCode with
    ⟨addrCode, hAddrCode, hCodeEq⟩
  rcases run_slotAddressCode? hAddrCode state values rest base hValues with
    ⟨addrState, hAddrRun, hAddrStack, hAddrMachine, hAddrShared⟩
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
  refine ⟨final, ?_, ?_, ?_, ?_⟩
  · rw [hCodeEq, Structured.Preservation.Code.run_append, hAddrRun]
    simpa [addr] using hTailRun
  · simp [final, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, loaded, addr]
  · simp [final, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, loaded, addr]
  · have hAddrState :
        addrState.toState = state.toState := by
      exact congrArg (fun shared => shared.toState) hAddrShared
    simpa [final, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, loaded, addr] using hAddrState

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
        state.toMachineState.mstore (base + slotOffset slot) value ∧
      final.toSharedState =
        ({ state with
          toMachineState :=
            state.toMachineState.mstore (base + slotOffset slot) value } :
          EVMState).toSharedState := by
  rcases storeTopSlotCode?_eq_some_inv hCode with
    ⟨addrCode, hAddrCode, hCodeEq⟩
  rcases run_slotAddressCode? hAddrCode state (value :: tail) rest base
      hValues with
    ⟨addrState, hAddrRun, hAddrStack, hAddrMachine, hAddrShared⟩
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
  refine ⟨final, ?_, ?_, ?_, ?_⟩
  · rw [hCodeEq, Structured.Preservation.Code.run_append, hAddrRun]
    simpa [addr] using hTailRun
  · simp [final, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC]
  · simp [final, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, addr]
  · have hAddrState :
        addrState.toState = state.toState := by
      exact congrArg (fun shared => shared.toState) hAddrShared
    simpa [final, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, addr] using hAddrState

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

theorem mload_mstore_generated_slot_other_value
    (hSpec : ZeroPaddingSpec)
    (hWordBytes : WordByteEncodingSpec)
    {machine : EvmYul.MachineState} {base : Word}
    {words writeSlot readSlot : Nat} {value : Word}
    (hReady : ScratchRegionReady machine (range base words).base
      (range base words).words)
    (hWriteSlot : writeSlot < words)
    (hReadSlot : readSlot < words)
    (hNe : readSlot ≠ writeSlot) :
    ((machine.mstore (base + slotOffset writeSlot) value).mload
        (base + slotOffset readSlot)).1 =
      (machine.mload (base + slotOffset readSlot)).1 := by
  rw [generatedAddress_eq_range_word base words writeSlot]
  rw [generatedAddress_eq_range_word base words readSlot]
  exact
    Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady.mload_mstore_range_other_slot_value
      hSpec hWordBytes hReady
      (by simpa [range] using hWriteSlot)
      (by simpa [range] using hReadSlot)
      (by
        intro hEq
        exact hNe (by
          simpa [range,
            Locals.SourceLowering.StateRel.SpillScratch.ScratchRange.word,
            Locals.SourceLowering.StateRel.SpillScratch.ScratchRange.slot]
            using hEq))

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

theorem FrameStoreRel.empty
    {store : Locals.Source.Store} {machine : EvmYul.MachineState}
    {base : Word} :
    FrameStoreRel [] store machine base := by
  intro name slot hLookup
  simp [lookupSlot?] at hLookup

theorem StateSlotsBounded.empty (nextSlot : Nat) :
    StateSlotsBounded
      ({ env := [], nextSlot := nextSlot } : CompileState) := by
  intro entry hMem
  simp at hMem

theorem StateSlotsNodup.empty (nextSlot : Nat) :
    StateSlotsNodup
      ({ env := [], nextSlot := nextSlot } : CompileState) := by
  simp [StateSlotsNodup, slotList]

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

theorem FrameStoreRel.mstore_allocateName_insert
    (hSpec : ZeroPaddingSpec)
    (hWordBytes : WordByteEncodingSpec)
    {compileState stateAfter : CompileState}
    {store : Locals.Source.Store}
    {machine : EvmYul.MachineState} {base : Word} {words : Nat}
    {name : Name} {slot : Nat} {value : Word}
    (hAlloc : allocateName name compileState = (slot, stateAfter))
    (hBound : StateSlotsBounded compileState)
    (hFrameWords : stateAfter.nextSlot ≤ words)
    (hReady : ScratchRegionReady machine (range base words).base
      (range base words).words)
    (hRel : FrameStoreRel compileState.env store machine base) :
    FrameStoreRel stateAfter.env
      (Locals.Source.Store.insert store name value)
      (machine.mstore (base + slotOffset slot) value) base := by
  cases compileState with
  | mk env nextSlot =>
      change
        (nextSlot,
          { env := (name, nextSlot) :: env
            nextSlot := nextSlot + 1 }) = (slot, stateAfter) at hAlloc
      cases hAlloc
      intro other readSlot hLookup
      have hFrameWords' : slot + 1 ≤ words := by
        simpa using hFrameWords
      have hWriteSlot : slot < words := by
        omega
      by_cases hOther : other = name
      · subst other
        simp [lookupSlot?] at hLookup
        cases hLookup
        refine ⟨value, ?_, ?_⟩
        · exact Locals.Source.Store.insert_self store name value
        · exact
            mload_mstore_generated_slot_value hSpec hWordBytes hReady
              hWriteSlot
      · have hNameNe : name ≠ other := by
          intro hEq
          exact hOther hEq.symm
        simp [lookupSlot?, hNameNe] at hLookup
        rcases hRel hLookup with ⟨storedValue, hStore, hLoad⟩
        have hReadSlotLtNext : readSlot < slot :=
          hBound (other, readSlot) (lookupSlot?_some_mem hLookup)
        have hReadSlot : readSlot < words := by omega
        have hSlotNe : readSlot ≠ slot := by omega
        refine ⟨storedValue, ?_, ?_⟩
        · simpa [Locals.Source.Store.insert_of_ne hOther] using hStore
        · rw [
            mload_mstore_generated_slot_other_value hSpec hWordBytes
              hReady hWriteSlot hReadSlot hSlotNe]
          exact hLoad

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
    ⟨final, hRun, hStack, hFinalMachine, _hFinalShared⟩
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

theorem run_compileExprCode?_var_frameStore_lookup_shared_of_stateSlots
    {compileState : CompileState} {store : Locals.Source.Store}
    {machine : EvmYul.MachineState} {base : Word} {words : Nat}
    {sourceShared : EvmYul.SharedState .EVM}
    {name : Name} {valuesAboveBase : Nat} {code : Structured.Code}
    (hCompile :
      compileExprCode? compileState.env valuesAboveBase (.var name) =
        some code)
    (hStateBound : StateSlotsBounded compileState)
    (hFrameWords : compileState.nextSlot ≤ words)
    (hReady : ScratchRegionReady machine (range base words).base
      (range base words).words)
    (state : EVMState)
    (hShared : SharedStateEqOutsideScratch (range base words) sourceShared
      state.toSharedState)
    (hRel : FrameStoreRel compileState.env store machine base)
    (values rest : EvmYul.Stack Word)
    (hMachine : state.toMachineState = machine)
    (hValues : values.length = valuesAboveBase) :
    ∃ value final,
      store name = some value ∧
      Structured.Code.run code
          { state with stack := values ++ base :: rest } = .ok final ∧
      final.stack = value :: values ++ base :: rest ∧
      ScratchRegionReady final.toMachineState
        (range base words).base (range base words).words ∧
      SharedStateEqOutsideScratch (range base words) sourceShared
        final.toSharedState ∧
      FrameStoreRel compileState.env store final.toMachineState base := by
  have hEnvBound : EnvSlotsBounded compileState.env words :=
    envSlotsBounded_of_stateSlotsBounded_le hStateBound hFrameWords
  rcases
      compileExprCode?_var_load_slot_bounded hEnvBound hCompile with
    ⟨slot, hLookup, hSlot, hLoadCode⟩
  rcases FrameStoreRel.load_lookup hRel hLookup with
    ⟨value, hStore, hLoad⟩
  rcases run_loadSlotCode? hLoadCode state values rest base hValues with
    ⟨final, hRun, hStack, hFinalMachineRaw, hFinalSharedRaw⟩
  have hMloadMachine :
      (state.toMachineState.mload (base + slotOffset slot)).2 =
        machine := by
    rw [hMachine]
    exact mload_generated_slot_machine_eq hReady hSlot
  have hFinalMachine : final.toMachineState = machine := by
    simpa [hFinalMachineRaw] using hMloadMachine
  have hLoadedMachineState :
      (state.toMachineState.mload (base + slotOffset slot)).2 =
        state.toMachineState := by
    simpa [hMachine] using hMloadMachine
  have hFinalShared : final.toSharedState = state.toSharedState := by
    rw [hFinalSharedRaw, hLoadedMachineState]
  refine ⟨value, final, hStore, hRun, ?_, ?_, ?_, ?_⟩
  · rw [hStack, hMachine, hLoad]
  · rw [hFinalMachine]
    exact hReady
  · rw [hFinalShared]
    exact hShared
  · rw [hFinalMachine]
    exact hRel

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

theorem run_compileExprCode?_lit_frameStore_shared
    {compileState : CompileState} {store : Locals.Source.Store}
    {machine : EvmYul.MachineState} {base value : Word} {words : Nat}
    {sourceShared : EvmYul.SharedState .EVM}
    {valuesAboveBase : Nat} {code : Structured.Code}
    (hCompile :
      compileExprCode? compileState.env valuesAboveBase (.lit value) =
        some code)
    (hReady : ScratchRegionReady machine (range base words).base
      (range base words).words)
    (state : EVMState)
    (hShared : SharedStateEqOutsideScratch (range base words) sourceShared
      state.toSharedState)
    (hRel : FrameStoreRel compileState.env store machine base)
    (values rest : EvmYul.Stack Word)
    (hMachine : state.toMachineState = machine)
    (hValues : values.length = valuesAboveBase) :
    ∃ final,
      Structured.Code.run code
          { state with stack := values ++ base :: rest } = .ok final ∧
      final.stack = value :: values ++ base :: rest ∧
      ScratchRegionReady final.toMachineState
        (range base words).base (range base words).words ∧
      SharedStateEqOutsideScratch (range base words) sourceShared
        final.toSharedState ∧
      FrameStoreRel compileState.env store final.toMachineState base := by
  rcases
      run_compileExprCode?_lit_frameStore
        hCompile hRel state values rest hMachine hValues with
    ⟨final, hRun, hFinalMachine, hFinalStack, hRelFinal⟩
  have hFinalShared : final.toSharedState = state.toSharedState := by
    simp [compileExprCode?] at hCompile
    cases hCompile
    let start : EVMState := { state with stack := values ++ base :: rest }
    let expected : EVMState :=
      start.replaceStackAndIncrPC (value :: values ++ base :: rest)
        (pcΔ := 33)
    have hRunExpected :
        Structured.Code.run [Structured.BasicInstr.push value]
            { state with stack := values ++ base :: rest } =
          .ok expected := by
      simp [Structured.Code.run, Structured.BasicInstr.step,
        Assembly.Target.stepInstr, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC, EvmYul.Stack.push, start, expected]
    have hExpected : final = expected := by
      rw [hRunExpected] at hRun
      injection hRun with hEq
      exact hEq.symm
    subst final
    simp [expected, start, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC]
  refine ⟨final, hRun, hFinalStack, ?_, ?_, hRelFinal⟩
  · rw [hFinalMachine]
    exact hReady
  · rw [hFinalShared]
    exact hShared

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

theorem run_compileExprSeqCode?_nil_frameStore_shared
    {compileState : CompileState} {store : Locals.Source.Store}
    {machine : EvmYul.MachineState} {base : Word} {words : Nat}
    {sourceShared : EvmYul.SharedState .EVM}
    {valuesAboveBase : Nat} {code : Structured.Code}
    (hCompile :
      compileExprSeqCode? compileState.env valuesAboveBase
          (Locals.ExprSeq.nil : Locals.ExprSeq 0) =
        some code)
    (hReady : ScratchRegionReady machine (range base words).base
      (range base words).words)
    (state : EVMState)
    (hShared : SharedStateEqOutsideScratch (range base words) sourceShared
      state.toSharedState)
    (hRel : FrameStoreRel compileState.env store machine base)
    (values rest : EvmYul.Stack Word)
    (hMachine : state.toMachineState = machine)
    (_hValues : values.length = valuesAboveBase) :
    ∃ final,
      Structured.Code.run code
          { state with stack := values ++ base :: rest } = .ok final ∧
      final.stack = values ++ base :: rest ∧
      ScratchRegionReady final.toMachineState
        (range base words).base (range base words).words ∧
      SharedStateEqOutsideScratch (range base words) sourceShared
        final.toSharedState ∧
      FrameStoreRel compileState.env store final.toMachineState base := by
  simp [compileExprSeqCode?] at hCompile
  cases hCompile
  let final : EVMState := { state with stack := values ++ base :: rest }
  refine ⟨final, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Structured.Code.run, final]
  · simp [final]
  · have hFinalMachine : final.toMachineState = machine := by
      simpa [final] using hMachine
    rw [hFinalMachine]
    exact hReady
  · simpa [final] using hShared
  · have hFinalMachine : final.toMachineState = machine := by
      simpa [final] using hMachine
    rw [hFinalMachine]
    intro query slot hLookup
    exact hRel hLookup

theorem run_compileExprSeqCode?_cons_frameStore_of_parts
    {compileState : CompileState} {store : Locals.Source.Store}
    {base : Word} {words : Nat} {valuesAboveBase left right : Nat}
    {head : Expr left} {tail : Locals.ExprSeq right}
    {code : Structured.Code}
    (hCompile :
      compileExprSeqCode? compileState.env valuesAboveBase
          (Locals.ExprSeq.cons (left := left) (right := right) head tail) =
        some code)
    (state : EVMState) (values rest : EvmYul.Stack Word)
    (hHeadRun :
      ∀ {headCode : Structured.Code},
        compileExprCode? compileState.env valuesAboveBase head =
          some headCode →
          ∃ (headValues : List Word) (mid : EVMState),
            headValues.length = left ∧
            Structured.Code.run headCode
                { state with stack := values ++ base :: rest } = .ok mid ∧
            mid.stack = headValues.reverse ++ values ++ base :: rest ∧
            ScratchRegionReady mid.toMachineState
              (range base words).base (range base words).words ∧
            FrameStoreRel compileState.env store mid.toMachineState base)
    (hTailRun :
      ∀ {tailCode : Structured.Code} {headValues : List Word}
          {mid : EVMState},
        compileExprSeqCode? compileState.env (valuesAboveBase + left) tail =
          some tailCode →
        headValues.length = left →
        mid.stack = headValues.reverse ++ values ++ base :: rest →
        ScratchRegionReady mid.toMachineState
          (range base words).base (range base words).words →
        FrameStoreRel compileState.env store mid.toMachineState base →
          ∃ (tailValues : List Word) (final : EVMState),
            tailValues.length = right ∧
            Structured.Code.run tailCode mid = .ok final ∧
            final.stack =
              tailValues.reverse ++ headValues.reverse ++ values ++
                base :: rest ∧
            ScratchRegionReady final.toMachineState
              (range base words).base (range base words).words ∧
            FrameStoreRel compileState.env store final.toMachineState base) :
    ∃ (resultValues : List Word) (final : EVMState),
      resultValues.length = left + right ∧
      Structured.Code.run code
          { state with stack := values ++ base :: rest } = .ok final ∧
      final.stack = resultValues.reverse ++ values ++ base :: rest ∧
      ScratchRegionReady final.toMachineState
        (range base words).base (range base words).words ∧
      FrameStoreRel compileState.env store final.toMachineState base := by
  simp [compileExprSeqCode?] at hCompile
  cases hHeadCode :
      compileExprCode? compileState.env valuesAboveBase head with
  | none =>
      simp [hHeadCode] at hCompile
  | some headCode =>
      cases hTailCode :
          compileExprSeqCode? compileState.env (valuesAboveBase + left)
            tail with
      | none =>
          simp [hHeadCode, hTailCode] at hCompile
      | some tailCode =>
          simp [hHeadCode, hTailCode] at hCompile
          cases hCompile
          rcases hHeadRun hHeadCode with
            ⟨headValues, mid, hHeadLen, hHeadRunCode, hMidStack,
              hReadyMid, hRelMid⟩
          rcases
              hTailRun hTailCode hHeadLen hMidStack hReadyMid hRelMid with
            ⟨tailValues, final, hTailLen, hTailRunCode, hFinalStack,
              hReadyFinal, hRelFinal⟩
          refine
            ⟨headValues ++ tailValues, final, ?_, ?_, ?_, hReadyFinal,
              hRelFinal⟩
          · simp [hHeadLen, hTailLen]
          · rw [Structured.Preservation.Code.run_append, hHeadRunCode]
            exact hTailRunCode
          · simpa [List.reverse_append, List.append_assoc] using hFinalStack

theorem run_compileExprSeqCode?_cons_frameStore_shared_of_parts
    {compileState : CompileState} {store : Locals.Source.Store}
    {base : Word} {words : Nat} {valuesAboveBase left right : Nat}
    {head : Expr left} {tail : Locals.ExprSeq right}
    {code : Structured.Code}
    {sourceShared' : EvmYul.SharedState .EVM}
    (hCompile :
      compileExprSeqCode? compileState.env valuesAboveBase
          (Locals.ExprSeq.cons (left := left) (right := right) head tail) =
        some code)
    (state : EVMState) (values rest : EvmYul.Stack Word)
    (hHeadRun :
      ∀ {headCode : Structured.Code},
        compileExprCode? compileState.env valuesAboveBase head =
          some headCode →
          ∃ (headValues : List Word)
            (sourceSharedAfterHead : EvmYul.SharedState .EVM)
            (mid : EVMState),
            headValues.length = left ∧
            Structured.Code.run headCode
                { state with stack := values ++ base :: rest } = .ok mid ∧
            mid.stack = headValues.reverse ++ values ++ base :: rest ∧
            ScratchRegionReady mid.toMachineState
              (range base words).base (range base words).words ∧
            SharedStateEqOutsideScratch (range base words)
              sourceSharedAfterHead mid.toSharedState ∧
            FrameStoreRel compileState.env store mid.toMachineState base)
    (hTailRun :
      ∀ {tailCode : Structured.Code} {headValues : List Word}
          {sourceSharedAfterHead : EvmYul.SharedState .EVM}
          {mid : EVMState},
        compileExprSeqCode? compileState.env (valuesAboveBase + left) tail =
          some tailCode →
        headValues.length = left →
        mid.stack = headValues.reverse ++ values ++ base :: rest →
        ScratchRegionReady mid.toMachineState
          (range base words).base (range base words).words →
        SharedStateEqOutsideScratch (range base words)
          sourceSharedAfterHead mid.toSharedState →
        FrameStoreRel compileState.env store mid.toMachineState base →
          ∃ (tailValues : List Word) (final : EVMState),
            tailValues.length = right ∧
            Structured.Code.run tailCode mid = .ok final ∧
            final.stack =
              tailValues.reverse ++ headValues.reverse ++ values ++
                base :: rest ∧
            ScratchRegionReady final.toMachineState
              (range base words).base (range base words).words ∧
            SharedStateEqOutsideScratch (range base words) sourceShared'
              final.toSharedState ∧
            FrameStoreRel compileState.env store final.toMachineState base) :
    ∃ (resultValues : List Word) (final : EVMState),
      resultValues.length = left + right ∧
      Structured.Code.run code
          { state with stack := values ++ base :: rest } = .ok final ∧
      final.stack = resultValues.reverse ++ values ++ base :: rest ∧
      ScratchRegionReady final.toMachineState
        (range base words).base (range base words).words ∧
      SharedStateEqOutsideScratch (range base words) sourceShared'
        final.toSharedState ∧
      FrameStoreRel compileState.env store final.toMachineState base := by
  simp [compileExprSeqCode?] at hCompile
  cases hHeadCode :
      compileExprCode? compileState.env valuesAboveBase head with
  | none =>
      simp [hHeadCode] at hCompile
  | some headCode =>
      cases hTailCode :
          compileExprSeqCode? compileState.env (valuesAboveBase + left)
            tail with
      | none =>
          simp [hHeadCode, hTailCode] at hCompile
      | some tailCode =>
          simp [hHeadCode, hTailCode] at hCompile
          cases hCompile
          rcases hHeadRun hHeadCode with
            ⟨headValues, sourceSharedAfterHead, mid, hHeadLen,
              hHeadRunCode, hMidStack, hReadyMid, hSharedMid, hRelMid⟩
          rcases
              hTailRun hTailCode hHeadLen hMidStack hReadyMid hSharedMid
                hRelMid with
            ⟨tailValues, final, hTailLen, hTailRunCode, hFinalStack,
              hReadyFinal, hSharedFinal, hRelFinal⟩
          refine
            ⟨headValues ++ tailValues, final, ?_, ?_, ?_, hReadyFinal,
              hSharedFinal, hRelFinal⟩
          · simp [hHeadLen, hTailLen]
          · rw [Structured.Preservation.Code.run_append, hHeadRunCode]
            exact hTailRunCode
          · simpa [List.reverse_append, List.append_assoc] using hFinalStack

theorem run_compileExprCode?_prim_frameStore_of_args
    {compileState : CompileState} {store : Locals.Source.Store}
    {base : Word} {words valuesAboveBase : Nat}
    {op : Structured.BasicOp}
    {args : Locals.ExprSeq (Expressions.Structured.BasicOp.inputs op)}
    {code : Structured.Code}
    {sourceShared sourceShared' : EvmYul.SharedState .EVM}
    {argValues resultValues : List Word}
    (hCompile :
      compileExprCode? compileState.env valuesAboveBase (.prim op args) =
        some code)
    (hNoMem :
      ¬ Locals.SourceLowering.StateRel.SpillScratch.SourceNoMemoryTouch.BasicOpMemoryTouching
          op)
    (hPrimEval :
      Locals.Source.PrimitiveSemantics.structured.eval op sourceShared
          argValues =
        .ok (sourceShared', resultValues))
    (state : EVMState) (values rest : EvmYul.Stack Word)
    (hArgsRun :
      ∀ {argsCode : Structured.Code},
        compileExprSeqCode? compileState.env valuesAboveBase args =
          some argsCode →
          ∃ mid,
            Structured.Code.run argsCode
                { state with stack := values ++ base :: rest } = .ok mid ∧
            mid.stack = argValues.reverse ++ values ++ base :: rest ∧
            ScratchRegionReady mid.toMachineState
              (range base words).base (range base words).words ∧
            SharedStateEqOutsideScratch (range base words) sourceShared
              mid.toSharedState ∧
            FrameStoreRel compileState.env store mid.toMachineState base) :
    ∃ final,
      resultValues.length = Expressions.Structured.BasicOp.outputs op ∧
      Structured.Code.run code
          { state with stack := values ++ base :: rest } = .ok final ∧
      final.stack = resultValues.reverse ++ values ++ base :: rest ∧
      ScratchRegionReady final.toMachineState
        (range base words).base (range base words).words ∧
      SharedStateEqOutsideScratch (range base words) sourceShared'
        final.toSharedState ∧
      FrameStoreRel compileState.env store final.toMachineState base := by
  simp [compileExprCode?] at hCompile
  cases hArgsCode :
      compileExprSeqCode? compileState.env valuesAboveBase args with
  | none =>
      simp [hArgsCode] at hCompile
  | some argsCode =>
      simp [hArgsCode] at hCompile
      cases hCompile
      rcases hArgsRun hArgsCode with
        ⟨mid, hRunArgs, hMidStack, hReadyMid, hSharedMid, hRelMid⟩
      rcases
          Locals.SourceLowering.PrimitiveSemantics.structuredScratchSound.eval_step_exists
            (range := range base words)
            (op := op)
            (sourceShared := sourceShared)
            (sourceShared' := sourceShared')
            (targetShared := mid.toSharedState)
            (values := argValues)
            (values' := resultValues)
            (evm := mid)
            (baseStack := values ++ base :: rest)
            hNoMem hPrimEval hSharedMid hReadyMid rfl
            (by simpa [List.append_assoc] using hMidStack) with
        ⟨final, hStep, hSharedFinal, hReadyFinal, hMachineFinal,
          hFinalStack⟩
      refine ⟨final, ?_, ?_, ?_, hReadyFinal, hSharedFinal, ?_⟩
      · exact
          Locals.SourceLowering.PrimitiveSemantics.structuredScratchSound.eval_length
            hPrimEval
      · rw [Structured.Preservation.Code.run_append, hRunArgs]
        simp [Structured.Code.run, Structured.BasicInstr.step, hStep]
      · simpa [List.append_assoc] using hFinalStack
      · rw [hMachineFinal]
        exact hRelMid

mutual
  theorem run_compileExprCode?_frameStore_of_source_eval :
      ∀ {results : Nat} {expr : Expr results}
        {compileState : CompileState}
        {source source' : Locals.Source.State}
        {state : EVMState} {base : Word} {words valuesAboveBase : Nat}
        {front rest : EvmYul.Stack Word}
        {resultValues : List Word} {code : Structured.Code},
        SourceExprSafe expr →
        Locals.Source.Expr.eval Locals.Source.PrimitiveSemantics.structured
          expr source = .ok (source', resultValues) →
        compileExprCode? compileState.env valuesAboveBase expr = some code →
        StateSlotsBounded compileState →
        compileState.nextSlot ≤ words →
        ScratchRegionReady state.toMachineState
          (range base words).base (range base words).words →
        SharedStateEqOutsideScratch (range base words) source.shared
          state.toSharedState →
        FrameStoreRel compileState.env source.vars state.toMachineState base →
        front.length = valuesAboveBase →
          ∃ final,
            resultValues.length = results ∧
            Structured.Code.run code
                { state with stack := front ++ base :: rest } = .ok final ∧
            final.stack = resultValues.reverse ++ front ++ base :: rest ∧
            ScratchRegionReady final.toMachineState
              (range base words).base (range base words).words ∧
            SharedStateEqOutsideScratch (range base words) source'.shared
              final.toSharedState ∧
            FrameStoreRel compileState.env source'.vars
              final.toMachineState base := by
    intro results expr compileState source source' state base words
      valuesAboveBase front rest resultValues code hSafe hEval hCompile
      hStateBound hFrameWords hReady hShared hRel hPrefixLen
    cases expr with
    | lit value =>
        simp [Locals.Source.Expr.eval] at hEval
        rcases hEval with ⟨rfl, rfl⟩
        rcases
            run_compileExprCode?_lit_frameStore_shared
              hCompile hReady state hShared hRel front rest rfl hPrefixLen with
          ⟨final, hRun, hStack, hReadyFinal, hSharedFinal, hRelFinal⟩
        refine ⟨final, ?_, hRun, ?_, hReadyFinal, ?_, ?_⟩
        · simp
        · simpa using hStack
        · simpa using hSharedFinal
        · exact hRelFinal
    | var name =>
        unfold Locals.Source.Expr.eval at hEval
        cases hStore : source.vars name with
        | none =>
            simp [hStore, Locals.Source.invalid] at hEval
            cases hEval
        | some value =>
            simp [hStore] at hEval
            rcases hEval with ⟨rfl, rfl⟩
            rcases
                run_compileExprCode?_var_frameStore_lookup_shared_of_stateSlots
                  hCompile hStateBound hFrameWords hReady state hShared hRel
                  front rest rfl hPrefixLen with
              ⟨loaded, final, hStoreLoaded, hRun, hStack, hReadyFinal,
                hSharedFinal, hRelFinal⟩
            have hLoaded : loaded = value := by
              rw [hStore] at hStoreLoaded
              cases hStoreLoaded
              rfl
            subst loaded
            refine ⟨final, ?_, hRun, ?_, hReadyFinal, ?_, ?_⟩
            · simp
            · simpa using hStack
            · simpa using hSharedFinal
            · exact hRelFinal
    | code raw =>
        simp [SourceExprSafe] at hSafe
        cases hSafe
    | prim op args =>
        simp [SourceExprSafe] at hSafe
        rcases hSafe with ⟨hOpSafe, hArgsSafe⟩
        unfold Locals.Source.Expr.eval at hEval
        cases hArgsEval :
            Locals.Source.Expr.ExprSeq.eval
              Locals.Source.PrimitiveSemantics.structured args source with
        | error err =>
            simp [hArgsEval] at hEval
        | ok argsResult =>
            rcases argsResult with ⟨sourceAfterArgs, argValues⟩
            simp [hArgsEval] at hEval
            cases hPrimEval :
                Locals.Source.PrimitiveSemantics.structured.eval op
                  sourceAfterArgs.shared argValues with
            | error err =>
                simp [hPrimEval] at hEval
            | ok primResult =>
                rcases primResult with ⟨shared', primValues⟩
                simp [hPrimEval] at hEval
                rcases hEval with ⟨rfl, rfl⟩
                rcases
                    run_compileExprCode?_prim_frameStore_of_args
                      (compileState := compileState)
                      (store := sourceAfterArgs.vars)
                      (base := base)
                      (words := words)
                      (valuesAboveBase := valuesAboveBase)
                      (op := op)
                      (args := args)
                      (code := code)
                      (sourceShared := sourceAfterArgs.shared)
                      (sourceShared' := shared')
                      (argValues := argValues)
                      (resultValues := primValues)
                      hCompile hOpSafe hPrimEval state front rest
                      (fun {argsCode} hArgsCode =>
                        by
                          rcases
                              run_compileExprSeqCode?_frameStore_of_source_eval
                                hArgsSafe hArgsEval hArgsCode hStateBound
                                hFrameWords hReady hShared hRel hPrefixLen with
                            ⟨mid, _hArgLen, hRunArgs, hMidStack, hReadyMid,
                              hSharedMid, hRelMid⟩
                          exact
                            ⟨mid, hRunArgs, hMidStack, hReadyMid, hSharedMid,
                              hRelMid⟩) with
                  ⟨final, hResultLen, hRun, hStack, hReadyFinal,
                    hSharedFinal, hRelFinal⟩
                refine ⟨final, hResultLen, hRun, hStack, hReadyFinal, ?_, ?_⟩
                · simpa only [Locals.Source.State.withShared] using
                    hSharedFinal
                · change
                    FrameStoreRel compileState.env sourceAfterArgs.vars
                      final.toMachineState base
                  exact hRelFinal

  theorem run_compileExprSeqCode?_frameStore_of_source_eval :
      ∀ {results : Nat} {exprs : Locals.ExprSeq results}
        {compileState : CompileState}
        {source source' : Locals.Source.State}
        {state : EVMState} {base : Word} {words valuesAboveBase : Nat}
        {front rest : EvmYul.Stack Word}
        {resultValues : List Word} {code : Structured.Code},
        SourceExprSeqSafe exprs →
        Locals.Source.Expr.ExprSeq.eval
          Locals.Source.PrimitiveSemantics.structured exprs source =
            .ok (source', resultValues) →
        compileExprSeqCode? compileState.env valuesAboveBase exprs =
          some code →
        StateSlotsBounded compileState →
        compileState.nextSlot ≤ words →
        ScratchRegionReady state.toMachineState
          (range base words).base (range base words).words →
        SharedStateEqOutsideScratch (range base words) source.shared
          state.toSharedState →
        FrameStoreRel compileState.env source.vars state.toMachineState base →
        front.length = valuesAboveBase →
          ∃ final,
            resultValues.length = results ∧
            Structured.Code.run code
                { state with stack := front ++ base :: rest } = .ok final ∧
            final.stack = resultValues.reverse ++ front ++ base :: rest ∧
            ScratchRegionReady final.toMachineState
              (range base words).base (range base words).words ∧
            SharedStateEqOutsideScratch (range base words) source'.shared
              final.toSharedState ∧
            FrameStoreRel compileState.env source'.vars
              final.toMachineState base := by
    intro results exprs compileState source source' state base words
      valuesAboveBase front rest resultValues code hSafe hEval hCompile
      hStateBound hFrameWords hReady hShared hRel hPrefixLen
    cases exprs with
    | nil =>
        simp [Locals.Source.Expr.ExprSeq.eval] at hEval
        rcases hEval with ⟨rfl, rfl⟩
        rcases
            run_compileExprSeqCode?_nil_frameStore_shared
              hCompile hReady state hShared hRel front rest rfl
              hPrefixLen with
          ⟨final, hRun, hStack, hReadyFinal, hSharedFinal, hRelFinal⟩
        refine ⟨final, ?_, hRun, ?_, hReadyFinal, ?_, ?_⟩
        · simp
        · simpa using hStack
        · simpa using hSharedFinal
        · exact hRelFinal
    | @cons left right head tail =>
        simp [SourceExprSeqSafe] at hSafe
        rcases hSafe with ⟨hHeadSafe, hTailSafe⟩
        unfold Locals.Source.Expr.ExprSeq.eval at hEval
        cases hHeadEval :
            Locals.Source.Expr.eval
              Locals.Source.PrimitiveSemantics.structured head source with
        | error err =>
            simp [hHeadEval] at hEval
        | ok headResult =>
            rcases headResult with ⟨sourceAfterHead, headValues⟩
            simp [hHeadEval] at hEval
            cases hTailEval :
                Locals.Source.Expr.ExprSeq.eval
                  Locals.Source.PrimitiveSemantics.structured tail
                    sourceAfterHead with
            | error err =>
                simp [hTailEval] at hEval
            | ok tailResult =>
                rcases tailResult with ⟨sourceAfterTail, tailValues⟩
                simp [hTailEval] at hEval
                rcases hEval with ⟨rfl, rfl⟩
                simp [compileExprSeqCode?] at hCompile
                cases hHeadCode :
                    compileExprCode? compileState.env valuesAboveBase
                      head with
                | none =>
                    simp [hHeadCode] at hCompile
                | some headCode =>
                    cases hTailCode :
                        compileExprSeqCode? compileState.env
                          (valuesAboveBase + left) tail with
                    | none =>
                        simp [hHeadCode, hTailCode] at hCompile
                    | some tailCode =>
                        simp [hHeadCode, hTailCode] at hCompile
                        cases hCompile
                        rcases
                            run_compileExprCode?_frameStore_of_source_eval
                              hHeadSafe hHeadEval hHeadCode hStateBound
                              hFrameWords hReady hShared hRel hPrefixLen with
                          ⟨mid, hHeadLen, hRunHead, hMidStack, hReadyMid,
                            hSharedMid, hRelMid⟩
                        have hTailPrefixLen :
                            (headValues.reverse ++ front).length =
                              valuesAboveBase + left := by
                          simp [List.length_reverse, hHeadLen, hPrefixLen]
                          omega
                        rcases
                            run_compileExprSeqCode?_frameStore_of_source_eval
                              (exprs := tail)
                              (compileState := compileState)
                              (source := sourceAfterHead)
                              (source' := sourceAfterTail)
                              (state := mid)
                              (base := base)
                              (words := words)
                              (valuesAboveBase := valuesAboveBase + left)
                              (front := headValues.reverse ++ front)
                              (rest := rest)
                              (resultValues := tailValues)
                              (code := tailCode)
                              hTailSafe hTailEval hTailCode hStateBound
                              hFrameWords hReadyMid hSharedMid hRelMid
                              hTailPrefixLen with
                          ⟨final, hTailLen, hRunTail, hFinalStack,
                            hReadyFinal, hSharedFinal, hRelFinal⟩
                        refine
                          ⟨final, ?_, ?_, ?_, hReadyFinal, hSharedFinal,
                            hRelFinal⟩
                        · simp [hHeadLen, hTailLen]
                        · rw [Structured.Preservation.Code.run_append,
                            hRunHead]
                          have hMidStart :
                              ({ mid with
                                stack :=
                                  headValues.reverse ++ (front ++
                                    base :: rest) } : EVMState) = mid := by
                            cases mid
                            simp at hMidStack ⊢
                            simpa [List.append_assoc] using hMidStack.symm
                          simpa [hMidStart, List.append_assoc] using hRunTail
                        · simpa [List.reverse_append, List.append_assoc]
                            using hFinalStack
end

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
    ⟨final, hRun, hStack, hFinalMachine, _hFinalShared⟩
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

theorem run_storeTopSlotCode?_frameStore_assign_shared_of_stateSlots
    (hSpec : ZeroPaddingSpec)
    (hWordBytes : WordByteEncodingSpec)
    {compileState : CompileState} {store : Locals.Source.Store}
    {machine : EvmYul.MachineState} {base : Word} {words : Nat}
    {sourceShared : EvmYul.SharedState .EVM}
    {name : Name} {slot valuesAboveBase : Nat}
    {code : Structured.Code} {value : Word}
    (hCode : storeTopSlotCode? valuesAboveBase slot = some code)
    (hStateBound : StateSlotsBounded compileState)
    (hStateNodup : StateSlotsNodup compileState)
    (hFrameWords : compileState.nextSlot ≤ words)
    (hReady : ScratchRegionReady machine (range base words).base
      (range base words).words)
    (state : EVMState)
    (hShared : SharedStateEqOutsideScratch (range base words) sourceShared
      state.toSharedState)
    (hRel : FrameStoreRel compileState.env store machine base)
    (hLookup : lookupSlot? name compileState.env = some slot)
    (tail rest : EvmYul.Stack Word)
    (hMachine : state.toMachineState = machine)
    (hValues : (value :: tail).length = valuesAboveBase) :
    ∃ final,
      Structured.Code.run code
          { state with stack := (value :: tail) ++ base :: rest } =
        .ok final ∧
      final.stack = tail ++ base :: rest ∧
      ScratchRegionReady final.toMachineState
        (range base words).base (range base words).words ∧
      SharedStateEqOutsideScratch (range base words) sourceShared
        final.toSharedState ∧
      FrameStoreRel compileState.env
        (Locals.Source.Store.insert store name value)
        final.toMachineState base := by
  have hBound : EnvSlotsBounded compileState.env words :=
    envSlotsBounded_of_stateSlotsBounded_le hStateBound hFrameWords
  have hNoDup : (slotList compileState.env).Nodup :=
    slotList_nodup_of_stateSlotsNodup hStateNodup
  rcases run_storeTopSlotCode? hCode state value tail rest base hValues with
    ⟨final, hRun, hStack, hFinalMachine, hFinalSharedRaw⟩
  have hSlot : slot < words :=
    lookupSlot?_lt_of_bounded hBound hLookup
  have hReadyStored :
      ScratchRegionReady
        (machine.mstore (base + slotOffset slot) value)
        (range base words).base (range base words).words :=
    mstore_generated_slot_ready hSpec hWordBytes hReady hSlot
  have hRelStored :
      FrameStoreRel compileState.env
        (Locals.Source.Store.insert store name value)
        (machine.mstore (base + slotOffset slot) value) base :=
    FrameStoreRel.mstore_insert hSpec hWordBytes hBound hReady hRel
      hLookup
      (fun hOtherLookup =>
        lookupSlot?_noAlias_of_slotList_nodup hNoDup hLookup hOtherLookup)
  have hSharedStored :
      SharedStateEqOutsideScratch (range base words) sourceShared
        ({ state with
          toMachineState :=
            state.toMachineState.mstore (base + slotOffset slot) value } :
          EVMState).toSharedState := by
    have hSlotRange : slot < (range base words).words := by
      simpa [range] using hSlot
    have hTargetStore :
        SharedStateEqOutsideScratch (range base words) sourceShared
          ({ state.toSharedState with
            toMachineState :=
              state.toSharedState.toMachineState.mstore
                ((range base words).word slot) value } :
            EvmYul.SharedState .EVM) :=
      Locals.SourceLowering.StateRel.SpillScratch.SharedStateEqOutsideScratch.mstore_target_scratch_slot
        hSpec hWordBytes hShared
        (by simpa [hMachine] using hReady) hSlotRange
    cases state
    simpa [generatedAddress_eq_range_word base words slot] using hTargetStore
  refine ⟨final, hRun, hStack, ?_, ?_, ?_⟩
  · rw [hFinalMachine, hMachine]
    exact hReadyStored
  · rw [hFinalSharedRaw]
    exact hSharedStored
  · rw [hFinalMachine, hMachine]
    exact hRelStored

theorem run_storeTopSlotCode?_frameStore_let_shared_of_allocateName
    (hSpec : ZeroPaddingSpec)
    (hWordBytes : WordByteEncodingSpec)
    {compileState stateAfter : CompileState}
    {store : Locals.Source.Store}
    {machine : EvmYul.MachineState} {base : Word} {words : Nat}
    {sourceShared : EvmYul.SharedState .EVM}
    {name : Name} {slot valuesAboveBase : Nat}
    {code : Structured.Code} {value : Word}
    (hCode : storeTopSlotCode? valuesAboveBase slot = some code)
    (hAlloc : allocateName name compileState = (slot, stateAfter))
    (hStateBound : StateSlotsBounded compileState)
    (hFrameWords : stateAfter.nextSlot ≤ words)
    (hReady : ScratchRegionReady machine (range base words).base
      (range base words).words)
    (state : EVMState)
    (hShared : SharedStateEqOutsideScratch (range base words) sourceShared
      state.toSharedState)
    (hRel : FrameStoreRel compileState.env store machine base)
    (tail rest : EvmYul.Stack Word)
    (hMachine : state.toMachineState = machine)
    (hValues : (value :: tail).length = valuesAboveBase) :
    ∃ final,
      Structured.Code.run code
          { state with stack := (value :: tail) ++ base :: rest } =
        .ok final ∧
      final.stack = tail ++ base :: rest ∧
      ScratchRegionReady final.toMachineState
        (range base words).base (range base words).words ∧
      SharedStateEqOutsideScratch (range base words) sourceShared
        final.toSharedState ∧
      FrameStoreRel stateAfter.env
        (Locals.Source.Store.insert store name value)
        final.toMachineState base := by
  rcases run_storeTopSlotCode? hCode state value tail rest base hValues with
    ⟨final, hRun, hStack, hFinalMachine, hFinalSharedRaw⟩
  have hSlot : slot < words := by
    cases compileState with
    | mk env nextSlot =>
        change
          (nextSlot,
            { env := (name, nextSlot) :: env
              nextSlot := nextSlot + 1 }) = (slot, stateAfter) at hAlloc
        cases hAlloc
        have hFrameWords' : slot + 1 ≤ words := by
          simpa using hFrameWords
        omega
  have hReadyStored :
      ScratchRegionReady
        (machine.mstore (base + slotOffset slot) value)
        (range base words).base (range base words).words :=
    mstore_generated_slot_ready hSpec hWordBytes hReady hSlot
  have hRelStored :
      FrameStoreRel stateAfter.env
        (Locals.Source.Store.insert store name value)
        (machine.mstore (base + slotOffset slot) value) base :=
    FrameStoreRel.mstore_allocateName_insert hSpec hWordBytes hAlloc
      hStateBound hFrameWords hReady hRel
  have hSharedStored :
      SharedStateEqOutsideScratch (range base words) sourceShared
        ({ state with
          toMachineState :=
            state.toMachineState.mstore (base + slotOffset slot) value } :
          EVMState).toSharedState := by
    have hSlotRange : slot < (range base words).words := by
      simpa [range] using hSlot
    have hTargetStore :
        SharedStateEqOutsideScratch (range base words) sourceShared
          ({ state.toSharedState with
            toMachineState :=
              state.toSharedState.toMachineState.mstore
                ((range base words).word slot) value } :
            EvmYul.SharedState .EVM) :=
      Locals.SourceLowering.StateRel.SpillScratch.SharedStateEqOutsideScratch.mstore_target_scratch_slot
        hSpec hWordBytes hShared
        (by simpa [hMachine] using hReady) hSlotRange
    cases state
    simpa [generatedAddress_eq_range_word base words slot] using hTargetStore
  refine ⟨final, hRun, hStack, ?_, ?_, ?_⟩
  · rw [hFinalMachine, hMachine]
    exact hReadyStored
  · rw [hFinalSharedRaw]
    exact hSharedStored
  · rw [hFinalMachine, hMachine]
    exact hRelStored

theorem source_evalOne_eq_eval_singleton
    {source source' : Locals.Source.State} {value : Word}
    {expr : Expr 1}
    (hEvalOne :
      Locals.Source.Expr.evalOne
          Locals.Source.PrimitiveSemantics.structured expr source =
        .ok (source', value)) :
    Locals.Source.Expr.eval Locals.Source.PrimitiveSemantics.structured
      expr source = .ok (source', [value]) := by
  unfold Locals.Source.Expr.evalOne at hEvalOne
  cases hExprEval :
      Locals.Source.Expr.eval Locals.Source.PrimitiveSemantics.structured
        expr source with
  | error err =>
      simp_all [Locals.Source.invalid]
  | ok exprResult =>
      rcases exprResult with ⟨sourceAfterExpr, values⟩
      cases values with
      | nil =>
          simp_all [Locals.Source.invalid]
          cases hEvalOne
      | cons head tail =>
          cases tail with
          | nil =>
              simp_all
          | cons second tail =>
              simp_all [Locals.Source.invalid]
              cases hEvalOne

theorem run_compileStmt?_assign_frameStore_of_value_code
    (hSpec : ZeroPaddingSpec)
    (hWordBytes : WordByteEncodingSpec)
    {ctx : CompileCtx} {returns : List Name}
    {compileState : CompileState} {name : Name} {valueExpr : Expr 1}
    {plan : Plan} {store : Locals.Source.Store}
    {evmState : EVMState} {base : Word} {words : Nat}
    (hCompile :
      compileStmt? ctx returns compileState (.assign name valueExpr) =
        some plan)
    (hStateBound : StateSlotsBounded compileState)
    (hStateNodup : StateSlotsNodup compileState)
    (hFrameWords : compileState.nextSlot ≤ words)
    (rest : EvmYul.Stack Word)
    (hValueRun :
      ∀ {valueCode : Structured.Code},
        compileExprCode? compileState.env 0 valueExpr = some valueCode →
          ∃ value mid,
            Structured.Code.run valueCode
                { evmState with stack := base :: rest } = .ok mid ∧
            mid.stack = value :: base :: rest ∧
            ScratchRegionReady mid.toMachineState
              (range base words).base (range base words).words ∧
            FrameStoreRel compileState.env store mid.toMachineState base) :
    ∃ value final code,
      plan.block = Block.ofCode code ∧
      Structured.Code.run code { evmState with stack := base :: rest } =
        .ok final ∧
      final.stack = base :: rest ∧
      ScratchRegionReady final.toMachineState
        (range base words).base (range base words).words ∧
      FrameStoreRel compileState.env
        (Locals.Source.Store.insert store name value)
        final.toMachineState base := by
  rcases
      compileStmt?_assign_target_slot_bounded hStateBound hCompile with
    ⟨slot, valueCode, storeCode, hLookup, _hSlot, hValueCode,
      hStoreCode, _hPlanState, hPlanBlock⟩
  rcases hValueRun hValueCode with
    ⟨value, mid, hRunValue, hMidStack, hReadyMid, hRelMid⟩
  rcases
      run_storeTopSlotCode?_frameStore_assign_of_stateSlots
        hSpec hWordBytes hStoreCode hStateBound hStateNodup hFrameWords
        hReadyMid hRelMid hLookup mid [] rest rfl (by simp)
        (value := value) with
    ⟨final, hRunStore, hFinalStack, hReadyFinal, hRelFinal⟩
  have hMidStart :
      ({ mid with stack := value :: base :: rest } : EVMState) = mid := by
    cases mid
    simp at hMidStack ⊢
    exact hMidStack.symm
  refine ⟨value, final, valueCode ++ storeCode, ?_, ?_, ?_, ?_, ?_⟩
  · exact hPlanBlock
  · rw [Structured.Preservation.Code.run_append, hRunValue]
    simpa [hMidStart] using hRunStore
  · simpa using hFinalStack
  · exact hReadyFinal
  · exact hRelFinal

theorem run_compileStmt?_assign_frameStore_of_source_evalOne
    (hSpec : ZeroPaddingSpec)
    (hWordBytes : WordByteEncodingSpec)
    {ctx : CompileCtx} {returns : List Name}
    {compileState : CompileState} {name : Name} {valueExpr : Expr 1}
    {plan : Plan}
    {source sourceAfterValue : Locals.Source.State} {value : Word}
    {evmState : EVMState} {base : Word} {words : Nat}
    (hCompile :
      compileStmt? ctx returns compileState (.assign name valueExpr) =
        some plan)
    (hSafe : SourceExprSafe valueExpr)
    (hEvalOne :
      Locals.Source.Expr.evalOne
          Locals.Source.PrimitiveSemantics.structured valueExpr source =
        .ok (sourceAfterValue, value))
    (hStateBound : StateSlotsBounded compileState)
    (hStateNodup : StateSlotsNodup compileState)
    (hFrameWords : compileState.nextSlot ≤ words)
    (hReady : ScratchRegionReady evmState.toMachineState
      (range base words).base (range base words).words)
    (hShared : SharedStateEqOutsideScratch (range base words) source.shared
      evmState.toSharedState)
    (hRel : FrameStoreRel compileState.env source.vars
      evmState.toMachineState base)
    (rest : EvmYul.Stack Word) :
    ∃ final code,
      plan.block = Block.ofCode code ∧
      Structured.Code.run code { evmState with stack := base :: rest } =
        .ok final ∧
      final.stack = base :: rest ∧
      ScratchRegionReady final.toMachineState
        (range base words).base (range base words).words ∧
      SharedStateEqOutsideScratch (range base words) sourceAfterValue.shared
        final.toSharedState ∧
      FrameStoreRel compileState.env
        (Locals.Source.Store.insert sourceAfterValue.vars name value)
        final.toMachineState base := by
  rcases
      compileStmt?_assign_target_slot_bounded hStateBound hCompile with
    ⟨slot, valueCode, storeCode, hLookup, _hSlot, hValueCode,
      hStoreCode, _hPlanState, hPlanBlock⟩
  have hExprEval :
      Locals.Source.Expr.eval Locals.Source.PrimitiveSemantics.structured
        valueExpr source = .ok (sourceAfterValue, [value]) :=
    source_evalOne_eq_eval_singleton hEvalOne
  rcases
      run_compileExprCode?_frameStore_of_source_eval
        (source := source)
        (source' := sourceAfterValue)
        (state := evmState)
        (base := base)
        (words := words)
        (valuesAboveBase := 0)
        (front := [])
        (rest := rest)
        (resultValues := [value])
        (code := valueCode)
        hSafe hExprEval hValueCode hStateBound hFrameWords
        hReady hShared hRel (by simp) with
    ⟨mid, _hValueLen, hRunValue, hMidStack, hReadyMid,
      hSharedMid, hRelMid⟩
  rcases
      run_storeTopSlotCode?_frameStore_assign_shared_of_stateSlots
        hSpec hWordBytes hStoreCode hStateBound hStateNodup
        hFrameWords hReadyMid mid hSharedMid hRelMid hLookup
        [] rest rfl (by simp) (value := value) with
    ⟨final, hRunStore, hFinalStack, hReadyFinal, hSharedFinal,
      hRelFinal⟩
  have hMidStart :
      ({ mid with stack := value :: base :: rest } : EVMState) =
        mid := by
    cases mid
    simp at hMidStack ⊢
    exact hMidStack.symm
  refine
    ⟨final, valueCode ++ storeCode, hPlanBlock, ?_, ?_,
      hReadyFinal, hSharedFinal, hRelFinal⟩
  · have hRunValueStart :
        Structured.Code.run valueCode
            { evmState with stack := base :: rest } = .ok mid := by
      simpa using hRunValue
    rw [Structured.Preservation.Code.run_append, hRunValueStart]
    simpa [hMidStart] using hRunStore
  · simpa using hFinalStack

theorem run_compileStmt?_expr_frameStore_of_source_eval
    {ctx : CompileCtx} {returns : List Name}
    {compileState : CompileState} {expr : Expr 0} {plan : Plan}
    {source source' : Locals.Source.State} {resultValues : List Word}
    {evmState : EVMState} {base : Word} {words : Nat}
    (hCompile :
      compileStmt? ctx returns compileState (.expr expr) = some plan)
    (hSafe : SourceExprSafe expr)
    (hEval :
      Locals.Source.Expr.eval Locals.Source.PrimitiveSemantics.structured
        expr source = .ok (source', resultValues))
    (hStateBound : StateSlotsBounded compileState)
    (hFrameWords : compileState.nextSlot ≤ words)
    (hReady : ScratchRegionReady evmState.toMachineState
      (range base words).base (range base words).words)
    (hShared : SharedStateEqOutsideScratch (range base words) source.shared
      evmState.toSharedState)
    (hRel : FrameStoreRel compileState.env source.vars
      evmState.toMachineState base)
    (rest : EvmYul.Stack Word) :
    ∃ final code,
      plan.state = compileState ∧
      plan.block = Block.ofCode code ∧
      Structured.Code.run code { evmState with stack := base :: rest } =
        .ok final ∧
      final.stack = base :: rest ∧
      ScratchRegionReady final.toMachineState
        (range base words).base (range base words).words ∧
      SharedStateEqOutsideScratch (range base words) source'.shared
        final.toSharedState ∧
      FrameStoreRel compileState.env source'.vars final.toMachineState base := by
  simp [compileStmt?] at hCompile
  cases hCode : compileExprCode? compileState.env 0 expr with
  | none =>
      simp [hCode] at hCompile
  | some code =>
      simp [hCode] at hCompile
      cases hCompile
      rcases
          run_compileExprCode?_frameStore_of_source_eval
            (source := source)
            (source' := source')
            (state := evmState)
            (base := base)
            (words := words)
            (valuesAboveBase := 0)
            (front := [])
            (rest := rest)
            (resultValues := resultValues)
            (code := code)
            hSafe hEval hCode hStateBound hFrameWords
            hReady hShared hRel (by simp) with
        ⟨final, hResultLen, hRun, hStack, hReadyFinal,
          hSharedFinal, hRelFinal⟩
      have hResultNil : resultValues = [] :=
        List.eq_nil_of_length_eq_zero hResultLen
      refine
        ⟨final, code, rfl, rfl, ?_, ?_, hReadyFinal, hSharedFinal,
          hRelFinal⟩
      · simpa using hRun
      · simpa [hResultNil] using hStack

theorem run_compileStmt?_let_frameStore_of_source_evalOne
    (hSpec : ZeroPaddingSpec)
    (hWordBytes : WordByteEncodingSpec)
    {ctx : CompileCtx} {returns : List Name}
    {compileState : CompileState} {name : Name} {valueExpr : Expr 1}
    {plan : Plan}
    {source sourceAfterValue : Locals.Source.State} {value : Word}
    {evmState : EVMState} {base : Word} {words : Nat}
    (hCompile :
      compileStmt? ctx returns compileState (.let_ name valueExpr) =
        some plan)
    (hSafe : SourceExprSafe valueExpr)
    (hEvalOne :
      Locals.Source.Expr.evalOne
          Locals.Source.PrimitiveSemantics.structured valueExpr source =
        .ok (sourceAfterValue, value))
    (hStateBound : StateSlotsBounded compileState)
    (hFrameWords : plan.state.nextSlot ≤ words)
    (hReady : ScratchRegionReady evmState.toMachineState
      (range base words).base (range base words).words)
    (hShared : SharedStateEqOutsideScratch (range base words) source.shared
      evmState.toSharedState)
    (hRel : FrameStoreRel compileState.env source.vars
      evmState.toMachineState base)
    (rest : EvmYul.Stack Word) :
    ∃ final code,
      plan.block = Block.ofCode code ∧
      Structured.Code.run code { evmState with stack := base :: rest } =
        .ok final ∧
      final.stack = base :: rest ∧
      ScratchRegionReady final.toMachineState
        (range base words).base (range base words).words ∧
      SharedStateEqOutsideScratch (range base words) sourceAfterValue.shared
        final.toSharedState ∧
      FrameStoreRel plan.state.env
        (Locals.Source.Store.insert sourceAfterValue.vars name value)
        final.toMachineState base := by
  simp [compileStmt?] at hCompile
  cases hValueCode : compileExprCode? compileState.env 0 valueExpr with
  | none =>
      simp [hValueCode] at hCompile
  | some valueCode =>
      cases hAlloc : allocateName name compileState with
      | mk slot stateAfter =>
          cases hStoreCode : storeTopSlotCode? 1 slot with
          | none =>
              simp [hValueCode, hAlloc, hStoreCode] at hCompile
          | some storeCode =>
              simp [hValueCode, hAlloc, hStoreCode] at hCompile
              cases hCompile
              have hOldFrameWords : compileState.nextSlot ≤ words := by
                have hMono :
                    compileState.nextSlot ≤ stateAfter.nextSlot := by
                  simpa [hAlloc] using
                    compileStmt?_nextSlot_mono
                      (ctx := ctx) (returns := returns)
                      (state := compileState)
                      (stmt := .let_ name valueExpr)
                      (plan :=
                        { state := stateAfter
                          block := Block.ofCode (valueCode ++ storeCode) })
                      (by
                        simp [compileStmt?, hValueCode, hAlloc,
                          hStoreCode])
                exact Nat.le_trans hMono hFrameWords
              have hExprEval :
                  Locals.Source.Expr.eval
                      Locals.Source.PrimitiveSemantics.structured
                      valueExpr source = .ok (sourceAfterValue, [value]) :=
                source_evalOne_eq_eval_singleton hEvalOne
              rcases
                  run_compileExprCode?_frameStore_of_source_eval
                    (source := source)
                    (source' := sourceAfterValue)
                    (state := evmState)
                    (base := base)
                    (words := words)
                    (valuesAboveBase := 0)
                    (front := [])
                    (rest := rest)
                    (resultValues := [value])
                    (code := valueCode)
                    hSafe hExprEval hValueCode hStateBound hOldFrameWords
                    hReady hShared hRel (by simp) with
                ⟨mid, _hValueLen, hRunValue, hMidStack, hReadyMid,
                  hSharedMid, hRelMid⟩
              rcases
                  run_storeTopSlotCode?_frameStore_let_shared_of_allocateName
                    hSpec hWordBytes hStoreCode hAlloc hStateBound
                    hFrameWords hReadyMid mid hSharedMid hRelMid
                    [] rest rfl (by simp) (value := value) with
                ⟨final, hRunStore, hFinalStack, hReadyFinal,
                  hSharedFinal, hRelFinal⟩
              have hMidStart :
                  ({ mid with stack := value :: base :: rest } : EVMState) =
                    mid := by
                cases mid
                simp at hMidStack ⊢
                exact hMidStack.symm
              refine
                ⟨final, valueCode ++ storeCode, rfl, ?_, ?_,
                  hReadyFinal, hSharedFinal, hRelFinal⟩
              · have hRunValueStart :
                    Structured.Code.run valueCode
                        { evmState with stack := base :: rest } = .ok mid := by
                  simpa using hRunValue
                rw [Structured.Preservation.Code.run_append, hRunValueStart]
                simpa [hMidStart] using hRunStore
              · simpa using hFinalStack

theorem run_compileStmt?_expr_frameStore_of_source_run_regular
    {ctx : CompileCtx} {returns : List Name}
    {compileState : CompileState} {expr : Expr 0} {plan : Plan}
    {program : Program}
    {source source' : Locals.Source.State}
    {sourceCtx sourceCtx' : EvmCompiler.Functions.Source.Ctx}
    {fuel : Nat}
    {evmState : EVMState} {base : Word} {words : Nat}
    (hCompile :
      compileStmt? ctx returns compileState (.expr expr) = some plan)
    (hSafe : SourceExprSafe expr)
    (hRun :
      EvmCompiler.Functions.Source.Stmt.run
          Locals.Source.PrimitiveSemantics.structured
          program sourceCtx fuel (.expr expr) source =
        .ok (EvmCompiler.Functions.Source.Outcome.regular source',
          sourceCtx'))
    (hStateBound : StateSlotsBounded compileState)
    (hFrameWords : compileState.nextSlot ≤ words)
    (hReady : ScratchRegionReady evmState.toMachineState
      (range base words).base (range base words).words)
    (hShared : SharedStateEqOutsideScratch (range base words) source.shared
      evmState.toSharedState)
    (hRel : FrameStoreRel compileState.env source.vars
      evmState.toMachineState base)
    (rest : EvmYul.Stack Word) :
    ∃ final code,
      plan.state = compileState ∧
      plan.block = Block.ofCode code ∧
      Structured.Code.run code { evmState with stack := base :: rest } =
        .ok final ∧
      final.stack = base :: rest ∧
      ScratchRegionReady final.toMachineState
        (range base words).base (range base words).words ∧
      SharedStateEqOutsideScratch (range base words) source'.shared
        final.toSharedState ∧
      FrameStoreRel compileState.env source'.vars final.toMachineState base := by
  unfold EvmCompiler.Functions.Source.Stmt.run at hRun
  cases hEval :
      Locals.Source.Expr.eval Locals.Source.PrimitiveSemantics.structured
        expr source with
  | error err =>
      simp [hEval] at hRun
  | ok result =>
      rcases result with ⟨sourceAfterExpr, resultValues⟩
      simp [hEval, EvmCompiler.Functions.Source.Outcome.regular] at hRun
      rcases hRun with ⟨hOutcome, _hCtx⟩
      cases hOutcome
      exact
        run_compileStmt?_expr_frameStore_of_source_eval
          hCompile hSafe hEval hStateBound hFrameWords hReady hShared
          hRel rest

theorem run_compileStmt?_let_frameStore_of_source_run_regular
    (hSpec : ZeroPaddingSpec)
    (hWordBytes : WordByteEncodingSpec)
    {ctx : CompileCtx} {returns : List Name}
    {compileState : CompileState} {name : Name} {valueExpr : Expr 1}
    {plan : Plan} {program : Program}
    {source source' : Locals.Source.State}
    {sourceCtx sourceCtx' : EvmCompiler.Functions.Source.Ctx}
    {fuel : Nat}
    {evmState : EVMState} {base : Word} {words : Nat}
    (hCompile :
      compileStmt? ctx returns compileState (.let_ name valueExpr) =
        some plan)
    (hSafe : SourceExprSafe valueExpr)
    (hRun :
      EvmCompiler.Functions.Source.Stmt.run
          Locals.Source.PrimitiveSemantics.structured
          program sourceCtx fuel (.let_ name valueExpr) source =
        .ok (EvmCompiler.Functions.Source.Outcome.regular source',
          sourceCtx'))
    (hStateBound : StateSlotsBounded compileState)
    (hFrameWords : plan.state.nextSlot ≤ words)
    (hReady : ScratchRegionReady evmState.toMachineState
      (range base words).base (range base words).words)
    (hShared : SharedStateEqOutsideScratch (range base words) source.shared
      evmState.toSharedState)
    (hRel : FrameStoreRel compileState.env source.vars
      evmState.toMachineState base)
    (rest : EvmYul.Stack Word) :
    ∃ final code,
      plan.block = Block.ofCode code ∧
      Structured.Code.run code { evmState with stack := base :: rest } =
        .ok final ∧
      final.stack = base :: rest ∧
      ScratchRegionReady final.toMachineState
        (range base words).base (range base words).words ∧
      SharedStateEqOutsideScratch (range base words) source'.shared
        final.toSharedState ∧
      FrameStoreRel plan.state.env source'.vars final.toMachineState base := by
  unfold EvmCompiler.Functions.Source.Stmt.run at hRun
  cases hEvalOne :
      Locals.Source.Expr.evalOne Locals.Source.PrimitiveSemantics.structured
        valueExpr source with
  | error err =>
      simp [hEvalOne] at hRun
  | ok result =>
      rcases result with ⟨sourceAfterValue, value⟩
      simp [hEvalOne, EvmCompiler.Functions.Source.Outcome.regular] at hRun
      rcases hRun with ⟨hOutcome, _hCtx⟩
      cases hOutcome
      rcases
          run_compileStmt?_let_frameStore_of_source_evalOne
            hSpec hWordBytes hCompile hSafe hEvalOne hStateBound
            hFrameWords hReady hShared hRel rest with
        ⟨final, code, hBlock, hRunCode, hStack, hReadyFinal,
          hSharedFinal, hRelFinal⟩
      refine
        ⟨final, code, hBlock, hRunCode, hStack, hReadyFinal, ?_, ?_⟩
      · change
          SharedStateEqOutsideScratch (range base words)
            sourceAfterValue.shared final.toSharedState
        exact hSharedFinal
      · change
          FrameStoreRel plan.state.env
            (Locals.Source.Store.insert sourceAfterValue.vars name value)
            final.toMachineState base
        exact hRelFinal

theorem run_compileStmt?_assign_frameStore_of_source_run_regular
    (hSpec : ZeroPaddingSpec)
    (hWordBytes : WordByteEncodingSpec)
    {ctx : CompileCtx} {returns : List Name}
    {compileState : CompileState} {name : Name} {valueExpr : Expr 1}
    {plan : Plan} {program : Program}
    {source source' : Locals.Source.State}
    {sourceCtx sourceCtx' : EvmCompiler.Functions.Source.Ctx}
    {fuel : Nat}
    {evmState : EVMState} {base : Word} {words : Nat}
    (hCompile :
      compileStmt? ctx returns compileState (.assign name valueExpr) =
        some plan)
    (hSafe : SourceExprSafe valueExpr)
    (hRun :
      EvmCompiler.Functions.Source.Stmt.run
          Locals.Source.PrimitiveSemantics.structured
          program sourceCtx fuel (.assign name valueExpr) source =
        .ok (EvmCompiler.Functions.Source.Outcome.regular source',
          sourceCtx'))
    (hStateBound : StateSlotsBounded compileState)
    (hStateNodup : StateSlotsNodup compileState)
    (hFrameWords : compileState.nextSlot ≤ words)
    (hReady : ScratchRegionReady evmState.toMachineState
      (range base words).base (range base words).words)
    (hShared : SharedStateEqOutsideScratch (range base words) source.shared
      evmState.toSharedState)
    (hRel : FrameStoreRel compileState.env source.vars
      evmState.toMachineState base)
    (rest : EvmYul.Stack Word) :
    ∃ final code,
      plan.block = Block.ofCode code ∧
      Structured.Code.run code { evmState with stack := base :: rest } =
        .ok final ∧
      final.stack = base :: rest ∧
      ScratchRegionReady final.toMachineState
        (range base words).base (range base words).words ∧
      SharedStateEqOutsideScratch (range base words) source'.shared
        final.toSharedState ∧
      FrameStoreRel compileState.env source'.vars final.toMachineState base := by
  unfold EvmCompiler.Functions.Source.Stmt.run at hRun
  cases hContains : source.vars.contains name with
  | false =>
      simp [hContains, EvmCompiler.Functions.Source.invalid,
        Structured.invalid] at hRun
  | true =>
      cases hEvalOne :
          Locals.Source.Expr.evalOne
            Locals.Source.PrimitiveSemantics.structured valueExpr source with
      | error err =>
          simp [hContains, hEvalOne] at hRun
      | ok result =>
          rcases result with ⟨sourceAfterValue, value⟩
          simp [hContains, hEvalOne,
            EvmCompiler.Functions.Source.Outcome.regular] at hRun
          rcases hRun with ⟨hOutcome, _hCtx⟩
          cases hOutcome
          rcases
              run_compileStmt?_assign_frameStore_of_source_evalOne
                hSpec hWordBytes hCompile hSafe hEvalOne hStateBound
                hStateNodup hFrameWords hReady hShared hRel rest with
            ⟨final, code, hBlock, hRunCode, hStack, hReadyFinal,
              hSharedFinal, hRelFinal⟩
          refine
            ⟨final, code, hBlock, hRunCode, hStack, hReadyFinal, ?_, ?_⟩
          · change
              SharedStateEqOutsideScratch (range base words)
                sourceAfterValue.shared final.toSharedState
            exact hSharedFinal
          · change
              FrameStoreRel compileState.env
                (Locals.Source.Store.insert sourceAfterValue.vars name value)
                final.toMachineState base
            exact hRelFinal

theorem run_blockOfCode_regular_of_code_run
    {program : Expressions.Program} {fuel : Nat}
    {code : Structured.Code} {state : Expressions.RunState}
    {final : EVMState}
    (hRun : Structured.Code.run code state.evm = .ok final) :
    Expressions.Block.run program (fuel + 2) (Block.ofCode code) state =
      .ok (Expressions.Outcome.regular (state.withEVM final)) := by
  simp [Block.ofCode, Expressions.Block.run, Expressions.Stmt.run,
    Structured.Code.runState, hRun, Expressions.Outcome.regular]

theorem run_blockAppend_ofCode_regular_of_code_run
    {program : Expressions.Program} {fuel : Nat}
    {code : Structured.Code} {tail : Expressions.Block}
    {state : Expressions.RunState} {final : EVMState}
    (hRun : Structured.Code.run code state.evm = .ok final) :
    Expressions.Block.run program (fuel + 2)
        (Block.append (Block.ofCode code) tail) state =
      Expressions.Block.run program (fuel + 1) tail (state.withEVM final) := by
  cases tail
  simp [Block.append, Block.ofCode, Expressions.Block.run,
    Expressions.Stmt.run, Structured.Code.runState, hRun,
    Expressions.Outcome.regular]

theorem run_block_append_regular_of_prefix_run
    {program : Expressions.Program} {fuel : Nat}
    {pref suffix : List Expressions.Stmt}
    {state mid : Expressions.RunState}
    (hPrefix :
      Expressions.Block.run program (fuel + pref.length)
          { stmts := pref } state =
        .ok (Expressions.Outcome.regular mid)) :
    Expressions.Block.run program (fuel + pref.length)
        { stmts := pref ++ suffix } state =
      Expressions.Block.run program fuel { stmts := suffix } mid := by
  induction pref generalizing fuel state mid with
  | nil =>
      cases fuel with
      | zero =>
          simp [Expressions.Block.run, Expressions.invalid,
            Structured.invalid] at hPrefix
      | succ fuel' =>
          simp [Expressions.Block.run, Expressions.Outcome.regular] at hPrefix
          cases hPrefix
          simp
  | cons stmt rest ih =>
      have hFuel :
          fuel + (stmt :: rest).length =
            (fuel + rest.length) + 1 := by
        simp [Nat.add_assoc]
      rw [hFuel] at hPrefix ⊢
      simp [Expressions.Block.run] at hPrefix ⊢
      cases hStmt : Expressions.Stmt.run program (fuel + rest.length)
          stmt state with
      | error err =>
          simp [hStmt] at hPrefix
      | ok outcome =>
          cases outcome with
          | mk outcomeState outcomeMode =>
              cases outcomeMode with
              | regular =>
                  simp [hStmt] at hPrefix ⊢
                  exact ih hPrefix
              | brk =>
                  simp [hStmt, Expressions.Outcome.regular] at hPrefix
                  cases hPrefix
              | cont =>
                  simp [hStmt, Expressions.Outcome.regular] at hPrefix
                  cases hPrefix
              | leave =>
                  simp [hStmt, Expressions.Outcome.regular] at hPrefix
                  cases hPrefix
              | halt kind =>
                  simp [hStmt, Expressions.Outcome.regular] at hPrefix
                  cases hPrefix

mutual
  theorem compileNoVarExprCode?_eq_compileExprCode?_nil_of_source_safe :
      ∀ {results : Nat} (expr : Expr results) (valuesAboveBase : Nat),
        SourceExprSafe expr →
          compileNoVarExprCode? expr =
            compileExprCode? [] valuesAboveBase expr := by
    intro results expr valuesAboveBase hSafe
    cases expr with
    | lit value =>
        rfl
    | var name =>
        simp [compileNoVarExprCode?, compileExprCode?, lookupSlot?]
    | code raw =>
        simp [SourceExprSafe,
          Locals.SourceLowering.StateRel.SpillScratch.SourceNoMemoryTouch.ExprSafe]
          at hSafe
    | prim op args =>
        simp [SourceExprSafe] at hSafe
        rcases hSafe with ⟨_hOpSafe, hArgsSafe⟩
        have hArgs :=
          compileNoVarExprSeqCode?_eq_compileExprSeqCode?_nil_of_source_safe
            args valuesAboveBase hArgsSafe
        simp [compileNoVarExprCode?, compileExprCode?, hArgs]

  theorem compileNoVarExprSeqCode?_eq_compileExprSeqCode?_nil_of_source_safe :
      ∀ {results : Nat} (exprs : Locals.ExprSeq results)
        (valuesAboveBase : Nat),
        SourceExprSeqSafe exprs →
          compileNoVarExprSeqCode? exprs =
            compileExprSeqCode? [] valuesAboveBase exprs := by
    intro results exprs valuesAboveBase hSafe
    cases exprs with
    | nil =>
        rfl
    | @cons left right head tail =>
        simp [SourceExprSeqSafe] at hSafe
        rcases hSafe with ⟨hHeadSafe, hTailSafe⟩
        have hHead :=
          compileNoVarExprCode?_eq_compileExprCode?_nil_of_source_safe
            head valuesAboveBase hHeadSafe
        have hTail :=
          compileNoVarExprSeqCode?_eq_compileExprSeqCode?_nil_of_source_safe
            tail (valuesAboveBase + left) hTailSafe
        simp [compileNoVarExprSeqCode?, compileExprSeqCode?, hHead, hTail]
end

theorem compilePreludeStmt?_expr_compileExprCode_nil_of_source_safe
    {expr : Expr 0} {compiled : Expressions.Stmt}
    (hSafe : SourceExprSafe expr)
    (hCompile : compilePreludeStmt? (.expr expr) = some compiled) :
    ∃ code,
      compiled = Expressions.Stmt.code code ∧
        compileExprCode? [] 0 expr = some code := by
  simp [compilePreludeStmt?] at hCompile
  cases hNoVar : compileNoVarExprCode? expr with
  | none =>
      simp [hNoVar] at hCompile
  | some code =>
      simp [hNoVar] at hCompile
      cases hCompile
      have hEq :=
        compileNoVarExprCode?_eq_compileExprCode?_nil_of_source_safe
          expr 0 hSafe
      rw [hNoVar] at hEq
      exact ⟨code, rfl, hEq.symm⟩

theorem splitPrelude_atomic_source_safe_compileExprCode_nil :
    ∀ {stmts : List Stmt} {prelude : List Expressions.Stmt}
      {rest : List Stmt},
      AtomicStmtListSafe stmts →
      splitPrelude stmts = (prelude, rest) →
        ∀ compiled, compiled ∈ prelude →
          ∃ (expr : Expr 0) (code : Structured.Code),
            compiled = Expressions.Stmt.code code ∧
              SourceExprSafe expr ∧
                compileExprCode? [] 0 expr = some code
  | [], prelude, rest, _hSafe, hSplit, compiled, hMem => by
      simp [splitPrelude] at hSplit
      rcases hSplit with ⟨rfl, rfl⟩
      simp at hMem
  | stmt :: stmts, prelude, rest, hSafe, hSplit, query, hMem => by
      unfold splitPrelude at hSplit
      cases hPrelude : compilePreludeStmt? stmt with
      | none =>
          simp [hPrelude] at hSplit
          rcases hSplit with ⟨rfl, rfl⟩
          simp at hMem
      | some compiled =>
          cases hTail : splitPrelude stmts with
          | mk tailPrelude tailRest =>
              simp [hPrelude, hTail] at hSplit
              rcases hSplit with ⟨rfl, rfl⟩
              simp at hMem
              rcases hMem with hHead | hTailMem
              · cases hHead
                cases stmt with
                | expr expr =>
                    simp [AtomicStmtListSafe, AtomicStmtSafe] at hSafe
                    rcases hSafe with ⟨hHeadSafe, _hTailSafe⟩
                    rcases
                      compilePreludeStmt?_expr_compileExprCode_nil_of_source_safe
                        hHeadSafe hPrelude with
                      ⟨code, hCompiled, hCode⟩
                    exact ⟨expr, code, hCompiled, hHeadSafe, hCode⟩
                | let_ name value =>
                    simp [compilePreludeStmt?] at hPrelude
                | assign name value =>
                    simp [compilePreludeStmt?] at hPrelude
                | block body =>
                    simp [compilePreludeStmt?] at hPrelude
                | if_ cond body =>
                    simp [compilePreludeStmt?] at hPrelude
                | switch scrutinee cases defaultBody =>
                    simp [compilePreludeStmt?] at hPrelude
                | for_ init cond post body =>
                    simp [compilePreludeStmt?] at hPrelude
                | brk =>
                    simp [compilePreludeStmt?] at hPrelude
                | cont =>
                    simp [compilePreludeStmt?] at hPrelude
                | leave =>
                    simp [compilePreludeStmt?] at hPrelude
                | call targets functionName args =>
                    simp [compilePreludeStmt?] at hPrelude
                | terminal kind =>
                    simp [compilePreludeStmt?] at hPrelude
                | terminalArgs kind args =>
                    simp [compilePreludeStmt?] at hPrelude
              · have hTailSafe : AtomicStmtListSafe stmts := by
                  cases stmt with
                  | expr expr =>
                      simp [AtomicStmtListSafe, AtomicStmtSafe] at hSafe
                      exact hSafe.2
                  | let_ name value =>
                      simp [AtomicStmtListSafe, AtomicStmtSafe] at hSafe
                      exact hSafe.2
                  | assign name value =>
                      simp [AtomicStmtListSafe, AtomicStmtSafe] at hSafe
                      exact hSafe.2
                  | block body =>
                      simp [AtomicStmtListSafe, AtomicStmtSafe] at hSafe
                  | if_ cond body =>
                      simp [AtomicStmtListSafe, AtomicStmtSafe] at hSafe
                  | switch scrutinee cases defaultBody =>
                      simp [AtomicStmtListSafe, AtomicStmtSafe] at hSafe
                  | for_ init cond post body =>
                      simp [AtomicStmtListSafe, AtomicStmtSafe] at hSafe
                  | brk =>
                      simp [AtomicStmtListSafe, AtomicStmtSafe] at hSafe
                  | cont =>
                      simp [AtomicStmtListSafe, AtomicStmtSafe] at hSafe
                  | leave =>
                      simp [AtomicStmtListSafe, AtomicStmtSafe] at hSafe
                  | call targets functionName args =>
                      simp [AtomicStmtListSafe, AtomicStmtSafe] at hSafe
                  | terminal kind =>
                      simp [AtomicStmtListSafe, AtomicStmtSafe] at hSafe
                  | terminalArgs kind args =>
                      simp [AtomicStmtListSafe, AtomicStmtSafe] at hSafe
                exact
                  splitPrelude_atomic_source_safe_compileExprCode_nil
                    hTailSafe hTail query hTailMem

theorem stackStoreRel_nil_any {store : Locals.Source.Store} :
    Locals.SourceLowering.StackStoreRel [] store [] := by
  simp [Locals.SourceLowering.StackStoreRel]

mutual
  theorem compileNoVarExprCode?_eq_locals_compileCode_initial_of_source_safe :
      ∀ {results : Nat} (expr : Expr results) (offset : Nat),
        SourceExprSafe expr →
          compileNoVarExprCode? expr =
            Locals.Expr.compileCode Locals.Ctx.initial offset expr := by
    intro results expr offset hSafe
    cases expr with
    | lit value =>
        rfl
    | var name =>
        simp [compileNoVarExprCode?, Locals.Expr.compileCode,
          Locals.Ctx.initial, Locals.Layout.lookupDepth?,
          Locals.Layout.lookupDepthFrom]
    | code raw =>
        simp [SourceExprSafe,
          Locals.SourceLowering.StateRel.SpillScratch.SourceNoMemoryTouch.ExprSafe]
          at hSafe
    | prim op args =>
        simp [SourceExprSafe] at hSafe
        rcases hSafe with ⟨_hOpSafe, hArgsSafe⟩
        have hArgs :=
          compileNoVarExprSeqCode?_eq_locals_compileCode_initial_of_source_safe
            args offset hArgsSafe
        simp [compileNoVarExprCode?, Locals.Expr.compileCode, hArgs]

  theorem compileNoVarExprSeqCode?_eq_locals_compileCode_initial_of_source_safe :
      ∀ {results : Nat} (exprs : Locals.ExprSeq results) (offset : Nat),
        SourceExprSeqSafe exprs →
          compileNoVarExprSeqCode? exprs =
            Locals.ExprSeq.compileCode Locals.Ctx.initial offset exprs := by
    intro results exprs offset hSafe
    cases exprs with
    | nil =>
        rfl
    | @cons left right head tail =>
        simp [SourceExprSeqSafe] at hSafe
        rcases hSafe with ⟨hHeadSafe, hTailSafe⟩
        have hHead :=
          compileNoVarExprCode?_eq_locals_compileCode_initial_of_source_safe
            head offset hHeadSafe
        have hTail :=
          compileNoVarExprSeqCode?_eq_locals_compileCode_initial_of_source_safe
            tail (offset + left) hTailSafe
        simp [compileNoVarExprSeqCode?, Locals.ExprSeq.compileCode, hHead,
          hTail]
end

mutual
  theorem compileNoVarExprCode?_accessible_nil_of_source_safe :
      ∀ {results : Nat} (expr : Expr results) (offset : Nat)
        {code : Structured.Code},
        SourceExprSafe expr →
        compileNoVarExprCode? expr = some code →
          Locals.SourceLowering.Expr.Accessible [] offset expr := by
    intro results expr offset code hSafe hCompile
    cases expr with
    | lit value =>
        simp [Locals.SourceLowering.Expr.Accessible]
    | var name =>
        simp [compileNoVarExprCode?] at hCompile
    | code raw =>
        simp [SourceExprSafe,
          Locals.SourceLowering.StateRel.SpillScratch.SourceNoMemoryTouch.ExprSafe]
          at hSafe
    | prim op args =>
        simp [SourceExprSafe] at hSafe
        rcases hSafe with ⟨_hOpSafe, hArgsSafe⟩
        simp [compileNoVarExprCode?] at hCompile
        cases hArgs : compileNoVarExprSeqCode? args with
        | none =>
            simp [hArgs] at hCompile
        | some argsCode =>
            simp [hArgs] at hCompile
            exact
              compileNoVarExprSeqCode?_accessible_nil_of_source_safe
                args offset hArgsSafe hArgs

  theorem compileNoVarExprSeqCode?_accessible_nil_of_source_safe :
      ∀ {results : Nat} (exprs : Locals.ExprSeq results) (offset : Nat)
        {code : Structured.Code},
        SourceExprSeqSafe exprs →
        compileNoVarExprSeqCode? exprs = some code →
          Locals.SourceLowering.ExprSeq.Accessible [] offset exprs := by
    intro results exprs offset code hSafe hCompile
    cases exprs with
    | nil =>
        simp [Locals.SourceLowering.ExprSeq.Accessible]
    | @cons left right head tail =>
        simp [SourceExprSeqSafe] at hSafe
        rcases hSafe with ⟨hHeadSafe, hTailSafe⟩
        simp [compileNoVarExprSeqCode?] at hCompile
        cases hHead : compileNoVarExprCode? head with
        | none =>
            simp [hHead] at hCompile
        | some headCode =>
            cases hTail : compileNoVarExprSeqCode? tail with
            | none =>
                simp [hHead, hTail] at hCompile
            | some tailCode =>
                simp [hHead, hTail] at hCompile
                exact
                  ⟨compileNoVarExprCode?_accessible_nil_of_source_safe
                      head offset hHeadSafe hHead,
                    compileNoVarExprSeqCode?_accessible_nil_of_source_safe
                      tail (offset + left) hTailSafe hTail⟩
end

theorem run_compileNoVarExprCode?_of_source_eval_source_safe
    {results : Nat} {expr : Expr results} {code : Structured.Code}
    {source source' : Locals.Source.State} {values : List Word}
    {evm : EVMState}
    (hSafe : SourceExprSafe expr)
    (hCompile : compileNoVarExprCode? expr = some code)
    (hShared : evm.toSharedState = source.shared)
    (hEval :
      Locals.Source.Expr.eval Locals.Source.PrimitiveSemantics.structured
          expr source = .ok (source', values)) :
    ∃ evm',
      Structured.Code.run code evm = .ok evm' ∧
        evm'.toSharedState = source'.shared ∧
        evm'.stack = values.reverse ++ evm.stack := by
  have hOwned :
      Locals.Source.Expr.SourceOwned expr :=
    Locals.SourceLowering.StateRel.SpillScratch.SourceNoMemoryTouch.exprSafe_sourceOwned
      hSafe
  have hAccess :
      Locals.SourceLowering.Expr.Accessible [] evm.stack.length expr :=
    compileNoVarExprCode?_accessible_nil_of_source_safe
      expr evm.stack.length hSafe hCompile
  have hLocalCompile :
      Locals.Expr.compileCode Locals.Ctx.initial evm.stack.length expr =
        some code := by
    have hEq :=
      compileNoVarExprCode?_eq_locals_compileCode_initial_of_source_safe
        expr evm.stack.length hSafe
    rw [hCompile] at hEq
    exact hEq.symm
  have hPrefix :
      Locals.SourceLowering.StackPrefixRel [] source evm.stack evm := by
    exact ⟨hShared, [], by simp,
      stackStoreRel_nil_any (store := source.vars)⟩
  rcases
      Locals.SourceLowering.Expr.runCode_of_eval_sourceOwned
        Locals.SourceLowering.PrimitiveSemantics.structured_primitiveSound
        (layout := []) (ctx := Locals.Ctx.initial)
        (offset := evm.stack.length) (source := source)
        (source' := source') (values := values) (evm := evm)
        (stackPrefix := evm.stack)
        rfl (by simp) hOwned hAccess rfl hPrefix hEval with
    ⟨evm', hRunDirect, hRelFinal⟩
  have hRunEq :=
    Locals.Direct.Expr.runCode_eq_compileCode Locals.Ctx.initial
      evm.stack.length expr code evm hLocalCompile
  rw [hRunEq] at hRunDirect
  rcases hRelFinal with ⟨hSharedFinal, baseStack, hStack, hStackRel⟩
  have hBaseNil : baseStack = [] := by
    exact List.eq_nil_of_length_eq_zero hStackRel.1
  refine ⟨evm', hRunDirect, hSharedFinal, ?_⟩
  simpa [hBaseNil, List.append_assoc] using hStack

theorem run_compilePreludeStmt?_expr_block_of_source_eval_source_safe
    {program : Expressions.Program} {fuel : Nat}
    {expr : Expr 0} {compiled : Expressions.Stmt}
    {source source' : Locals.Source.State} {values : List Word}
    {runState : Expressions.RunState} {evm : EVMState}
    (hSafe : SourceExprSafe expr)
    (hCompile : compilePreludeStmt? (.expr expr) = some compiled)
    (hShared : evm.toSharedState = source.shared)
    (hEval :
      Locals.Source.Expr.eval Locals.Source.PrimitiveSemantics.structured
          expr source = .ok (source', values)) :
    ∃ evm',
      Expressions.Block.run program (fuel + 2) { stmts := [compiled] }
          { runState with evm := evm } =
        .ok (Expressions.Outcome.regular
          ({ runState with evm := evm' })) ∧
      evm'.toSharedState = source'.shared ∧
      evm'.stack = values.reverse ++ evm.stack := by
  unfold compilePreludeStmt? at hCompile
  cases hNoVar : compileNoVarExprCode? expr with
  | none =>
      simp [hNoVar] at hCompile
  | some code =>
      simp [hNoVar] at hCompile
      cases hCompile
      rcases
          run_compileNoVarExprCode?_of_source_eval_source_safe
            hSafe hNoVar hShared hEval with
        ⟨evm', hRun, hSharedFinal, hStackFinal⟩
      refine ⟨evm', ?_, hSharedFinal, hStackFinal⟩
      simpa [Block.ofCode] using
        (run_blockOfCode_regular_of_code_run
          (program := program) (fuel := fuel)
          (code := code) (state := { runState with evm := evm })
          (final := evm') hRun)

theorem run_compilePreludeStmt?_expr_stmt_of_source_eval_source_safe
    {program : Expressions.Program} {fuel : Nat}
    {expr : Expr 0} {compiled : Expressions.Stmt}
    {source source' : Locals.Source.State} {values : List Word}
    {runState : Expressions.RunState} {evm : EVMState}
    (hSafe : SourceExprSafe expr)
    (hCompile : compilePreludeStmt? (.expr expr) = some compiled)
    (hShared : evm.toSharedState = source.shared)
    (hEval :
      Locals.Source.Expr.eval Locals.Source.PrimitiveSemantics.structured
          expr source = .ok (source', values)) :
    ∃ evm',
      Expressions.Stmt.run program fuel compiled { runState with evm := evm } =
        .ok (Expressions.Outcome.regular
          ({ runState with evm := evm' })) ∧
      evm'.toSharedState = source'.shared ∧
      evm'.stack = evm.stack := by
  unfold compilePreludeStmt? at hCompile
  cases hNoVar : compileNoVarExprCode? expr with
  | none =>
      simp [hNoVar] at hCompile
  | some code =>
      simp [hNoVar] at hCompile
      cases hCompile
      rcases
          run_compileNoVarExprCode?_of_source_eval_source_safe
            hSafe hNoVar hShared hEval with
        ⟨evm', hRun, hSharedFinal, hStackFinal⟩
      have hOwned :
          Locals.Source.Expr.SourceOwned expr :=
        Locals.SourceLowering.StateRel.SpillScratch.SourceNoMemoryTouch.exprSafe_sourceOwned
          hSafe
      have hValuesLen :
          values.length = 0 :=
        Locals.SourceLowering.Expr.eval_length_of_sourceOwned
          Locals.SourceLowering.PrimitiveSemantics.structured_primitiveSound
          hOwned hEval
      have hValuesNil : values = [] :=
        List.eq_nil_of_length_eq_zero hValuesLen
      refine ⟨evm', ?_, hSharedFinal, ?_⟩
      · simp [Expressions.Stmt.run, Structured.Code.runState,
          Structured.RunState.withEVM, hRun]
      · simpa [hValuesNil] using hStackFinal

theorem run_splitPrelude_atomic_source_safe_prelude_block_of_source_run_open_regular :
    ∀ {stmts : List Stmt} {prelude : List Expressions.Stmt}
      {restSourceStmts : List Stmt}
      {sourceProgram : Program} {compiledProgram : Expressions.Program}
      {source finalSource : Locals.Source.State}
      {sourceCtx finalCtx : EvmCompiler.Functions.Source.Ctx}
      {sourceFuel targetFuel : Nat}
      {runState : Expressions.RunState} {evm : EVMState},
      AtomicStmtListSafe stmts →
      splitPrelude stmts = (prelude, restSourceStmts) →
      evm.toSharedState = source.shared →
      EvmCompiler.Functions.Source.Block.runOpen
          Locals.Source.PrimitiveSemantics.structured
          sourceProgram sourceCtx sourceFuel { stmts := stmts } source =
        .ok (EvmCompiler.Functions.Source.Outcome.regular finalSource,
          finalCtx) →
      ∃ sourceAfter sourceCtxAfter preludeEvm restFuel,
        Expressions.Block.run compiledProgram
            (targetFuel + prelude.length + 1)
            { stmts := prelude } { runState with evm := evm } =
          .ok (Expressions.Outcome.regular
            ({ runState with evm := preludeEvm })) ∧
        preludeEvm.toSharedState = sourceAfter.shared ∧
        preludeEvm.stack = evm.stack ∧
        EvmCompiler.Functions.Source.Block.runOpen
            Locals.Source.PrimitiveSemantics.structured
            sourceProgram sourceCtxAfter restFuel
            { stmts := restSourceStmts } sourceAfter =
          .ok (EvmCompiler.Functions.Source.Outcome.regular finalSource,
            finalCtx)
  | [], prelude, restSourceStmts, sourceProgram, compiledProgram,
      source, finalSource, sourceCtx, finalCtx, sourceFuel, targetFuel,
      runState, evm, _hSafe, hSplit, hShared, hRun => by
      simp [splitPrelude] at hSplit
      rcases hSplit with ⟨rfl, rfl⟩
      refine ⟨source, sourceCtx, evm, sourceFuel, ?_, hShared, rfl, hRun⟩
      cases targetFuel with
      | zero =>
          simp [Expressions.Block.run, Expressions.Outcome.regular]
      | succ targetFuel =>
          simp [Expressions.Block.run, Expressions.Outcome.regular]
  | stmt :: stmts, prelude, restSourceStmts, sourceProgram,
      compiledProgram, source, finalSource, sourceCtx, finalCtx, sourceFuel,
      targetFuel, runState, evm, hSafe, hSplit, hShared, hRun => by
      unfold splitPrelude at hSplit
      cases hPrelude : compilePreludeStmt? stmt with
      | none =>
          simp [hPrelude] at hSplit
          rcases hSplit with ⟨rfl, rfl⟩
          refine ⟨source, sourceCtx, evm, sourceFuel, ?_, hShared, rfl, hRun⟩
          cases targetFuel with
          | zero =>
              simp [Expressions.Block.run, Expressions.Outcome.regular]
          | succ targetFuel =>
              simp [Expressions.Block.run, Expressions.Outcome.regular]
      | some compiled =>
          cases hTail : splitPrelude stmts with
          | mk tailPrelude tailRest =>
              simp [hPrelude, hTail] at hSplit
              rcases hSplit with ⟨rfl, rfl⟩
              cases stmt with
              | expr expr =>
                  simp [AtomicStmtListSafe, AtomicStmtSafe] at hSafe
                  rcases hSafe with ⟨hHeadSafe, hTailSafe⟩
                  cases sourceFuel with
                  | zero =>
                      simp [EvmCompiler.Functions.Source.Block.runOpen,
                        EvmCompiler.Functions.Source.invalid,
                        Structured.invalid] at hRun
                  | succ sourceFuel' =>
                      simp [EvmCompiler.Functions.Source.Block.runOpen] at hRun
                      cases hEval :
                          Locals.Source.Expr.eval
                            Locals.Source.PrimitiveSemantics.structured
                            expr source with
                      | error err =>
                          simp [EvmCompiler.Functions.Source.Stmt.run, hEval]
                            at hRun
                      | ok evalResult =>
                          rcases evalResult with ⟨sourceAfterHead, values⟩
                          simp [EvmCompiler.Functions.Source.Stmt.run, hEval,
                            EvmCompiler.Functions.Source.Outcome.regular]
                            at hRun
                          rcases
                              run_compilePreludeStmt?_expr_stmt_of_source_eval_source_safe
                                (program := compiledProgram)
                                (fuel := targetFuel + tailPrelude.length + 1)
                                (runState := runState) (evm := evm)
                                hHeadSafe hPrelude hShared hEval with
                            ⟨evmAfterHead, hRunHead, hSharedHead,
                              hStackHead⟩
                          rcases
                              run_splitPrelude_atomic_source_safe_prelude_block_of_source_run_open_regular
                                (stmts := stmts) (prelude := tailPrelude)
                                (restSourceStmts := tailRest)
                                (sourceProgram := sourceProgram)
                                (compiledProgram := compiledProgram)
                                (source := sourceAfterHead)
                                (finalSource := finalSource)
                                (sourceCtx := sourceCtx)
                                (finalCtx := finalCtx)
                                (sourceFuel := sourceFuel')
                                (targetFuel := targetFuel)
                                (runState := runState)
                                (evm := evmAfterHead)
                                hTailSafe hTail hSharedHead hRun with
                            ⟨sourceAfterPrelude, sourceCtxAfter,
                              preludeEvm, restFuel, hRunTail,
                              hSharedPrelude, hStackPrelude, hRunRest⟩
                          refine
                            ⟨sourceAfterPrelude, sourceCtxAfter, preludeEvm,
                              restFuel, ?_, hSharedPrelude, ?_, hRunRest⟩
                          · have hFuel :
                                targetFuel +
                                    (compiled :: tailPrelude).length + 1 =
                                  (targetFuel + tailPrelude.length + 1) + 1 := by
                              simp
                              omega
                            rw [hFuel]
                            simp [Expressions.Block.run, hRunHead,
                              Expressions.Outcome.regular, hRunTail]
                          · simpa [hStackHead] using hStackPrelude
              | let_ name value =>
                  simp [compilePreludeStmt?] at hPrelude
              | assign name value =>
                  simp [compilePreludeStmt?] at hPrelude
              | block body =>
                  simp [compilePreludeStmt?] at hPrelude
              | if_ cond body =>
                  simp [compilePreludeStmt?] at hPrelude
              | switch scrutinee cases defaultBody =>
                  simp [compilePreludeStmt?] at hPrelude
              | for_ init cond post body =>
                  simp [compilePreludeStmt?] at hPrelude
              | brk =>
                  simp [compilePreludeStmt?] at hPrelude
              | cont =>
                  simp [compilePreludeStmt?] at hPrelude
              | leave =>
                  simp [compilePreludeStmt?] at hPrelude
              | call targets functionName args =>
                  simp [compilePreludeStmt?] at hPrelude
              | terminal kind =>
                  simp [compilePreludeStmt?] at hPrelude
              | terminalArgs kind args =>
                  simp [compilePreludeStmt?] at hPrelude

theorem splitPrelude_atomic_stmt_list_safe_rest :
    ∀ {stmts : List Stmt} {prelude : List Expressions.Stmt}
      {rest : List Stmt},
      AtomicStmtListSafe stmts →
      splitPrelude stmts = (prelude, rest) →
        AtomicStmtListSafe rest
  | [], prelude, rest, _hSafe, hSplit => by
      simp [splitPrelude] at hSplit
      rcases hSplit with ⟨rfl, rfl⟩
      trivial
  | stmt :: stmts, prelude, rest, hSafe, hSplit => by
      unfold splitPrelude at hSplit
      cases hPrelude : compilePreludeStmt? stmt with
      | none =>
          simp [hPrelude] at hSplit
          rcases hSplit with ⟨rfl, rfl⟩
          exact hSafe
      | some compiled =>
          cases hTail : splitPrelude stmts with
          | mk tailPrelude tailRest =>
              simp [hPrelude, hTail] at hSplit
              rcases hSplit with ⟨rfl, rfl⟩
              have hTailSafe : AtomicStmtListSafe stmts := by
                cases stmt with
                | expr expr =>
                    simp [AtomicStmtListSafe, AtomicStmtSafe] at hSafe
                    exact hSafe.2
                | let_ name value =>
                    simp [compilePreludeStmt?] at hPrelude
                | assign name value =>
                    simp [compilePreludeStmt?] at hPrelude
                | block body =>
                    simp [compilePreludeStmt?] at hPrelude
                | if_ cond body =>
                    simp [compilePreludeStmt?] at hPrelude
                | switch scrutinee cases defaultBody =>
                    simp [compilePreludeStmt?] at hPrelude
                | for_ init cond post body =>
                    simp [compilePreludeStmt?] at hPrelude
                | brk =>
                    simp [compilePreludeStmt?] at hPrelude
                | cont =>
                    simp [compilePreludeStmt?] at hPrelude
                | leave =>
                    simp [compilePreludeStmt?] at hPrelude
                | call targets functionName args =>
                    simp [compilePreludeStmt?] at hPrelude
                | terminal kind =>
                    simp [compilePreludeStmt?] at hPrelude
                | terminalArgs kind args =>
                    simp [compilePreludeStmt?] at hPrelude
              exact splitPrelude_atomic_stmt_list_safe_rest hTailSafe hTail

theorem run_compileStmtList?_nil_block_frameStore_of_source_run_open_regular
    {ctx : CompileCtx} {returns : List Name}
    {compileState : CompileState} {plan : Plan}
    {sourceProgram : Program} {compiledProgram : Expressions.Program}
    {source source' : Locals.Source.State}
    {sourceCtx sourceCtx' : EvmCompiler.Functions.Source.Ctx}
    {sourceFuel blockFuel : Nat}
    {runState : Expressions.RunState}
    {evmState : EVMState} {base : Word} {words : Nat}
    (hCompile :
      compileStmtList? ctx returns compileState [] = some plan)
    (hRun :
      EvmCompiler.Functions.Source.Block.runOpen
          Locals.Source.PrimitiveSemantics.structured
          sourceProgram sourceCtx sourceFuel { stmts := [] } source =
        .ok (EvmCompiler.Functions.Source.Outcome.regular source',
          sourceCtx'))
    (hReady : ScratchRegionReady evmState.toMachineState
      (range base words).base (range base words).words)
    (hShared : SharedStateEqOutsideScratch (range base words) source.shared
      evmState.toSharedState)
    (hRel : FrameStoreRel compileState.env source.vars
      evmState.toMachineState base)
    (rest : EvmYul.Stack Word) :
    plan.state = compileState ∧
      Expressions.Block.run compiledProgram (blockFuel + 1) plan.block
          { runState with evm := { evmState with stack := base :: rest } } =
        .ok (Expressions.Outcome.regular
          ({ runState with evm := { evmState with stack := base :: rest } })) ∧
      ScratchRegionReady evmState.toMachineState
        (range base words).base (range base words).words ∧
      SharedStateEqOutsideScratch (range base words) source'.shared
        evmState.toSharedState ∧
      FrameStoreRel compileState.env source'.vars evmState.toMachineState base := by
  simp [compileStmtList?] at hCompile
  cases hCompile
  cases sourceFuel with
  | zero =>
      simp [EvmCompiler.Functions.Source.Block.runOpen,
        EvmCompiler.Functions.Source.invalid, Structured.invalid] at hRun
  | succ fuel =>
      simp [EvmCompiler.Functions.Source.Block.runOpen,
        EvmCompiler.Functions.Source.Outcome.regular] at hRun
      rcases hRun with ⟨hOutcome, _hCtx⟩
      cases hOutcome
      exact ⟨rfl, by simp [Expressions.Block.run,
        Expressions.Outcome.regular], hReady, hShared, hRel⟩

set_option maxHeartbeats 1200000 in
theorem run_compileStmtList?_atomic_block_frameStore_of_source_run_open_regular
    (hSpec : ZeroPaddingSpec)
    (hWordBytes : WordByteEncodingSpec)
    {ctx : CompileCtx} {returns : List Name}
    {compileState : CompileState} {stmts : List Stmt} {plan : Plan}
    {sourceProgram : Program} {compiledProgram : Expressions.Program}
    {source source' : Locals.Source.State}
    {sourceCtx sourceCtx' : EvmCompiler.Functions.Source.Ctx}
    {sourceFuel blockFuel : Nat}
    {runState : Expressions.RunState}
    {evmState : EVMState} {base : Word} {words : Nat}
    (hCompile :
      compileStmtList? ctx returns compileState stmts = some plan)
    (hSafe : AtomicStmtListSafe stmts)
    (hRun :
      EvmCompiler.Functions.Source.Block.runOpen
          Locals.Source.PrimitiveSemantics.structured
          sourceProgram sourceCtx sourceFuel { stmts := stmts } source =
        .ok (EvmCompiler.Functions.Source.Outcome.regular source',
          sourceCtx'))
    (hStateBound : StateSlotsBounded compileState)
    (hStateNodup : StateSlotsNodup compileState)
    (hFrameWords : plan.state.nextSlot ≤ words)
    (hReady : ScratchRegionReady evmState.toMachineState
      (range base words).base (range base words).words)
    (hShared : SharedStateEqOutsideScratch (range base words) source.shared
      evmState.toSharedState)
    (hRel : FrameStoreRel compileState.env source.vars
      evmState.toMachineState base)
    (restStack : EvmYul.Stack Word) :
    ∃ final,
      Expressions.Block.run compiledProgram
          (blockFuel + 2 * stmts.length + 1) plan.block
          { runState with evm := { evmState with stack := base :: restStack } } =
        .ok (Expressions.Outcome.regular ({ runState with evm := final })) ∧
      final.stack = base :: restStack ∧
      ScratchRegionReady final.toMachineState
        (range base words).base (range base words).words ∧
      SharedStateEqOutsideScratch (range base words) source'.shared
        final.toSharedState ∧
      FrameStoreRel plan.state.env source'.vars final.toMachineState base := by
  induction stmts generalizing compileState plan source sourceCtx sourceFuel
      evmState blockFuel with
  | nil =>
        rcases
            run_compileStmtList?_nil_block_frameStore_of_source_run_open_regular
              (compiledProgram := compiledProgram)
              (runState := runState)
              (evmState := evmState)
            (base := base)
              (words := words)
              (rest := restStack)
              hCompile hRun hReady hShared hRel with
          ⟨hPlanState, hBlockRun, hReadyFinal, hSharedFinal, hRelFinal⟩
        refine ⟨{ evmState with stack := base :: restStack }, ?_, rfl,
          hReadyFinal, hSharedFinal, ?_⟩
        · simpa using hBlockRun
        · rw [hPlanState]
          intro name slot hLookup
          exact hRelFinal hLookup
  | cons stmt tail ih =>
      unfold compileStmtList? at hCompile
      cases hHead : compileStmt? ctx returns compileState stmt with
      | none =>
          simp [hHead] at hCompile
      | some head =>
          cases hTail :
              compileStmtList? ctx returns head.state tail with
          | none =>
              simp [hHead, hTail] at hCompile
          | some tailPlan =>
              simp [hHead, hTail] at hCompile
              cases hCompile
              rcases hSafe with ⟨hHeadSafe, hTailSafe⟩
              have hHeadBound : StateSlotsBounded head.state :=
                compileStmt?_stateSlotsBounded
                  (plan := head) hStateBound hHead
              have hHeadNodup : StateSlotsNodup head.state :=
                compileStmt?_stateSlotsNodup
                  (plan := head) hStateBound hStateNodup hHead
              have hHeadMono :
                  compileState.nextSlot ≤ head.state.nextSlot :=
                compileStmt?_nextSlot_mono (plan := head) hHead
              have hTailMono :
                  head.state.nextSlot ≤ tailPlan.state.nextSlot :=
                compileStmtList?_nextSlot_mono
                  (stmts := tail) (plan := tailPlan) hTail
              have hStateFrameWords : compileState.nextSlot ≤ words :=
                Nat.le_trans hHeadMono
                  (Nat.le_trans hTailMono hFrameWords)
              have hHeadFrameWords : head.state.nextSlot ≤ words :=
                Nat.le_trans hTailMono hFrameWords
              cases sourceFuel with
              | zero =>
                  simp [EvmCompiler.Functions.Source.Block.runOpen,
                    EvmCompiler.Functions.Source.invalid,
                    Structured.invalid] at hRun
              | succ sourceFuel' =>
                  cases hStmtRun :
                      EvmCompiler.Functions.Source.Stmt.run
                          Locals.Source.PrimitiveSemantics.structured
                          sourceProgram sourceCtx sourceFuel' stmt source with
                  | error err =>
                      simp [EvmCompiler.Functions.Source.Block.runOpen,
                        hStmtRun] at hRun
                  | ok stmtResult =>
                      rcases stmtResult with ⟨stmtOutcome, headCtx⟩
                      cases stmtOutcome with
                      | mk sourceAfterHead mode =>
                          cases mode with
                          | regular =>
                              have hStmtRunRegular :
                                  EvmCompiler.Functions.Source.Stmt.run
                                      Locals.Source.PrimitiveSemantics.structured
                                      sourceProgram sourceCtx sourceFuel'
                                      stmt source =
                                    .ok
                                      (EvmCompiler.Functions.Source.Outcome.regular
                                        sourceAfterHead, headCtx) := by
                                simpa [EvmCompiler.Functions.Source.Outcome.regular]
                                  using hStmtRun
                              have hTailRun :
                                  EvmCompiler.Functions.Source.Block.runOpen
                                      Locals.Source.PrimitiveSemantics.structured
                                      sourceProgram headCtx sourceFuel'
                                      { stmts := tail } sourceAfterHead =
                                    .ok
                                      (EvmCompiler.Functions.Source.Outcome.regular
                                        source', sourceCtx') := by
                                  simpa [EvmCompiler.Functions.Source.Block.runOpen,
                                    hStmtRun,
                                    EvmCompiler.Functions.Source.Outcome.regular]
                                    using hRun
                              have hConsFuel :
                                  blockFuel + 2 * (stmt :: tail).length + 1 =
                                    (blockFuel + 2 * tail.length + 1) + 2 := by
                                simp
                                omega
                              cases stmt with
                              | expr expr =>
                                  rcases
                                      run_compileStmt?_expr_frameStore_of_source_run_regular
                                        (program := sourceProgram)
                                        (sourceCtx := sourceCtx)
                                        (sourceCtx' := headCtx)
                                        (fuel := sourceFuel')
                                        (evmState := evmState)
                                        (base := base)
                                        (words := words)
                                        (rest := restStack)
                                        hHead hHeadSafe hStmtRunRegular
                                        hStateBound hStateFrameWords hReady
                                        hShared hRel with
                                    ⟨headFinal, headCode, hHeadState,
                                      hHeadBlock, hHeadCodeRun, hHeadStack,
                                      hHeadReady, hHeadShared, hHeadRel⟩
                                  have hHeadRel' :
                                      FrameStoreRel head.state.env
                                        sourceAfterHead.vars
                                        headFinal.toMachineState base := by
                                    rw [hHeadState]
                                    intro name slot hLookup
                                    exact hHeadRel hLookup
                                  rcases
                                      ih
                                        (compileState := head.state)
                                        (plan := tailPlan)
                                        (source := sourceAfterHead)
                                        (sourceCtx := headCtx)
                                        (sourceFuel := sourceFuel')
                                        (evmState := headFinal)
                                        (blockFuel := blockFuel + 1)
                                        hTail hTailSafe hTailRun hHeadBound
                                          hHeadNodup hFrameWords hHeadReady
                                          hHeadShared hHeadRel' with
                                    ⟨final, hTailBlockRun, hFinalStack,
                                      hReadyFinal, hSharedFinal, hRelFinal⟩
                                  refine
                                    ⟨final, ?_, hFinalStack, hReadyFinal,
                                      hSharedFinal, hRelFinal⟩
                                  rw [hHeadBlock]
                                  rw [hConsFuel]
                                  change
                                    Expressions.Block.run compiledProgram
                                        ((blockFuel + 2 * tail.length + 1) + 2)
                                        (Block.append (Block.ofCode headCode)
                                          tailPlan.block)
                                        { runState with
                                          evm :=
                                            { evmState with
                                              stack := base :: restStack } } =
                                      .ok
                                        (Expressions.Outcome.regular
                                          ({ runState with evm := final }))
                                  have hStartTail :
                                      ({ runState with evm := headFinal } :
                                        Expressions.RunState) =
                                      ({ runState with
                                        evm :=
                                          { headFinal with
                                            stack := base :: restStack } } :
                                        Expressions.RunState) := by
                                    cases headFinal
                                    simp at hHeadStack ⊢
                                    exact hHeadStack
                                  have hTailRun' :
                                      Expressions.Block.run compiledProgram
                                          ((blockFuel + 1) +
                                            2 * tail.length + 1)
                                          tailPlan.block
                                          ({ runState with evm := headFinal } :
                                            Expressions.RunState) =
                                        .ok
                                          (Expressions.Outcome.regular
                                            ({ runState with evm := final })) := by
                                    simpa [hStartTail] using hTailBlockRun
                                  rw [
                                    run_blockAppend_ofCode_regular_of_code_run
                                      (program := compiledProgram)
                                      (fuel := blockFuel + 2 * tail.length + 1)
                                      (tail := tailPlan.block)
                                      (state :=
                                        { runState with
                                          evm :=
                                            { evmState with
                                              stack := base :: restStack } })
                                      hHeadCodeRun]
                                  simpa [Nat.mul_add, Nat.add_assoc,
                                    Nat.add_comm, Nat.add_left_comm]
                                    using hTailRun'
                              | let_ name value =>
                                  rcases
                                      run_compileStmt?_let_frameStore_of_source_run_regular
                                        hSpec hWordBytes
                                        (program := sourceProgram)
                                        (sourceCtx := sourceCtx)
                                        (sourceCtx' := headCtx)
                                        (fuel := sourceFuel')
                                        (evmState := evmState)
                                        (base := base)
                                        (words := words)
                                        (rest := restStack)
                                        hHead hHeadSafe hStmtRunRegular
                                        hStateBound hHeadFrameWords hReady
                                        hShared hRel with
                                    ⟨headFinal, headCode, hHeadBlock,
                                      hHeadCodeRun, hHeadStack, hHeadReady,
                                      hHeadShared, hHeadRel⟩
                                  rcases
                                      ih
                                        (compileState := head.state)
                                        (plan := tailPlan)
                                        (source := sourceAfterHead)
                                        (sourceCtx := headCtx)
                                        (sourceFuel := sourceFuel')
                                        (evmState := headFinal)
                                        (blockFuel := blockFuel + 1)
                                        hTail hTailSafe hTailRun hHeadBound
                                          hHeadNodup hFrameWords hHeadReady
                                          hHeadShared hHeadRel with
                                    ⟨final, hTailBlockRun, hFinalStack,
                                      hReadyFinal, hSharedFinal, hRelFinal⟩
                                  refine
                                    ⟨final, ?_, hFinalStack, hReadyFinal,
                                      hSharedFinal, hRelFinal⟩
                                  rw [hHeadBlock]
                                  rw [hConsFuel]
                                  change
                                    Expressions.Block.run compiledProgram
                                        ((blockFuel + 2 * tail.length + 1) + 2)
                                        (Block.append (Block.ofCode headCode)
                                          tailPlan.block)
                                        { runState with
                                          evm :=
                                            { evmState with
                                              stack := base :: restStack } } =
                                      .ok
                                        (Expressions.Outcome.regular
                                          ({ runState with evm := final }))
                                  have hStartTail :
                                      ({ runState with evm := headFinal } :
                                        Expressions.RunState) =
                                      ({ runState with
                                        evm :=
                                          { headFinal with
                                            stack := base :: restStack } } :
                                        Expressions.RunState) := by
                                    cases headFinal
                                    simp at hHeadStack ⊢
                                    exact hHeadStack
                                  have hTailRun' :
                                      Expressions.Block.run compiledProgram
                                          ((blockFuel + 1) +
                                            2 * tail.length + 1)
                                          tailPlan.block
                                          ({ runState with evm := headFinal } :
                                            Expressions.RunState) =
                                        .ok
                                          (Expressions.Outcome.regular
                                            ({ runState with evm := final })) := by
                                    simpa [hStartTail] using hTailBlockRun
                                  rw [
                                    run_blockAppend_ofCode_regular_of_code_run
                                      (program := compiledProgram)
                                      (fuel := blockFuel + 2 * tail.length + 1)
                                      (tail := tailPlan.block)
                                      (state :=
                                        { runState with
                                          evm :=
                                            { evmState with
                                              stack := base :: restStack } })
                                      hHeadCodeRun]
                                  simpa [Nat.mul_add, Nat.add_assoc,
                                    Nat.add_comm, Nat.add_left_comm]
                                    using hTailRun'
                              | assign name value =>
                                  rcases
                                      run_compileStmt?_assign_frameStore_of_source_run_regular
                                        hSpec hWordBytes
                                        (program := sourceProgram)
                                        (sourceCtx := sourceCtx)
                                        (sourceCtx' := headCtx)
                                        (fuel := sourceFuel')
                                        (evmState := evmState)
                                        (base := base)
                                        (words := words)
                                        (rest := restStack)
                                        hHead hHeadSafe hStmtRunRegular
                                        hStateBound hStateNodup
                                        hStateFrameWords hReady hShared
                                        hRel with
                                    ⟨headFinal, headCode, hHeadBlock,
                                      hHeadCodeRun, hHeadStack, hHeadReady,
                                      hHeadShared, hHeadRel⟩
                                  rcases
                                      compileStmt?_assign_target_slot_bounded
                                        hStateBound hHead with
                                    ⟨_slot, _valueCode, _storeCode, _hLookup,
                                      _hSlot, _hValueCode, _hStoreCode,
                                      hHeadState, _hHeadBlockShape⟩
                                  have hHeadRel' :
                                      FrameStoreRel head.state.env
                                        sourceAfterHead.vars
                                        headFinal.toMachineState base := by
                                    rw [hHeadState]
                                    intro name slot hLookup
                                    exact hHeadRel hLookup
                                  rcases
                                      ih
                                        (compileState := head.state)
                                        (plan := tailPlan)
                                        (source := sourceAfterHead)
                                        (sourceCtx := headCtx)
                                        (sourceFuel := sourceFuel')
                                        (evmState := headFinal)
                                        (blockFuel := blockFuel + 1)
                                        hTail hTailSafe hTailRun hHeadBound
                                          hHeadNodup hFrameWords hHeadReady
                                          hHeadShared hHeadRel' with
                                    ⟨final, hTailBlockRun, hFinalStack,
                                      hReadyFinal, hSharedFinal, hRelFinal⟩
                                  refine
                                    ⟨final, ?_, hFinalStack, hReadyFinal,
                                      hSharedFinal, hRelFinal⟩
                                  rw [hHeadBlock]
                                  rw [hConsFuel]
                                  change
                                    Expressions.Block.run compiledProgram
                                        ((blockFuel + 2 * tail.length + 1) + 2)
                                        (Block.append (Block.ofCode headCode)
                                          tailPlan.block)
                                        { runState with
                                          evm :=
                                            { evmState with
                                              stack := base :: restStack } } =
                                      .ok
                                        (Expressions.Outcome.regular
                                          ({ runState with evm := final }))
                                  have hStartTail :
                                      ({ runState with evm := headFinal } :
                                        Expressions.RunState) =
                                      ({ runState with
                                        evm :=
                                          { headFinal with
                                            stack := base :: restStack } } :
                                        Expressions.RunState) := by
                                    cases headFinal
                                    simp at hHeadStack ⊢
                                    exact hHeadStack
                                  have hTailRun' :
                                      Expressions.Block.run compiledProgram
                                          ((blockFuel + 1) +
                                            2 * tail.length + 1)
                                          tailPlan.block
                                          ({ runState with evm := headFinal } :
                                            Expressions.RunState) =
                                        .ok
                                          (Expressions.Outcome.regular
                                            ({ runState with evm := final })) := by
                                    simpa [hStartTail] using hTailBlockRun
                                  rw [
                                    run_blockAppend_ofCode_regular_of_code_run
                                      (program := compiledProgram)
                                      (fuel := blockFuel + 2 * tail.length + 1)
                                      (tail := tailPlan.block)
                                      (state :=
                                        { runState with
                                          evm :=
                                            { evmState with
                                              stack := base :: restStack } })
                                      hHeadCodeRun]
                                  simpa [Nat.mul_add, Nat.add_assoc,
                                    Nat.add_comm, Nat.add_left_comm]
                                    using hTailRun'
                              | block body =>
                                  simp [AtomicStmtSafe] at hHeadSafe
                              | if_ cond body =>
                                  simp [AtomicStmtSafe] at hHeadSafe
                              | switch scrutinee cases defaultBody =>
                                  simp [AtomicStmtSafe] at hHeadSafe
                              | for_ init cond post body =>
                                  simp [AtomicStmtSafe] at hHeadSafe
                              | brk =>
                                  simp [AtomicStmtSafe] at hHeadSafe
                              | cont =>
                                  simp [AtomicStmtSafe] at hHeadSafe
                              | leave =>
                                  simp [AtomicStmtSafe] at hHeadSafe
                              | call targets functionName args =>
                                  simp [AtomicStmtSafe] at hHeadSafe
                              | terminal kind =>
                                  simp [AtomicStmtSafe] at hHeadSafe
                              | terminalArgs kind args =>
                                  simp [AtomicStmtSafe] at hHeadSafe
                            | brk =>
                                simp [EvmCompiler.Functions.Source.Block.runOpen,
                                  hStmtRun,
                                  EvmCompiler.Functions.Source.Outcome.regular]
                                  at hRun
                                rcases hRun with ⟨hOutcome, _hCtx⟩
                                cases hOutcome
                            | cont =>
                                simp [EvmCompiler.Functions.Source.Block.runOpen,
                                  hStmtRun,
                                  EvmCompiler.Functions.Source.Outcome.regular]
                                  at hRun
                                rcases hRun with ⟨hOutcome, _hCtx⟩
                                cases hOutcome
                            | leave =>
                                simp [EvmCompiler.Functions.Source.Block.runOpen,
                                  hStmtRun,
                                  EvmCompiler.Functions.Source.Outcome.regular]
                                  at hRun
                                rcases hRun with ⟨hOutcome, _hCtx⟩
                                cases hOutcome
                            | halt kind =>
                                simp [EvmCompiler.Functions.Source.Block.runOpen,
                                  hStmtRun,
                                  EvmCompiler.Functions.Source.Outcome.regular]
                                  at hRun
                                rcases hRun with ⟨hOutcome, _hCtx⟩
                                cases hOutcome

theorem run_frameInitCode_append_compileStmtList?_atomic_block_frameStore_of_source_run_open_regular
    (hSpec : ZeroPaddingSpec)
    (hWordBytes : WordByteEncodingSpec)
    {ctx : CompileCtx} {returns : List Name}
    {compileState : CompileState} {stmts : List Stmt} {plan : Plan}
    {sourceProgram : Program} {compiledProgram : Expressions.Program}
    {source source' : Locals.Source.State}
    {sourceCtx sourceCtx' : EvmCompiler.Functions.Source.Ctx}
    {sourceFuel blockFuel : Nat}
    {runState : Expressions.RunState}
    {evmState initState : EVMState} {base : Word} {words : Nat}
    (hCompile :
      compileStmtList? ctx returns compileState stmts = some plan)
    (hSafe : AtomicStmtListSafe stmts)
    (hRun :
      EvmCompiler.Functions.Source.Block.runOpen
          Locals.Source.PrimitiveSemantics.structured
          sourceProgram sourceCtx sourceFuel { stmts := stmts } source =
        .ok (EvmCompiler.Functions.Source.Outcome.regular source',
          sourceCtx'))
    (hStateBound : StateSlotsBounded compileState)
    (hStateNodup : StateSlotsNodup compileState)
    (hFrameWords : plan.state.nextSlot ≤ words)
    (hInitRun :
      Structured.Code.run (frameInitCode words) evmState = .ok initState)
    (hInitStack : initState.stack = base :: evmState.stack)
    (hReady : ScratchRegionReady initState.toMachineState
      (range base words).base (range base words).words)
    (hShared : SharedStateEqOutsideScratch (range base words) source.shared
      initState.toSharedState)
    (hRel : FrameStoreRel compileState.env source.vars
      initState.toMachineState base) :
    ∃ final,
      Expressions.Block.run compiledProgram
          (blockFuel + 2 * stmts.length + 2)
          (Block.append (Block.ofCode (frameInitCode words)) plan.block)
          { runState with evm := evmState } =
        .ok (Expressions.Outcome.regular ({ runState with evm := final })) ∧
      final.stack = base :: evmState.stack ∧
      ScratchRegionReady final.toMachineState
        (range base words).base (range base words).words ∧
      SharedStateEqOutsideScratch (range base words) source'.shared
        final.toSharedState ∧
      FrameStoreRel plan.state.env source'.vars final.toMachineState base := by
  rcases
      run_compileStmtList?_atomic_block_frameStore_of_source_run_open_regular
        hSpec hWordBytes
        (compiledProgram := compiledProgram)
        (runState := runState)
        (evmState := initState)
        (base := base)
        (words := words)
        (restStack := evmState.stack)
        hCompile hSafe hRun hStateBound hStateNodup hFrameWords hReady
        hShared hRel with
    ⟨final, hBodyRun, hFinalStack, hReadyFinal, hSharedFinal,
      hRelFinal⟩
  refine
    ⟨final, ?_, hFinalStack, hReadyFinal, hSharedFinal, hRelFinal⟩
  have hFuel :
      blockFuel + 2 * stmts.length + 2 =
        (blockFuel + 2 * stmts.length) + 2 := by
    omega
  rw [hFuel]
  rw [
    run_blockAppend_ofCode_regular_of_code_run
      (program := compiledProgram)
      (fuel := blockFuel + 2 * stmts.length)
      (tail := plan.block)
      (state := { runState with evm := evmState })
      hInitRun]
  have hStartTail :
      (({ runState with evm := evmState } : Expressions.RunState).withEVM
          initState) =
        ({ runState with
          evm := { initState with stack := base :: evmState.stack } } :
          Expressions.RunState) := by
    cases initState
    simp [Structured.RunState.withEVM] at hInitStack ⊢
    exact hInitStack
  have hBodyRun' :
      Expressions.Block.run compiledProgram
          (blockFuel + 2 * stmts.length + 1) plan.block
          (({ runState with evm := evmState } :
            Expressions.RunState).withEVM initState) =
        .ok (Expressions.Outcome.regular ({ runState with evm := final })) := by
    simpa [hStartTail] using hBodyRun
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hBodyRun'

theorem run_compileMain?_atomic_noPrelude_block_frameStore_of_source_run_open_regular
    (hSpec : ZeroPaddingSpec)
    (hWordBytes : WordByteEncodingSpec)
    {ctx : CompileCtx}
    {compileState : CompileState} {stmts : List Stmt} {mainPlan : Plan}
    {sourceProgram : Program} {compiledProgram : Expressions.Program}
    {source source' : Locals.Source.State}
    {sourceCtx sourceCtx' : EvmCompiler.Functions.Source.Ctx}
    {sourceFuel blockFuel : Nat}
    {runState : Expressions.RunState}
    {evmState initState : EVMState} {base : Word} {words : Nat}
    (hSplit : splitPrelude stmts = ([], stmts))
    (hCompile :
      compileMain? ctx words compileState { stmts := stmts } = some mainPlan)
    (hSafe : AtomicStmtListSafe stmts)
    (hRun :
      EvmCompiler.Functions.Source.Block.runOpen
          Locals.Source.PrimitiveSemantics.structured
          sourceProgram sourceCtx sourceFuel { stmts := stmts } source =
        .ok (EvmCompiler.Functions.Source.Outcome.regular source',
          sourceCtx'))
    (hStateBound : StateSlotsBounded compileState)
    (hStateNodup : StateSlotsNodup compileState)
    (hFrameWords : mainPlan.state.nextSlot ≤ words)
    (hInitRun :
      Structured.Code.run (frameInitCode words) evmState = .ok initState)
    (hInitStack : initState.stack = base :: evmState.stack)
    (hReady : ScratchRegionReady initState.toMachineState
      (range base words).base (range base words).words)
    (hShared : SharedStateEqOutsideScratch (range base words) source.shared
      initState.toSharedState)
    (hRel : FrameStoreRel compileState.env source.vars
      initState.toMachineState base) :
    ∃ final,
      Expressions.Block.run compiledProgram
          (blockFuel + 2 * stmts.length + 2) mainPlan.block
          { runState with evm := evmState } =
        .ok (Expressions.Outcome.regular ({ runState with evm := final })) ∧
      final.stack = base :: evmState.stack ∧
      ScratchRegionReady final.toMachineState
        (range base words).base (range base words).words ∧
      SharedStateEqOutsideScratch (range base words) source'.shared
        final.toSharedState ∧
      FrameStoreRel mainPlan.state.env source'.vars final.toMachineState
        base := by
  unfold compileMain? at hCompile
  simp [hSplit] at hCompile
  cases hPlan : compileStmtList? ctx [] compileState stmts with
  | none =>
      simp [hPlan] at hCompile
  | some plan =>
      simp [hPlan] at hCompile
      cases hCompile
      rcases
          run_frameInitCode_append_compileStmtList?_atomic_block_frameStore_of_source_run_open_regular
            hSpec hWordBytes
            (compiledProgram := compiledProgram)
            (sourceFuel := sourceFuel)
            (blockFuel := blockFuel)
            (runState := runState)
            (evmState := evmState)
            (initState := initState)
            (base := base)
            (words := words)
            hPlan hSafe hRun hStateBound hStateNodup hFrameWords
            hInitRun hInitStack hReady hShared hRel with
        ⟨final, hBlockRun, hStack, hReadyFinal, hSharedFinal, hRelFinal⟩
      refine
        ⟨final, ?_, hStack, hReadyFinal, hSharedFinal, hRelFinal⟩
      simpa [Block.append, Block.ofCode] using hBlockRun

theorem run_compileMain?_atomic_withPrelude_block_frameStore_of_source_run_open_regular
    (hSpec : ZeroPaddingSpec)
    (hWordBytes : WordByteEncodingSpec)
    {ctx : CompileCtx}
    {compileState : CompileState} {stmts rest : List Stmt}
    {prelude : List Expressions.Stmt} {mainPlan : Plan}
    {sourceProgram : Program} {compiledProgram : Expressions.Program}
    {source source' : Locals.Source.State}
    {sourceCtx sourceCtx' : EvmCompiler.Functions.Source.Ctx}
    {sourceFuel blockFuel : Nat}
    {runState : Expressions.RunState}
    {evmState preludeEvm initState : EVMState} {base : Word}
    {words : Nat}
    (hSplit : splitPrelude stmts = (prelude, rest))
    (hCompile :
      compileMain? ctx words compileState { stmts := stmts } =
        some mainPlan)
    (hPreludeRun :
      Expressions.Block.run compiledProgram
          ((blockFuel + 2 * rest.length + 2) + prelude.length)
          { stmts := prelude } { runState with evm := evmState } =
        .ok (Expressions.Outcome.regular
          ({ runState with evm := preludeEvm })))
    (hSafe : AtomicStmtListSafe rest)
    (hRun :
      EvmCompiler.Functions.Source.Block.runOpen
          Locals.Source.PrimitiveSemantics.structured
          sourceProgram sourceCtx sourceFuel { stmts := rest } source =
        .ok (EvmCompiler.Functions.Source.Outcome.regular source',
          sourceCtx'))
    (hStateBound : StateSlotsBounded compileState)
    (hStateNodup : StateSlotsNodup compileState)
    (hFrameWords : mainPlan.state.nextSlot ≤ words)
    (hInitRun :
      Structured.Code.run (frameInitCode words) preludeEvm = .ok initState)
    (hInitStack : initState.stack = base :: preludeEvm.stack)
    (hReady : ScratchRegionReady initState.toMachineState
      (range base words).base (range base words).words)
    (hShared : SharedStateEqOutsideScratch (range base words) source.shared
      initState.toSharedState)
    (hRel : FrameStoreRel compileState.env source.vars
      initState.toMachineState base) :
    ∃ final,
      Expressions.Block.run compiledProgram
          ((blockFuel + 2 * rest.length + 2) + prelude.length)
          mainPlan.block { runState with evm := evmState } =
        .ok (Expressions.Outcome.regular ({ runState with evm := final })) ∧
      final.stack = base :: preludeEvm.stack ∧
      ScratchRegionReady final.toMachineState
        (range base words).base (range base words).words ∧
      SharedStateEqOutsideScratch (range base words) source'.shared
        final.toSharedState ∧
      FrameStoreRel mainPlan.state.env source'.vars final.toMachineState
        base := by
  unfold compileMain? at hCompile
  simp [hSplit] at hCompile
  cases hPlan : compileStmtList? ctx [] compileState rest with
  | none =>
      simp [hPlan] at hCompile
  | some plan =>
      simp [hPlan] at hCompile
      cases hCompile
      rcases
          run_frameInitCode_append_compileStmtList?_atomic_block_frameStore_of_source_run_open_regular
            hSpec hWordBytes
            (compiledProgram := compiledProgram)
            (sourceFuel := sourceFuel)
            (blockFuel := blockFuel)
            (runState := runState)
            (evmState := preludeEvm)
            (initState := initState)
            (base := base)
            (words := words)
            hPlan hSafe hRun hStateBound hStateNodup hFrameWords
            hInitRun hInitStack hReady hShared hRel with
        ⟨final, hTailRun, hStack, hReadyFinal, hSharedFinal, hRelFinal⟩
      refine
        ⟨final, ?_, hStack, hReadyFinal, hSharedFinal, hRelFinal⟩
      have hAppend :=
        run_block_append_regular_of_prefix_run
          (program := compiledProgram)
          (fuel := blockFuel + 2 * rest.length + 2)
          (pref := prelude)
          (suffix :=
            (Expressions.Stmt.code (frameInitCode words)) ::
              plan.block.stmts)
          (state := { runState with evm := evmState })
          (mid := { runState with evm := preludeEvm })
          hPreludeRun
      rw [hAppend]
      simpa [Block.append, Block.ofCode] using hTailRun

theorem run_compileMain?_atomic_withPrelude_block_frameStore_of_full_source_run_open_regular
    (hSpec : ZeroPaddingSpec)
    (hWordBytes : WordByteEncodingSpec)
    {ctx : CompileCtx}
    {compileState : CompileState} {stmts rest : List Stmt}
    {prelude : List Expressions.Stmt} {mainPlan : Plan}
    {sourceProgram : Program} {compiledProgram : Expressions.Program}
    {source source' : Locals.Source.State}
    {sourceCtx sourceCtx' : EvmCompiler.Functions.Source.Ctx}
    {sourceFuel blockFuel : Nat}
    {runState : Expressions.RunState}
    {evmState : EVMState} {words : Nat}
    (hSplit : splitPrelude stmts = (prelude, rest))
    (hCompile :
      compileMain? ctx words compileState { stmts := stmts } =
        some mainPlan)
    (hSafe : AtomicStmtListSafe stmts)
    (hRun :
      EvmCompiler.Functions.Source.Block.runOpen
          Locals.Source.PrimitiveSemantics.structured
          sourceProgram sourceCtx sourceFuel { stmts := stmts } source =
        .ok (EvmCompiler.Functions.Source.Outcome.regular source',
          sourceCtx'))
    (hStateBound : StateSlotsBounded compileState)
    (hStateNodup : StateSlotsNodup compileState)
    (hFrameWords : mainPlan.state.nextSlot ≤ words)
    (hSharedStart : evmState.toSharedState = source.shared) :
    ∃ sourceAfterPrelude sourceCtxAfterPrelude preludeEvm restFuel,
      preludeEvm.toSharedState = sourceAfterPrelude.shared ∧
      preludeEvm.stack = evmState.stack ∧
      EvmCompiler.Functions.Source.Block.runOpen
          Locals.Source.PrimitiveSemantics.structured
          sourceProgram sourceCtxAfterPrelude restFuel
          { stmts := rest } sourceAfterPrelude =
        .ok (EvmCompiler.Functions.Source.Outcome.regular source',
          sourceCtx') ∧
      ∀ {initState : EVMState} {base : Word},
        Structured.Code.run (frameInitCode words) preludeEvm =
          .ok initState →
        initState.stack = base :: preludeEvm.stack →
        ScratchRegionReady initState.toMachineState
          (range base words).base (range base words).words →
        SharedStateEqOutsideScratch (range base words)
          sourceAfterPrelude.shared initState.toSharedState →
        FrameStoreRel compileState.env sourceAfterPrelude.vars
          initState.toMachineState base →
          ∃ final,
            Expressions.Block.run compiledProgram
                ((blockFuel + 2 * rest.length + 2) + prelude.length)
                mainPlan.block { runState with evm := evmState } =
              .ok (Expressions.Outcome.regular
                ({ runState with evm := final })) ∧
            final.stack = base :: evmState.stack ∧
            ScratchRegionReady final.toMachineState
              (range base words).base (range base words).words ∧
            SharedStateEqOutsideScratch (range base words) source'.shared
              final.toSharedState ∧
            FrameStoreRel mainPlan.state.env source'.vars
              final.toMachineState base := by
  have hRestSafe :
      AtomicStmtListSafe rest :=
    splitPrelude_atomic_stmt_list_safe_rest hSafe hSplit
  rcases
      run_splitPrelude_atomic_source_safe_prelude_block_of_source_run_open_regular
        (stmts := stmts) (prelude := prelude) (restSourceStmts := rest)
        (sourceProgram := sourceProgram) (compiledProgram := compiledProgram)
        (source := source) (finalSource := source')
        (sourceCtx := sourceCtx) (finalCtx := sourceCtx')
        (sourceFuel := sourceFuel)
        (targetFuel := blockFuel + 2 * rest.length + 1)
        (runState := runState) (evm := evmState)
        hSafe hSplit hSharedStart hRun with
    ⟨sourceAfterPrelude, sourceCtxAfterPrelude, preludeEvm, restFuel,
      hPreludeRun, hPreludeShared, hPreludeStack, hRestRun⟩
  have hPreludeRun' :
      Expressions.Block.run compiledProgram
          ((blockFuel + 2 * rest.length + 2) + prelude.length)
          { stmts := prelude } { runState with evm := evmState } =
        .ok (Expressions.Outcome.regular
          ({ runState with evm := preludeEvm })) := by
    have hFuel :
        (blockFuel + 2 * rest.length + 1) + prelude.length + 1 =
          (blockFuel + 2 * rest.length + 2) + prelude.length := by
      omega
    rw [← hFuel]
    exact hPreludeRun
  refine
    ⟨sourceAfterPrelude, sourceCtxAfterPrelude, preludeEvm, restFuel,
      hPreludeShared, hPreludeStack, hRestRun, ?_⟩
  intro initState base hInitRun hInitStack hReady hShared hRel
  rcases
      run_compileMain?_atomic_withPrelude_block_frameStore_of_source_run_open_regular
        hSpec hWordBytes
        (ctx := ctx)
        (compileState := compileState)
        (stmts := stmts)
        (rest := rest)
        (prelude := prelude)
        (mainPlan := mainPlan)
        (sourceProgram := sourceProgram)
        (compiledProgram := compiledProgram)
        (source := sourceAfterPrelude)
        (source' := source')
        (sourceCtx := sourceCtxAfterPrelude)
        (sourceCtx' := sourceCtx')
        (sourceFuel := restFuel)
        (blockFuel := blockFuel)
        (runState := runState)
        (evmState := evmState)
        (preludeEvm := preludeEvm)
        (initState := initState)
        (base := base)
        (words := words)
        hSplit hCompile hPreludeRun' hRestSafe hRestRun
        hStateBound hStateNodup hFrameWords hInitRun hInitStack hReady
        hShared hRel with
    ⟨final, hMainRun, hStack, hReadyFinal, hSharedFinal, hRelFinal⟩
  refine ⟨final, hMainRun, ?_, hReadyFinal, hSharedFinal, hRelFinal⟩
  simpa [hPreludeStack] using hStack

theorem run_compileMain?_atomic_noPrelude_empty_frame_of_frameInit_ready_succ
    (hSpec : ZeroPaddingSpec)
    (hWordBytes : WordByteEncodingSpec)
    {ctx : CompileCtx}
    {startSlot slot : Nat} {stmts : List Stmt} {mainPlan : Plan}
    {sourceProgram : Program} {compiledProgram : Expressions.Program}
    {source source' : Locals.Source.State}
    {sourceCtx sourceCtx' : EvmCompiler.Functions.Source.Ctx}
    {sourceFuel blockFuel : Nat}
    {runState : Expressions.RunState}
    {evmState : EVMState}
    (hSplit : splitPrelude stmts = ([], stmts))
    (hCompile :
      compileMain? ctx (slot + 1)
          ({ env := [], nextSlot := startSlot } : CompileState)
          { stmts := stmts } =
        some mainPlan)
    (hSafe : AtomicStmtListSafe stmts)
    (hRun :
      EvmCompiler.Functions.Source.Block.runOpen
          Locals.Source.PrimitiveSemantics.structured
          sourceProgram sourceCtx sourceFuel { stmts := stmts } source =
        .ok (EvmCompiler.Functions.Source.Outcome.regular source',
          sourceCtx'))
    (hFrameWords : mainPlan.state.nextSlot ≤ slot + 1)
    (hOffsetLtUInt :
      (evmState.toMachineState.mload freePtrWord).1.toNat + 32 * slot <
        EvmYul.UInt256.size)
    (hPadNoOverflow :
      (evmState.toMachineState.mload freePtrWord).1.toNat + 32 * slot -
          (frameBumpMachine (slot + 1) evmState.toMachineState).memory.size <
        USize.size)
    (hWithinAfter :
      (evmState.toMachineState.mload freePtrWord).1.toNat +
          32 * (slot + 1) ≤
        EvmYul.MachineState.M
          (frameBumpMachine (slot + 1)
            evmState.toMachineState).activeWords.toNat
          ((evmState.toMachineState.mload freePtrWord).1.toNat +
            32 * slot) 32 * 32)
    (hActiveAfter :
      EvmYul.MachineState.M
          (frameBumpMachine (slot + 1)
            evmState.toMachineState).activeWords.toNat
          ((evmState.toMachineState.mload freePtrWord).1.toNat +
            32 * slot) 32 * 32 <
        EvmYul.UInt256.size)
    (hSharedInit :
      ∀ initState,
        Structured.Code.run (frameInitCode (slot + 1)) evmState =
            .ok initState →
          SharedStateEqOutsideScratch
            (range (evmState.toMachineState.mload freePtrWord).1
              (slot + 1)) source.shared initState.toSharedState) :
    ∃ final,
      Expressions.Block.run compiledProgram
          (blockFuel + 2 * stmts.length + 2) mainPlan.block
          { runState with evm := evmState } =
        .ok (Expressions.Outcome.regular ({ runState with evm := final })) ∧
      final.stack =
        (evmState.toMachineState.mload freePtrWord).1 :: evmState.stack ∧
      ScratchRegionReady final.toMachineState
        (range (evmState.toMachineState.mload freePtrWord).1
          (slot + 1)).base
        (range (evmState.toMachineState.mload freePtrWord).1
          (slot + 1)).words ∧
      SharedStateEqOutsideScratch
        (range (evmState.toMachineState.mload freePtrWord).1
          (slot + 1)) source'.shared final.toSharedState ∧
      FrameStoreRel mainPlan.state.env source'.vars final.toMachineState
        (evmState.toMachineState.mload freePtrWord).1 := by
  rcases
      run_frameInitCode_ready_succ hSpec hWordBytes evmState slot
        hOffsetLtUInt hPadNoOverflow hWithinAfter hActiveAfter with
    ⟨initState, hInitRun, hInitStack, _hInitMachine, hReady⟩
  exact
    run_compileMain?_atomic_noPrelude_block_frameStore_of_source_run_open_regular
      hSpec hWordBytes
      (ctx := ctx)
      (compileState := ({ env := [], nextSlot := startSlot } : CompileState))
      (stmts := stmts)
      (mainPlan := mainPlan)
      (sourceProgram := sourceProgram)
      (compiledProgram := compiledProgram)
      (sourceFuel := sourceFuel)
      (blockFuel := blockFuel)
      (runState := runState)
      (evmState := evmState)
      (initState := initState)
      (base := (evmState.toMachineState.mload freePtrWord).1)
      (words := slot + 1)
      hSplit hCompile hSafe hRun
      (StateSlotsBounded.empty startSlot)
      (StateSlotsNodup.empty startSlot)
      hFrameWords hInitRun hInitStack hReady
      (hSharedInit initState hInitRun)
      FrameStoreRel.empty

theorem run_compileMain?_atomic_withPrelude_empty_frame_of_frameInit_ready_succ
    (hSpec : ZeroPaddingSpec)
    (hWordBytes : WordByteEncodingSpec)
    {ctx : CompileCtx}
    {startSlot slot : Nat} {stmts rest : List Stmt}
    {prelude : List Expressions.Stmt} {mainPlan : Plan}
    {sourceProgram : Program} {compiledProgram : Expressions.Program}
    {source source' : Locals.Source.State}
    {sourceCtx sourceCtx' : EvmCompiler.Functions.Source.Ctx}
    {sourceFuel blockFuel : Nat}
    {runState : Expressions.RunState}
    {evmState preludeEvm : EVMState}
    (hSplit : splitPrelude stmts = (prelude, rest))
    (hCompile :
      compileMain? ctx (slot + 1)
          ({ env := [], nextSlot := startSlot } : CompileState)
          { stmts := stmts } =
        some mainPlan)
    (hPreludeRun :
      Expressions.Block.run compiledProgram
          ((blockFuel + 2 * rest.length + 2) + prelude.length)
          { stmts := prelude } { runState with evm := evmState } =
        .ok (Expressions.Outcome.regular
          ({ runState with evm := preludeEvm })))
    (hSafe : AtomicStmtListSafe rest)
    (hRun :
      EvmCompiler.Functions.Source.Block.runOpen
          Locals.Source.PrimitiveSemantics.structured
          sourceProgram sourceCtx sourceFuel { stmts := rest } source =
        .ok (EvmCompiler.Functions.Source.Outcome.regular source',
          sourceCtx'))
    (hFrameWords : mainPlan.state.nextSlot ≤ slot + 1)
    (hOffsetLtUInt :
      (preludeEvm.toMachineState.mload freePtrWord).1.toNat +
          32 * slot <
        EvmYul.UInt256.size)
    (hPadNoOverflow :
      (preludeEvm.toMachineState.mload freePtrWord).1.toNat +
          32 * slot -
          (frameBumpMachine (slot + 1)
            preludeEvm.toMachineState).memory.size <
        USize.size)
    (hWithinAfter :
      (preludeEvm.toMachineState.mload freePtrWord).1.toNat +
          32 * (slot + 1) ≤
        EvmYul.MachineState.M
          (frameBumpMachine (slot + 1)
            preludeEvm.toMachineState).activeWords.toNat
          ((preludeEvm.toMachineState.mload freePtrWord).1.toNat +
            32 * slot) 32 * 32)
    (hActiveAfter :
      EvmYul.MachineState.M
          (frameBumpMachine (slot + 1)
            preludeEvm.toMachineState).activeWords.toNat
          ((preludeEvm.toMachineState.mload freePtrWord).1.toNat +
            32 * slot) 32 * 32 <
        EvmYul.UInt256.size)
    (hSharedInit :
      ∀ initState,
        Structured.Code.run (frameInitCode (slot + 1)) preludeEvm =
            .ok initState →
          SharedStateEqOutsideScratch
            (range (preludeEvm.toMachineState.mload freePtrWord).1
              (slot + 1)) source.shared initState.toSharedState) :
    ∃ final,
      Expressions.Block.run compiledProgram
          ((blockFuel + 2 * rest.length + 2) + prelude.length)
          mainPlan.block { runState with evm := evmState } =
        .ok (Expressions.Outcome.regular ({ runState with evm := final })) ∧
      final.stack =
        (preludeEvm.toMachineState.mload freePtrWord).1 ::
          preludeEvm.stack ∧
      ScratchRegionReady final.toMachineState
        (range (preludeEvm.toMachineState.mload freePtrWord).1
          (slot + 1)).base
        (range (preludeEvm.toMachineState.mload freePtrWord).1
          (slot + 1)).words ∧
      SharedStateEqOutsideScratch
        (range (preludeEvm.toMachineState.mload freePtrWord).1
          (slot + 1)) source'.shared final.toSharedState ∧
      FrameStoreRel mainPlan.state.env source'.vars final.toMachineState
        (preludeEvm.toMachineState.mload freePtrWord).1 := by
  rcases
      run_frameInitCode_ready_succ hSpec hWordBytes preludeEvm slot
        hOffsetLtUInt hPadNoOverflow hWithinAfter hActiveAfter with
    ⟨initState, hInitRun, hInitStack, _hInitMachine, hReady⟩
  exact
    run_compileMain?_atomic_withPrelude_block_frameStore_of_source_run_open_regular
      hSpec hWordBytes
      (ctx := ctx)
      (compileState := ({ env := [], nextSlot := startSlot } : CompileState))
      (stmts := stmts)
      (rest := rest)
      (prelude := prelude)
      (mainPlan := mainPlan)
      (sourceProgram := sourceProgram)
      (compiledProgram := compiledProgram)
      (sourceFuel := sourceFuel)
      (blockFuel := blockFuel)
      (runState := runState)
      (evmState := evmState)
      (preludeEvm := preludeEvm)
      (initState := initState)
      (base := (preludeEvm.toMachineState.mload freePtrWord).1)
      (words := slot + 1)
      hSplit hCompile hPreludeRun hSafe hRun
      (StateSlotsBounded.empty startSlot)
      (StateSlotsNodup.empty startSlot)
      hFrameWords hInitRun hInitStack hReady
      (hSharedInit initState hInitRun)
      FrameStoreRel.empty

theorem run_compileMain?_atomic_withPrelude_empty_frame_of_full_source_run_frameInit_ready_succ
    (hSpec : ZeroPaddingSpec)
    (hWordBytes : WordByteEncodingSpec)
    {ctx : CompileCtx}
    {startSlot slot : Nat} {stmts rest : List Stmt}
    {prelude : List Expressions.Stmt} {mainPlan : Plan}
    {sourceProgram : Program} {compiledProgram : Expressions.Program}
    {source source' : Locals.Source.State}
    {sourceCtx sourceCtx' : EvmCompiler.Functions.Source.Ctx}
    {sourceFuel blockFuel : Nat}
    {runState : Expressions.RunState}
    {evmState : EVMState}
    (hSplit : splitPrelude stmts = (prelude, rest))
    (hCompile :
      compileMain? ctx (slot + 1)
          ({ env := [], nextSlot := startSlot } : CompileState)
          { stmts := stmts } =
        some mainPlan)
    (hSafe : AtomicStmtListSafe stmts)
    (hRun :
      EvmCompiler.Functions.Source.Block.runOpen
          Locals.Source.PrimitiveSemantics.structured
          sourceProgram sourceCtx sourceFuel { stmts := stmts } source =
        .ok (EvmCompiler.Functions.Source.Outcome.regular source',
          sourceCtx'))
    (hFrameWords : mainPlan.state.nextSlot ≤ slot + 1)
    (hSharedStart : evmState.toSharedState = source.shared) :
    ∃ sourceAfterPrelude sourceCtxAfterPrelude preludeEvm restFuel,
      preludeEvm.toSharedState = sourceAfterPrelude.shared ∧
      preludeEvm.stack = evmState.stack ∧
      EvmCompiler.Functions.Source.Block.runOpen
          Locals.Source.PrimitiveSemantics.structured
          sourceProgram sourceCtxAfterPrelude restFuel
          { stmts := rest } sourceAfterPrelude =
        .ok (EvmCompiler.Functions.Source.Outcome.regular source',
          sourceCtx') ∧
      (∀
          (_hOffsetLtUInt :
            (preludeEvm.toMachineState.mload freePtrWord).1.toNat +
                32 * slot <
              EvmYul.UInt256.size)
          (_hPadNoOverflow :
            (preludeEvm.toMachineState.mload freePtrWord).1.toNat +
                32 * slot -
                (frameBumpMachine (slot + 1)
                  preludeEvm.toMachineState).memory.size <
              USize.size)
          (_hWithinAfter :
            (preludeEvm.toMachineState.mload freePtrWord).1.toNat +
                32 * (slot + 1) ≤
              EvmYul.MachineState.M
                (frameBumpMachine (slot + 1)
                  preludeEvm.toMachineState).activeWords.toNat
                ((preludeEvm.toMachineState.mload freePtrWord).1.toNat +
                  32 * slot) 32 * 32)
          (_hActiveAfter :
            EvmYul.MachineState.M
                (frameBumpMachine (slot + 1)
                  preludeEvm.toMachineState).activeWords.toNat
                ((preludeEvm.toMachineState.mload freePtrWord).1.toNat +
                  32 * slot) 32 * 32 <
              EvmYul.UInt256.size)
          (_hSharedInit :
            ∀ initState,
              Structured.Code.run (frameInitCode (slot + 1)) preludeEvm =
                  .ok initState →
                SharedStateEqOutsideScratch
                  (range (preludeEvm.toMachineState.mload freePtrWord).1
                    (slot + 1)) sourceAfterPrelude.shared
                  initState.toSharedState),
        ∃ final,
          Expressions.Block.run compiledProgram
              ((blockFuel + 2 * rest.length + 2) + prelude.length)
              mainPlan.block { runState with evm := evmState } =
            .ok (Expressions.Outcome.regular
              ({ runState with evm := final })) ∧
          final.stack =
            (preludeEvm.toMachineState.mload freePtrWord).1 ::
              evmState.stack ∧
          ScratchRegionReady final.toMachineState
            (range (preludeEvm.toMachineState.mload freePtrWord).1
              (slot + 1)).base
            (range (preludeEvm.toMachineState.mload freePtrWord).1
              (slot + 1)).words ∧
          SharedStateEqOutsideScratch
            (range (preludeEvm.toMachineState.mload freePtrWord).1
              (slot + 1)) source'.shared final.toSharedState ∧
          FrameStoreRel mainPlan.state.env source'.vars final.toMachineState
            (preludeEvm.toMachineState.mload freePtrWord).1) := by
  rcases
      run_compileMain?_atomic_withPrelude_block_frameStore_of_full_source_run_open_regular
        hSpec hWordBytes
        (ctx := ctx)
        (compileState := ({ env := [], nextSlot := startSlot } : CompileState))
        (stmts := stmts)
        (rest := rest)
        (prelude := prelude)
        (mainPlan := mainPlan)
        (sourceProgram := sourceProgram)
        (compiledProgram := compiledProgram)
        (source := source)
        (source' := source')
        (sourceCtx := sourceCtx)
        (sourceCtx' := sourceCtx')
        (sourceFuel := sourceFuel)
        (blockFuel := blockFuel)
        (runState := runState)
        (evmState := evmState)
        (words := slot + 1)
        hSplit hCompile hSafe hRun
        (StateSlotsBounded.empty startSlot)
        (StateSlotsNodup.empty startSlot)
        hFrameWords hSharedStart with
    ⟨sourceAfterPrelude, sourceCtxAfterPrelude, preludeEvm, restFuel,
      hPreludeShared, hPreludeStack, hRestRun, hCont⟩
  refine
    ⟨sourceAfterPrelude, sourceCtxAfterPrelude, preludeEvm, restFuel,
      hPreludeShared, hPreludeStack, hRestRun, ?_⟩
  intro hOffsetLtUInt hPadNoOverflow hWithinAfter hActiveAfter hSharedInit
  rcases
      run_frameInitCode_ready_succ hSpec hWordBytes preludeEvm slot
        hOffsetLtUInt hPadNoOverflow hWithinAfter hActiveAfter with
    ⟨initState, hInitRun, hInitStack, _hInitMachine, hReady⟩
  exact
    hCont hInitRun hInitStack hReady
      (hSharedInit initState hInitRun)
      FrameStoreRel.empty

theorem run_compileStmt?_expr_block_frameStore_of_source_run_regular
    {ctx : CompileCtx} {returns : List Name}
    {compileState : CompileState} {expr : Expr 0} {plan : Plan}
    {sourceProgram : Program} {compiledProgram : Expressions.Program}
    {source source' : Locals.Source.State}
    {sourceCtx sourceCtx' : EvmCompiler.Functions.Source.Ctx}
    {sourceFuel blockFuel : Nat}
    {runState : Expressions.RunState}
    {evmState : EVMState} {base : Word} {words : Nat}
    (hCompile :
      compileStmt? ctx returns compileState (.expr expr) = some plan)
    (hSafe : SourceExprSafe expr)
    (hRun :
      EvmCompiler.Functions.Source.Stmt.run
          Locals.Source.PrimitiveSemantics.structured
          sourceProgram sourceCtx sourceFuel (.expr expr) source =
        .ok (EvmCompiler.Functions.Source.Outcome.regular source',
          sourceCtx'))
    (hStateBound : StateSlotsBounded compileState)
    (hFrameWords : compileState.nextSlot ≤ words)
    (hReady : ScratchRegionReady evmState.toMachineState
      (range base words).base (range base words).words)
    (hShared : SharedStateEqOutsideScratch (range base words) source.shared
      evmState.toSharedState)
    (hRel : FrameStoreRel compileState.env source.vars
      evmState.toMachineState base)
    (rest : EvmYul.Stack Word) :
    ∃ final,
      plan.state = compileState ∧
      Expressions.Block.run compiledProgram (blockFuel + 2) plan.block
          { runState with evm := { evmState with stack := base :: rest } } =
        .ok (Expressions.Outcome.regular ({ runState with evm := final })) ∧
      final.stack = base :: rest ∧
      ScratchRegionReady final.toMachineState
        (range base words).base (range base words).words ∧
      SharedStateEqOutsideScratch (range base words) source'.shared
        final.toSharedState ∧
      FrameStoreRel compileState.env source'.vars final.toMachineState base := by
  rcases
      run_compileStmt?_expr_frameStore_of_source_run_regular
        hCompile hSafe hRun hStateBound hFrameWords hReady hShared hRel
        rest with
    ⟨final, code, hPlanState, hBlock, hCodeRun, hStack, hReadyFinal,
      hSharedFinal, hRelFinal⟩
  refine
    ⟨final, hPlanState, ?_, hStack, hReadyFinal, hSharedFinal, hRelFinal⟩
  rw [hBlock]
  exact
    run_blockOfCode_regular_of_code_run
      (program := compiledProgram) (fuel := blockFuel)
      (state := { runState with evm := { evmState with stack := base :: rest } })
      hCodeRun

theorem run_compileStmt?_let_block_frameStore_of_source_run_regular
    (hSpec : ZeroPaddingSpec)
    (hWordBytes : WordByteEncodingSpec)
    {ctx : CompileCtx} {returns : List Name}
    {compileState : CompileState} {name : Name} {valueExpr : Expr 1}
    {plan : Plan}
    {sourceProgram : Program} {compiledProgram : Expressions.Program}
    {source source' : Locals.Source.State}
    {sourceCtx sourceCtx' : EvmCompiler.Functions.Source.Ctx}
    {sourceFuel blockFuel : Nat}
    {runState : Expressions.RunState}
    {evmState : EVMState} {base : Word} {words : Nat}
    (hCompile :
      compileStmt? ctx returns compileState (.let_ name valueExpr) =
        some plan)
    (hSafe : SourceExprSafe valueExpr)
    (hRun :
      EvmCompiler.Functions.Source.Stmt.run
          Locals.Source.PrimitiveSemantics.structured
          sourceProgram sourceCtx sourceFuel (.let_ name valueExpr) source =
        .ok (EvmCompiler.Functions.Source.Outcome.regular source',
          sourceCtx'))
    (hStateBound : StateSlotsBounded compileState)
    (hFrameWords : plan.state.nextSlot ≤ words)
    (hReady : ScratchRegionReady evmState.toMachineState
      (range base words).base (range base words).words)
    (hShared : SharedStateEqOutsideScratch (range base words) source.shared
      evmState.toSharedState)
    (hRel : FrameStoreRel compileState.env source.vars
      evmState.toMachineState base)
    (rest : EvmYul.Stack Word) :
    ∃ final,
      Expressions.Block.run compiledProgram (blockFuel + 2) plan.block
          { runState with evm := { evmState with stack := base :: rest } } =
        .ok (Expressions.Outcome.regular ({ runState with evm := final })) ∧
      final.stack = base :: rest ∧
      ScratchRegionReady final.toMachineState
        (range base words).base (range base words).words ∧
      SharedStateEqOutsideScratch (range base words) source'.shared
        final.toSharedState ∧
      FrameStoreRel plan.state.env source'.vars final.toMachineState base := by
  rcases
      run_compileStmt?_let_frameStore_of_source_run_regular
        hSpec hWordBytes hCompile hSafe hRun hStateBound hFrameWords
        hReady hShared hRel rest with
    ⟨final, code, hBlock, hCodeRun, hStack, hReadyFinal,
      hSharedFinal, hRelFinal⟩
  refine ⟨final, ?_, hStack, hReadyFinal, hSharedFinal, hRelFinal⟩
  rw [hBlock]
  exact
    run_blockOfCode_regular_of_code_run
      (program := compiledProgram) (fuel := blockFuel)
      (state := { runState with evm := { evmState with stack := base :: rest } })
      hCodeRun

theorem run_compileStmt?_assign_block_frameStore_of_source_run_regular
    (hSpec : ZeroPaddingSpec)
    (hWordBytes : WordByteEncodingSpec)
    {ctx : CompileCtx} {returns : List Name}
    {compileState : CompileState} {name : Name} {valueExpr : Expr 1}
    {plan : Plan}
    {sourceProgram : Program} {compiledProgram : Expressions.Program}
    {source source' : Locals.Source.State}
    {sourceCtx sourceCtx' : EvmCompiler.Functions.Source.Ctx}
    {sourceFuel blockFuel : Nat}
    {runState : Expressions.RunState}
    {evmState : EVMState} {base : Word} {words : Nat}
    (hCompile :
      compileStmt? ctx returns compileState (.assign name valueExpr) =
        some plan)
    (hSafe : SourceExprSafe valueExpr)
    (hRun :
      EvmCompiler.Functions.Source.Stmt.run
          Locals.Source.PrimitiveSemantics.structured
          sourceProgram sourceCtx sourceFuel (.assign name valueExpr) source =
        .ok (EvmCompiler.Functions.Source.Outcome.regular source',
          sourceCtx'))
    (hStateBound : StateSlotsBounded compileState)
    (hStateNodup : StateSlotsNodup compileState)
    (hFrameWords : compileState.nextSlot ≤ words)
    (hReady : ScratchRegionReady evmState.toMachineState
      (range base words).base (range base words).words)
    (hShared : SharedStateEqOutsideScratch (range base words) source.shared
      evmState.toSharedState)
    (hRel : FrameStoreRel compileState.env source.vars
      evmState.toMachineState base)
    (rest : EvmYul.Stack Word) :
    ∃ final,
      Expressions.Block.run compiledProgram (blockFuel + 2) plan.block
          { runState with evm := { evmState with stack := base :: rest } } =
        .ok (Expressions.Outcome.regular ({ runState with evm := final })) ∧
      final.stack = base :: rest ∧
      ScratchRegionReady final.toMachineState
        (range base words).base (range base words).words ∧
      SharedStateEqOutsideScratch (range base words) source'.shared
        final.toSharedState ∧
      FrameStoreRel compileState.env source'.vars final.toMachineState base := by
  rcases
      run_compileStmt?_assign_frameStore_of_source_run_regular
        hSpec hWordBytes hCompile hSafe hRun hStateBound hStateNodup
        hFrameWords hReady hShared hRel rest with
    ⟨final, code, hBlock, hCodeRun, hStack, hReadyFinal,
      hSharedFinal, hRelFinal⟩
  refine ⟨final, ?_, hStack, hReadyFinal, hSharedFinal, hRelFinal⟩
  rw [hBlock]
  exact
    run_blockOfCode_regular_of_code_run
      (program := compiledProgram) (fuel := blockFuel)
      (state := { runState with evm := { evmState with stack := base :: rest } })
      hCodeRun

end FrameMemory

end ScratchFrameSpill
end Functions
end EvmCompiler
