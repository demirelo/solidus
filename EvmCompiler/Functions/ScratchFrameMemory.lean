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
