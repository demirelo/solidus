import EvmCompiler.Assembly.Syntax

/-!
# Literal-push encoding

A source-level `push value` does not have to lower to a literal `PUSH`.  Wide
all-ones masks (`0xff…ff`, ubiquitous in ABI and storage-packing code) are
re-encoded as `NOT 0` shifted right, which compacts to a fixed five bytes
regardless of the mask width instead of `1 + w`.

This module sits directly on top of `Assembly.Syntax` — below *every* semantics
layer — because each layer that steps a `push` must advance the program counter
by exactly the number of bytes the lowering emits.  Keeping the encoding in one
place is what makes those pc deltas agree by construction.
-/

namespace EvmCompiler
namespace Assembly

/-- If `value` is the all-ones mask `2 ^ (8 * w) - 1` for some byte width
`5 ≤ w ≤ 31`, return `w`.

Widths below 5 are excluded on purpose: the computed encoding costs a fixed
5 bytes after compaction (`PUSH0; NOT; PUSH1 s; SHR`), so it only pays for
itself once the literal `PUSH w` would cost `1 + w > 5` bytes.  Width 32 is
excluded because `2 ^ 256 - 1` needs no shift and does not occur in practice.

The `% 256 = 255` test is a cheap pre-filter: every all-ones mask ends in
`0xff`, and almost no other constant does, so the 27-way search below runs
only on genuine candidates. -/
def maskWidth? (value : Word) : Option Nat :=
  if value.toNat % 256 = 255 then
    (List.range' 5 27).find? fun w => value.toNat = 2 ^ (8 * w) - 1
  else
    none

/-- Assembly encoding of a literal push. -/
def pushCode (value : Word) : Program :=
  match maskWidth? value with
  | some w =>
      [ .push (EvmYul.UInt256.ofNat 0), .prim .not
      , .push (EvmYul.UInt256.ofNat (256 - 8 * w)), .prim .shr ]
  | none => [.push value]

theorem maskWidth?_spec {value : Word} {w : Nat}
    (hMask : maskWidth? value = some w) :
    5 ≤ w ∧ w ≤ 31 ∧ value.toNat = 2 ^ (8 * w) - 1 := by
  unfold maskWidth? at hMask
  by_cases hLow : value.toNat % 256 = 255
  · rw [if_pos hLow] at hMask
    have hMem := List.mem_of_find?_eq_some hMask
    have hCheck := List.find?_some hMask
    have hRange := List.mem_range'_1.mp hMem
    exact ⟨by omega, by omega, by simpa using hCheck⟩
  · rw [if_neg hLow] at hMask
    exact absurd hMask (by simp)

/-- The emitted byte length of a push encoding: a literal `PUSH32` is 33 bytes,
the computed mask form is `33 + 1 + 33 + 1`. -/
theorem pushCode_byteLength (value : Word) :
    Program.byteLength (pushCode value) =
      match maskWidth? value with
      | some _ => 68
      | none => 33 := by
  unfold pushCode
  cases maskWidth? value <;>
    simp [Program.byteLength, Instr.byteSize, Instr.push32Size]

/-- The program-counter delta a single `push value` must advance by: exactly
the number of bytes its lowering emits. -/
def pushPcDelta (value : Word) : Nat :=
  Program.byteLength (pushCode value)

end Assembly
end EvmCompiler
