import Proofs.Runtime.Caliper.Layouts

/-! Executable bounded-layout wiring. Copying a statically sized slice expands
to ordinary load/push instructions. Both runtime and generated code grow linearly
in the declared slice size; there is no free host-language list operation.
-/

namespace Signatures.Runtime.CaliperBackend

open Caliper

variable {w : Nat}

theorem width_pos (hw : 16 < 2 ^ w) : 0 < w := by
  by_contra h
  have hw0 : w = 0 := by omega
  subst w
  norm_num at hw

/-- Registers 1 and 2 hold the current index and copied word. Destination storage
must already be reserved. Source and destination must be distinct buffers. -/
def copySlice (source destination start : Nat) : Nat → Stmt w
  | 0 => .skip
  | count + 1 =>
      .imm 1 (BitVec.ofNat w start) ;;
      .memLoad 2 source 1 ;;
      .memPush destination 2 ;;
      copySlice source destination (start + 1) count

def sliceWordTime (cost : CostModel) : Nat := cost.imm + cost.memLoad + cost.memPush

theorem copySlice_straight (source destination start count : Nat) :
    (copySlice (w := w) source destination start count).Straight := by
  induction count generalizing start <;> simp_all [copySlice, Stmt.Straight]

theorem copySlice_preserves_zero (source destination start count : Nat) :
    ¬ (copySlice (w := w) source destination start count).Writes 0 := by
  induction count generalizing start <;> simp_all [copySlice, Stmt.Writes]

theorem copySlice_staticTime (cost : CostModel) (source destination start count : Nat) :
    (copySlice (w := w) source destination start count).staticTime cost = count * sliceWordTime cost := by
  induction count generalizing start with
  | zero => simp [copySlice, Stmt.staticTime]
  | succ count ih => simp [copySlice, Stmt.staticTime, ih, sliceWordTime]; ring

theorem copySlice_descriptionFits (source destination start count : Nat)
    (hw : 16 < 2 ^ w) (hs : source < 2 ^ w) (hd : destination < 2 ^ w) :
    DescriptionFits (copySlice (w := w) source destination start count) := by
  induction count generalizing start with
  | zero => simp [DescriptionFits, copySlice, description]
  | succ count ih =>
    have hp := width_pos hw
    have hword := (BitVec.ofNat w start).isLt
    apply DescriptionFits.seq hp (by simp [DescriptionFits, description]; omega)
    apply DescriptionFits.seq hp (by simp [DescriptionFits, description]; omega)
    apply DescriptionFits.seq hp (by simp [DescriptionFits, description]; omega)
    exact ih (start + 1)

theorem copySlice_randomFree (source destination start count : Nat) :
    (copySlice (w := w) source destination start count).RandomFree := by
  induction count generalizing start <;> simp_all [copySlice, Stmt.RandomFree]

theorem copySlice_touches (source destination start count buffer : Nat)
    (touched : (copySlice (w := w) source destination start count).Touches buffer) :
    buffer = destination := by
  induction count generalizing start with
  | zero => cases touched
  | succ count ih =>
    simp only [copySlice, Stmt.Touches, false_or] at touched
    exact touched.elim id (ih _)

theorem copySlice_descriptionWords (source destination start count : Nat) :
    descriptionWords (copySlice (w := w) source destination start count) = 13 * count + 1 := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
    simp only [copySlice, descriptionWords_seq, ih]
    simp [descriptionWords, description]
    omega

/-- Exact instruction cost and zero additional allocation. The output specification
is stated on actual buffer contents; capacity and address bounds prove all accesses
safe and prevent modular wraparound of the copied indices. -/
theorem copySlice_exec (cost : CostModel) (tape : RandomTape w)
    (source destination : BufId) (distinct : destination ≠ source)
    (count start : Nat) (before : State w)
    (span : start + count ≤ (before.bufs source).size)
    (fits : (before.bufs source).size < 2 ^ w)
    (room : (before.bufs destination).size + count ≤ before.caps destination) :
    ∃ after,
      Caliper.Exec cost tape (copySlice source destination start count)
        before after (count * sliceWordTime cost) 0 0 ∧
      (after.bufs destination).toList = (before.bufs destination).toList ++
        ((before.bufs source).toList.drop start).take count ∧
      after.caps = before.caps := by
  induction count generalizing start before with
  | zero => exact ⟨before, by simpa [copySlice] using (Caliper.Exec.skip (C := cost) (tape := tape) (s := before)), by simp, rfl⟩
  | succ count ih =>
    have hindex : start < (before.bufs source).size := by omega
    have hword : (BitVec.ofNat w start).toNat = start := by
      simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hindex.trans fits)]
    let indexed := before.setReg 1 (BitVec.ofNat w start)
    let loaded := indexed.setReg 2 (before.bufs source)[start]
    let pushed := loaded.setBuf destination ((before.bufs destination).push (before.bufs source)[start])
    have he₁ : Caliper.Exec cost tape (.imm 1 (BitVec.ofNat w start)) before indexed cost.imm 0 0 := .imm
    have hload : (indexed.regs 1).toNat < (indexed.bufs source).size := by
      simpa [indexed, hword] using hindex
    have he₂ : Caliper.Exec cost tape (.memLoad 2 source 1) indexed loaded cost.memLoad 0 0 := by
      convert Caliper.Exec.memLoad (C := cost) (tape := tape) hload using 1
      simp [loaded, indexed, hword]
    have hpush : (loaded.bufs destination).size < loaded.caps destination := by
      simp only [loaded, indexed, bufs_setReg, caps_setReg]
      omega
    have he₃ : Caliper.Exec cost tape (.memPush destination 2) loaded pushed cost.memPush 0 0 := by
      convert Caliper.Exec.memPush (C := cost) (tape := tape) (src := 2) hpush using 1
      simp [pushed, loaded, indexed]
    have hs : pushed.bufs source = before.bufs source := by
      simp [pushed, loaded, indexed, bufs_setBuf_ne _ _ (Ne.symm distinct)]
    have hd : pushed.bufs destination = (before.bufs destination).push (before.bufs source)[start] := by
      simp [pushed]
    obtain ⟨after, he, hout, hc⟩ := ih (start + 1) pushed
      (by rw [hs]; omega) (by rw [hs]; exact fits)
      (by simp only [hd, Array.size_push, pushed, loaded, indexed, caps_setBuf, caps_setReg]; omega)
    refine ⟨after, ?_, ?_, hc⟩
    · simpa [copySlice, sliceWordTime, Nat.succ_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Caliper.Exec.seq he₁ (Caliper.Exec.seq he₂ (Caliper.Exec.seq he₃ he))
    · rw [hout, hs, hd, Array.toList_push]
      rw [List.drop_eq_getElem_cons (i := start) (l := (before.bufs source).toList) (by simpa using hindex)]
      simp [List.append_assoc]

end Signatures.Runtime.CaliperBackend
