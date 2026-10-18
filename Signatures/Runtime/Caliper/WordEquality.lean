import Signatures.Runtime.Caliper.Boolean

/-! Executed equality of two stored word slices. Each comparison loads both
words and updates a Boolean accumulator with word equality and bitwise AND.
The scan does not allocate or modify buffers. Its code is unrolled by the
declared encoding width, with linear time and stored-code size. -/

namespace Signatures.Runtime.CaliperBackend.WordEquality

open Caliper

variable {w : Nat}

def bit (value : Bool) : Word w := if value then 1 else 0

def step (left right : Nat) : Stmt w :=
  .imm 1 (BitVec.ofNat w left) ;; .memLoad 2 0 1 ;;
  .imm 1 (BitVec.ofNat w right) ;; .memLoad 3 0 1 ;;
  .bin .eq 2 2 3 ;; .bin .and 4 4 2

def scan (left right : Nat) : Nat → Stmt w
  | 0 => .skip
  | count + 1 => step left right ;; scan (left + 1) (right + 1) count

def wordTime (cost : CostModel) : Nat :=
  cost.imm + (cost.memLoad + (cost.imm + (cost.memLoad + (cost.bin .eq + cost.bin .and))))

/-- Specification of the scan, not an instruction available to the machine. -/
def equalSlices (bytes : Array (Word w)) (left right : Nat) : Nat → Bool
  | 0 => true
  | count + 1 => decide (bytes[left]?.getD 0 = bytes[right]?.getD 0) &&
      equalSlices bytes (left + 1) (right + 1) count

theorem equalSlices_eq (bytes : Array (Word w)) (left right count : Nat)
    (leftSpan : left + count ≤ bytes.size) (rightSpan : right + count ≤ bytes.size) :
    equalSlices bytes left right count =
      decide ((bytes.toList.drop left).take count = (bytes.toList.drop right).take count) := by
  induction count generalizing left right with
  | zero => simp [equalSlices]
  | succ count ih =>
    have hl : left < bytes.size := by omega
    have hr : right < bytes.size := by omega
    rw [equalSlices, ih (left + 1) (right + 1) (by omega) (by omega)]
    rw [List.drop_eq_getElem_cons (l := bytes.toList) (i := left) (by simpa using hl),
      List.drop_eq_getElem_cons (l := bytes.toList) (i := right) (by simpa using hr)]
    simp [hl, hr]

theorem step_exec (cost : CostModel) (tape : RandomTape w) (left right : Nat) (before : State w)
    (leftIndex : left < (before.bufs 0).size) (rightIndex : right < (before.bufs 0).size)
    (fits : (before.bufs 0).size < 2 ^ w) :
    ∃ after, Caliper.Exec cost tape (step left right) before after (wordTime cost) 0 0 ∧
      after.regs 4 = before.regs 4 &&& (BinOp.eq.eval (before.bufs 0)[left] (before.bufs 0)[right]) ∧
      after.bufs = before.bufs ∧ after.caps = before.caps ∧ after.regs 0 = before.regs 0 := by
  have hl : (BitVec.ofNat w left).toNat = left := by
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (leftIndex.trans fits)]
  have hr : (BitVec.ofNat w right).toNat = right := by
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (rightIndex.trans fits)]
  let indexedLeft := before.setReg 1 (BitVec.ofNat w left)
  let loadedLeft := indexedLeft.setReg 2 (before.bufs 0)[left]
  let indexedRight := loadedLeft.setReg 1 (BitVec.ofNat w right)
  let loadedRight := indexedRight.setReg 3 (before.bufs 0)[right]
  let compared := loadedRight.setReg 2 (BinOp.eq.eval (before.bufs 0)[left] (before.bufs 0)[right])
  let after := compared.setReg 4 (before.regs 4 &&& (BinOp.eq.eval (before.bufs 0)[left] (before.bufs 0)[right]))
  have readLeft : Caliper.Exec cost tape (.memLoad 2 0 1) indexedLeft loadedLeft cost.memLoad 0 0 := by
    convert Caliper.Exec.memLoad (C := cost) (tape := tape) (s := indexedLeft) (d := 2) (b := 0) (i := 1)
      (by simpa [indexedLeft, hl] using leftIndex) using 1
    simp [loadedLeft, indexedLeft, hl]
  have readRight : Caliper.Exec cost tape (.memLoad 3 0 1) indexedRight loadedRight cost.memLoad 0 0 := by
    convert Caliper.Exec.memLoad (C := cost) (tape := tape) (s := indexedRight) (d := 3) (b := 0) (i := 1)
      (by simpa [indexedRight, loadedLeft, indexedLeft, hr] using rightIndex) using 1
    simp [loadedRight, indexedRight, loadedLeft, indexedLeft, hr]
  have compare : Caliper.Exec cost tape (.bin .eq 2 2 3) loadedRight compared (cost.bin .eq) 0 0 := by
    convert Caliper.Exec.bin (C := cost) (tape := tape) (s := loadedRight) (op := .eq) (d := 2) (a := 2) (b := 3) using 1
    simp [compared, loadedRight, indexedRight, loadedLeft, indexedLeft]
  have accumulate : Caliper.Exec cost tape (.bin .and 4 4 2) compared after (cost.bin .and) 0 0 := by
    convert Caliper.Exec.bin (C := cost) (tape := tape) (s := compared) (op := .and) (d := 4) (a := 4) (b := 2) using 1
    simp [after, compared, loadedRight, indexedRight, loadedLeft, indexedLeft]
  have execution := Caliper.Exec.seq (Caliper.Exec.imm (C := cost) (tape := tape) (s := before)
    (d := 1) (v := BitVec.ofNat w left)) (Caliper.Exec.seq readLeft
      (Caliper.Exec.seq (Caliper.Exec.imm (C := cost) (tape := tape) (s := loadedLeft)
        (d := 1) (v := BitVec.ofNat w right)) (Caliper.Exec.seq readRight (Caliper.Exec.seq compare accumulate))))
  exact ⟨after, by simpa [step, wordTime] using execution, by simp [after], rfl, rfl,
    by simp [after, compared, loadedRight, indexedRight, loadedLeft, indexedLeft]⟩

theorem bit_and_eq (acc : Bool) (left right : Word w) :
    bit acc &&& BinOp.eq.eval left right = bit (acc && decide (left = right)) := by
  cases acc <;> by_cases equal : left = right <;> simp [bit, BinOp.eval, equal]

theorem scan_exec (cost : CostModel) (tape : RandomTape w) (count left right : Nat)
    (before : State w) (acc : Bool) (accumulator : before.regs 4 = bit acc)
    (leftSpan : left + count ≤ (before.bufs 0).size) (rightSpan : right + count ≤ (before.bufs 0).size)
    (fits : (before.bufs 0).size < 2 ^ w) :
    ∃ after, Caliper.Exec cost tape (scan left right count) before after (count * wordTime cost) 0 0 ∧
      after.regs 4 = bit (acc && equalSlices (before.bufs 0) left right count) ∧
      after.bufs = before.bufs ∧ after.caps = before.caps ∧ after.regs 0 = before.regs 0 := by
  induction count generalizing left right before acc with
  | zero => exact ⟨before, by simpa [scan] using (Caliper.Exec.skip (C := cost) (tape := tape) (s := before)),
      by simpa [equalSlices] using accumulator, rfl, rfl, rfl⟩
  | succ count ih =>
    have hl : left < (before.bufs 0).size := by omega
    have hr : right < (before.bufs 0).size := by omega
    obtain ⟨compared, compare, value, bytes, capacities, zero⟩ := step_exec cost tape left right before hl hr fits
    rw [accumulator, bit_and_eq] at value
    obtain ⟨after, rest, result, finalBytes, finalCaps, finalZero⟩ :=
      ih (left + 1) (right + 1) compared (acc && decide ((before.bufs 0)[left] = (before.bufs 0)[right])) value
        (by rw [bytes]; omega) (by rw [bytes]; omega) (by rw [bytes]; exact fits)
    refine ⟨after, ?_, ?_, finalBytes.trans bytes, finalCaps.trans capacities, finalZero.trans zero⟩
    · simpa [scan, Nat.succ_mul, Nat.add_comm] using Caliper.Exec.seq compare rest
    · simpa [equalSlices, bytes, hl, hr, Bool.and_assoc] using result

theorem scan_straight (left right count : Nat) : (scan (w := w) left right count).Straight := by
  induction count generalizing left right <;> simp_all [scan, step, Stmt.Straight]

theorem scan_randomFree (left right count : Nat) : (scan (w := w) left right count).RandomFree := by
  induction count generalizing left right <;> simp_all [scan, step, Stmt.RandomFree]

theorem scan_descriptionWords (left right count : Nat) :
    descriptionWords (scan (w := w) left right count) = 30 * count + 1 := by
  induction count generalizing left right with
  | zero => rfl
  | succ count ih =>
    rw [scan, descriptionWords_seq, ih]
    have stepWords : descriptionWords (step (w := w) left right) = 29 := rfl
    rw [stepWords]
    omega

theorem scan_descriptionFits (left right count : Nat) (hw : 16 < 2 ^ w) :
    DescriptionFits (scan (w := w) left right count) := by
  induction count generalizing left right with
  | zero => simp [scan, DescriptionFits, description]
  | succ count ih =>
    apply DescriptionFits.seq (width_pos hw)
    · have hl := Nat.mod_lt left (show 0 < 2 ^ w by positivity)
      have hr := Nat.mod_lt right (show 0 < 2 ^ w by positivity)
      have positive := (width_pos hw).ne'
      have eqTags : ∀ token ∈ description (.bin .eq 2 2 3 : Stmt w), token ≤ 16 :=
        (show ∀ token ∈ description (.bin .eq 2 2 3 : Stmt 0), token ≤ 16 from by decide)
      have andTags : ∀ token ∈ description (.bin .and 4 4 2 : Stmt w), token ≤ 16 :=
        (show ∀ token ∈ description (.bin .and 4 4 2 : Stmt 0), token ≤ 16 from by decide)
      simp [description] at eqTags andTags
      simp [step, DescriptionFits, description, positive]
      omega
    · exact ih _ _

end Signatures.Runtime.CaliperBackend.WordEquality
