import Proofs.Runtime.Caliper.WordBinary

/-! Natural-number subtraction on bounded words. Underflow is detected by an
executed comparison and branch; the result is zero rather than modular wraparound. -/

namespace Signatures.Runtime.CaliperBackend.Saturating

open Caliper

variable {w : Nat}

def subtract (value : Word w × Word w) : Word w :=
  if value.1.toNat < value.2.toNat then 0 else value.1 - value.2

def code : Stmt w := WordBinary.load ;; .bin .ult 3 1 2 ;;
  .ifNZ 3 (.imm 1 0) (.bin .sub 1 1 2) ;; WordBinary.finish

def time (cost : CostModel) (value : Word w × Word w) : Nat :=
  cost.memLoad + (cost.imm + cost.memLoad) +
    (cost.bin .ult + ((cost.branch + (if value.1.toNat < value.2.toNat then cost.imm else cost.bin .sub)) +
      (cost.memStore + cost.memPop)))

theorem descriptionFits (hw : 16 < 2 ^ w) : DescriptionFits (code (w := w)) := by
  have ult := WordBinary.descriptionFits (w := w) .ult hw
  have sub := WordBinary.descriptionFits (w := w) .sub hw
  have positive := (width_pos hw).ne'
  simp [WordBinary.code, WordBinary.load, WordBinary.finish, DescriptionFits, description, positive] at ult sub
  simp [code, WordBinary.load, WordBinary.finish, DescriptionFits, description, positive]
  omega

theorem descriptionWords_eq : descriptionWords (code (w := w)) = 38 := rfl

theorem exec (cost : CostModel) (tape : RandomTape w) (left right : Word w)
    (before : State w) (zero : before.regs 0 = 0) (contents : before.bufs 0 = #[left, right])
    (hw : 0 < w) :
    ∃ after, Caliper.Exec cost tape code before after (time cost (left, right)) 0 0 ∧
      after.bufs 0 = #[subtract (left, right)] ∧ after.regs 0 = before.regs 0 ∧ after.caps = before.caps := by
  have read := WordBinary.load_exec cost tape left right before zero contents hw
  let loaded := WordBinary.loaded before left right
  let compared := loaded.setReg 3 (if left.toNat < right.toNat then 1 else 0)
  have comparison : Caliper.Exec cost tape (.bin .ult 3 1 2) loaded compared (cost.bin .ult) 0 0 := by
    convert Caliper.Exec.bin (C := cost) (tape := tape) (s := loaded) (op := .ult) (d := 3) (a := 1) (b := 2) using 1
    simp [compared, loaded, WordBinary.loaded]
  have branch : ∃ selected, Caliper.Exec cost tape (.ifNZ 3 (.imm 1 0) (.bin .sub 1 1 2)) compared selected
      (cost.branch + (if left.toNat < right.toNat then cost.imm else cost.bin .sub)) 0 0 ∧
      selected.regs 1 = subtract (left, right) ∧ selected.regs 0 = before.regs 0 ∧
      selected.bufs 0 = before.bufs 0 ∧ selected.caps = before.caps := by
    by_cases underflow : left.toNat < right.toNat
    · refine ⟨compared.setReg 1 0, ?_, ?_, ?_, rfl, rfl⟩
      · simpa [underflow] using Caliper.Exec.ifNZ_true (C := cost) (tape := tape) (s := compared)
          (c := 3) (els := .bin .sub 1 1 2) (by simp [compared, underflow, hw.ne'])
          (Caliper.Exec.imm (C := cost) (tape := tape) (s := compared) (d := 1) (v := 0))
      · simp [subtract, underflow]
      · simp [compared, loaded, WordBinary.loaded]
    · have difference : Caliper.Exec cost tape (.bin .sub 1 1 2) compared (compared.setReg 1 (left - right)) (cost.bin .sub) 0 0 := by
        convert Caliper.Exec.bin (C := cost) (tape := tape) (s := compared) (op := .sub) (d := 1) (a := 1) (b := 2) using 1
        simp [compared, loaded, WordBinary.loaded]
      exact ⟨compared.setReg 1 (left - right),
        by
          simpa [underflow] using (Caliper.Exec.ifNZ_false (c := 3) (thn := .imm 1 0)
            (by simp [compared, underflow]) difference),
        by simp [subtract, underflow], by simp [compared, loaded, WordBinary.loaded], rfl, rfl⟩
  obtain ⟨selected, selectedExec, value, offset, original, capacities⟩ := branch
  obtain ⟨after, written, result, finalZero, finalCaps⟩ := WordBinary.finish_exec cost tape left right selected
    (offset.trans zero) (original.trans contents)
  exact ⟨after, by simpa [code, time] using Caliper.Exec.seq read (Caliper.Exec.seq comparison (Caliper.Exec.seq selectedExec written)),
    by rw [result, value], finalZero.trans offset, finalCaps.trans capacities⟩

def realizer (cost : CostModel) (hw : 16 < 2 ^ w) :
    Realizer cost (WordBinary.pair w hw) (wordRepresentation w (width_pos hw)) subtract where
  code := code
  positive_width := width_pos hw
  description_fits := descriptionFits hw
  random_free := by trivial
  time := time cost
  net _ := 0
  workspace _ := 0
  correct tape value before represented := by
    have contents : before.bufs 0 = #[value.1, value.2] := by
      have array := congrArg List.toArray represented.2.1
      simpa [WordBinary.pair, wordRepresentation, wordEncoding, Representation.prod, Encoding.prod, Encoding.checked] using array
    obtain ⟨after, execution, result, zero, caps⟩ := exec cost tape value.1 value.2 before represented.1 contents (width_pos hw)
    exact ⟨after, 0, 0, execution,
      ⟨zero.trans represented.1, by simp [result, wordRepresentation, wordEncoding],
        execution.wellFormed_preserved represented.2.2.1, by intro buffer; rw [caps]; exact represented.2.2.2 buffer⟩,
      le_rfl, le_rfl⟩

theorem time_unit (value : Word w × Word w) : time .unit value = 8 := by simp [time, CostModel.unit]

end Signatures.Runtime.CaliperBackend.Saturating
