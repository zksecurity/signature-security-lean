import Proofs.Runtime.Caliper.Words
import Proofs.Runtime.Caliper.Layouts
import Proofs.Runtime.Caliper.CellArithmetic

/-! Binary word operations with actual loads, arithmetic, store and truncation.
The reserved input capacity remains charged after the two-word input becomes a
one-word output. Register zero and all capacities are preserved. -/

namespace Signatures.Runtime.CaliperBackend.WordBinary

open Caliper

variable {w : Nat}

def load : Stmt w := .memLoad 1 0 0 ;; .imm 2 1 ;; .memLoad 2 0 2
def finish : Stmt w := .memStore 0 0 1 ;; .memPop 0
def code (op : BinOp) : Stmt w := load ;; .bin op 1 1 2 ;; finish

def loaded (before : State w) (left right : Word w) : State w :=
  ((before.setReg 1 left).setReg 2 1).setReg 2 right

theorem load_exec (cost : CostModel) (tape : RandomTape w) (left right : Word w)
    (before : State w) (zero : before.regs 0 = 0) (contents : before.bufs 0 = #[left, right])
    (hw : 0 < w) : Caliper.Exec cost tape load before (loaded before left right)
      (cost.memLoad + (cost.imm + cost.memLoad)) 0 0 := by
  have first : Caliper.Exec cost tape (.memLoad 1 0 0) before (before.setReg 1 left) cost.memLoad 0 0 := by
    convert Caliper.Exec.memLoad (C := cost) (tape := tape) (s := before) (d := 1) (b := 0) (i := 0)
      (by simp [zero, contents]) using 1
    simp [zero, contents]
  have second : Caliper.Exec cost tape (.memLoad 2 0 2) ((before.setReg 1 left).setReg 2 1)
      (loaded before left right) cost.memLoad 0 0 := by
    convert Caliper.Exec.memLoad (C := cost) (tape := tape) (s := (before.setReg 1 left).setReg 2 1)
      (d := 2) (b := 0) (i := 2) (by simp [contents, Nat.mod_eq_of_lt (Nat.one_lt_two_pow hw.ne')]) using 1
    simp [loaded, contents, Nat.mod_eq_of_lt (Nat.one_lt_two_pow hw.ne')]
  simpa [load] using Caliper.Exec.seq first
    (Caliper.Exec.seq (Caliper.Exec.imm (C := cost) (tape := tape) (s := before.setReg 1 left) (d := 2) (v := 1)) second)

theorem finish_exec (cost : CostModel) (tape : RandomTape w) (left right : Word w)
    (before : State w) (zero : before.regs 0 = 0) (contents : before.bufs 0 = #[left, right]) :
    ∃ after, Caliper.Exec cost tape finish before after (cost.memStore + cost.memPop) 0 0 ∧
      after.bufs 0 = #[before.regs 1] ∧ after.regs 0 = before.regs 0 ∧ after.caps = before.caps := by
  let stored := before.setBuf 0 #[before.regs 1, right]
  let after := stored.setBuf 0 #[before.regs 1]
  have write : Caliper.Exec cost tape (.memStore 0 0 1) before stored cost.memStore 0 0 := by
    convert Caliper.Exec.memStore (C := cost) (tape := tape) (s := before) (b := 0) (i := 0) (src := 1)
      (by simp [zero, contents]) using 1
    simp [stored, zero, contents]
  have pop : Caliper.Exec cost tape (.memPop 0) stored after cost.memPop 0 0 := by
    convert Caliper.Exec.memPop (C := cost) (tape := tape) (s := stored) (b := 0) using 1
    simp [stored, after]
  exact ⟨after, by simpa [finish] using Caliper.Exec.seq write pop, rfl, rfl, rfl⟩

theorem descriptionFits (op : BinOp) (hw : 16 < 2 ^ w) : DescriptionFits (code (w := w) op) := by
  have closed : ∀ operation, ∀ token ∈ description (.bin operation 1 1 2 : Stmt 0), token ≤ 14 := by
    intro operation; cases operation <;> decide
  have tags : ∀ token ∈ description (.bin op 1 1 2 : Stmt w), token ≤ 14 := closed op
  have constant := (1 : Word w).isLt
  have positive := (width_pos hw).ne'
  simp [description] at tags
  simp [code, load, finish, DescriptionFits, description, positive]
  omega

theorem descriptionWords_eq (op : BinOp) : descriptionWords (code (w := w) op) = 27 := rfl

theorem exec (cost : CostModel) (tape : RandomTape w) (op : BinOp) (left right : Word w)
    (before : State w) (zero : before.regs 0 = 0) (contents : before.bufs 0 = #[left, right])
    (hw : 0 < w) :
    ∃ after, Caliper.Exec cost tape (code op) before after
      (cost.memLoad + (cost.imm + cost.memLoad) + (cost.bin op + (cost.memStore + cost.memPop))) 0 0 ∧
      after.bufs 0 = #[op.eval left right] ∧ after.regs 0 = before.regs 0 ∧ after.caps = before.caps := by
  have read := load_exec cost tape left right before zero contents hw
  let computed := (loaded before left right).setReg 1 (op.eval left right)
  have operation : Caliper.Exec cost tape (.bin op 1 1 2) (loaded before left right) computed (cost.bin op) 0 0 := by
    convert Caliper.Exec.bin (C := cost) (tape := tape) (s := loaded before left right) (op := op) (d := 1) (a := 1) (b := 2) using 1
    simp [computed, loaded]
  obtain ⟨after, written, result, offset, caps⟩ := finish_exec cost tape left right computed
    (by simpa [computed, loaded] using zero) (by simpa [computed, loaded] using contents)
  exact ⟨after, by simpa [code] using Caliper.Exec.seq read (Caliper.Exec.seq operation written),
    by simpa [computed] using result, by simpa [computed, loaded] using offset, caps⟩

def pair (w : Nat) (hw : 16 < 2 ^ w) : Representation w (Word w × Word w) :=
  (wordRepresentation w (width_pos hw)).prod (wordRepresentation w (width_pos hw)) (by
    change 1 + 1 < 2 ^ w
    omega)

def realizer (cost : CostModel) (op : BinOp) (hw : 16 < 2 ^ w) :
    Realizer cost (pair w hw) (wordRepresentation w (width_pos hw)) (fun value => op.eval value.1 value.2) where
  code := code op
  positive_width := width_pos hw
  description_fits := descriptionFits op hw
  random_free := by trivial
  time _ := cost.memLoad + (cost.imm + cost.memLoad) + (cost.bin op + (cost.memStore + cost.memPop))
  net _ := 0
  workspace _ := 0
  correct tape value before represented := by
    have contents : before.bufs 0 = #[value.1, value.2] := by
      have array := congrArg List.toArray represented.2.1
      simpa [pair, wordRepresentation, wordEncoding, Representation.prod, Encoding.prod, Encoding.checked] using array
    obtain ⟨after, execution, result, zero, caps⟩ := exec cost tape op value.1 value.2 before represented.1 contents (width_pos hw)
    exact ⟨after, 0, 0, execution,
      ⟨zero.trans represented.1, by simp [result, wordRepresentation, wordEncoding],
        execution.wellFormed_preserved represented.2.2.1, by intro buffer; rw [caps]; exact represented.2.2.2 buffer⟩,
      le_rfl, le_rfl⟩

end Signatures.Runtime.CaliperBackend.WordBinary
