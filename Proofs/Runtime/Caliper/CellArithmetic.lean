import Proofs.Runtime.Caliper.Assembly

/-! Arithmetic on an encoded data word. The index and arithmetic operand are
loaded by actual instructions; the operation preserves all capacities and the
remaining words. This is used for bounded list length headers. -/

namespace Signatures.Runtime.CaliperBackend.CellArithmetic

open Caliper

variable {w : Nat}

def code (offset : Nat) (op : BinOp) (operand : Word w) : Stmt w :=
  .imm 1 (BitVec.ofNat w offset) ;; .memLoad 2 0 1 ;;
  .imm 3 operand ;; .bin op 2 2 3 ;; .memStore 0 1 2

theorem straight (offset : Nat) (op : BinOp) (operand : Word w) :
    (code offset op operand).Straight := by trivial

theorem randomFree (offset : Nat) (op : BinOp) (operand : Word w) :
    (code offset op operand).RandomFree := by trivial

theorem descriptionWords_eq (offset : Nat) (op : BinOp) (operand : Word w) :
    descriptionWords (code offset op operand) = 23 := by rfl

theorem descriptionFits (offset : Nat) (op : BinOp) (operand : Word w)
    (hw : 16 < 2 ^ w) : DescriptionFits (code offset op operand) := by
  have hi := (BitVec.ofNat w offset).isLt
  have ho := operand.isLt
  have positive := (width_pos hw).ne'
  have closed : ∀ operation, ∀ token ∈ description (.bin operation 2 2 3 : Stmt 0), token ≤ 14 := by
    intro operation
    cases operation <;> decide
  have tagBound : ∀ token ∈ description (.bin op 2 2 3 : Stmt w), token ≤ 14 := closed op
  simp [description] at tagBound
  simp [code, DescriptionFits, description, positive]
  omega

theorem time_eq (cost : CostModel) (offset : Nat) (op : BinOp) (operand : Word w) :
    (code offset op operand).staticTime cost =
      cost.imm + (cost.memLoad + (cost.imm + (cost.bin op + cost.memStore))) := rfl

theorem exec (cost : CostModel) (tape : RandomTape w) (offset : Nat)
    (op : BinOp) (operand : Word w) (before : State w)
    (index : offset < (before.bufs 0).size) (fits : offset < 2 ^ w) :
    ∃ after, Caliper.Exec cost tape (code offset op operand) before after
      ((code offset op operand).staticTime cost) 0 0 ∧
      after.bufs 0 = (before.bufs 0).set offset (op.eval (before.bufs 0)[offset] operand) ∧
      after.regs 0 = before.regs 0 ∧ after.caps = before.caps := by
  have hi : (BitVec.ofNat w offset).toNat = offset := by
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits]
  let indexed := before.setReg 1 (BitVec.ofNat w offset)
  let loaded := indexed.setReg 2 (before.bufs 0)[offset]
  let constant := loaded.setReg 3 operand
  let computed := constant.setReg 2 (op.eval (before.bufs 0)[offset] operand)
  let after := computed.setBuf 0 ((before.bufs 0).set offset (op.eval (before.bufs 0)[offset] operand))
  have read : Caliper.Exec cost tape (.memLoad 2 0 1) indexed loaded cost.memLoad 0 0 := by
    convert Caliper.Exec.memLoad (C := cost) (tape := tape) (s := indexed) (d := 2) (b := 0) (i := 1)
      (by simpa [indexed, hi] using index) using 1
    simp [indexed, loaded, hi]
  have compute : Caliper.Exec cost tape (.bin op 2 2 3) constant computed (cost.bin op) 0 0 := by
    convert Caliper.Exec.bin (C := cost) (tape := tape) (s := constant) (op := op) (d := 2) (a := 2) (b := 3) using 1
    simp [computed, constant, loaded]
  have write : Caliper.Exec cost tape (.memStore 0 1 2) computed after cost.memStore 0 0 := by
    convert Caliper.Exec.memStore (C := cost) (tape := tape) (s := computed) (b := 0) (i := 1) (src := 2)
      (by simpa [computed, constant, loaded, indexed, hi] using index) using 1
    simp [after, computed, constant, loaded, indexed, hi]
  have execution := Caliper.Exec.seq (Caliper.Exec.imm (C := cost) (tape := tape) (s := before)
      (d := 1) (v := BitVec.ofNat w offset)) (Caliper.Exec.seq read
      (Caliper.Exec.seq (Caliper.Exec.imm (C := cost) (tape := tape) (s := loaded) (d := 3) (v := operand))
        (Caliper.Exec.seq compute write)))
  exact ⟨after, by simpa [code, Stmt.staticTime] using execution, rfl,
    by simp [after, computed, constant, loaded, indexed], rfl⟩

theorem exec_at (cost : CostModel) (tape : RandomTape w)
    (leading suffix : List (Word w)) (value operand : Word w) (op : BinOp)
    (before : State w) (contents : (before.bufs 0).toList = leading ++ value :: suffix)
    (fits : leading.length < 2 ^ w) :
    ∃ after, Caliper.Exec cost tape (code leading.length op operand) before after
      ((code leading.length op operand).staticTime cost) 0 0 ∧
      (after.bufs 0).toList = leading ++ op.eval value operand :: suffix ∧
      after.regs 0 = before.regs 0 ∧ after.caps = before.caps := by
  have size := congrArg List.length contents
  have index : leading.length < (before.bufs 0).size := by simp only [Array.length_toList, List.length_append, List.length_cons] at size; omega
  obtain ⟨after, execution, changed, zero, caps⟩ := exec cost tape leading.length op operand before index fits
  have stored : (before.bufs 0)[leading.length] = value := by
    have lookup := congrArg (fun bytes => bytes[leading.length]?) contents
    simpa [index] using lookup
  refine ⟨after, execution, ?_, zero, caps⟩
  rw [changed, Array.toList_set, stored, contents]
  simp

end Signatures.Runtime.CaliperBackend.CellArithmetic
