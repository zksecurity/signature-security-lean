import Proofs.Runtime.Caliper.CapacityBounds

/-! Executed counter operations for input-counted iteration. A frame stores its
payload followed by one counter word. Loading and decrementing that word use
ordinary Caliper instructions; no host counter controls the running program.
-/

namespace Signatures.Runtime.CaliperBackend.Counter

open Caliper

variable {w : Nat}

def load (payloadWords : Nat) : Stmt w :=
  .imm 1 (BitVec.ofNat w payloadWords) ;; .memLoad 2 0 1

def decrement : Stmt w :=
  .imm 3 1 ;; .bin .sub 2 2 3 ;; .memPop 0 ;; .memPush 0 2

theorem load_straight (payloadWords : Nat) : (load (w := w) payloadWords).Straight := ⟨trivial, trivial⟩
theorem decrement_straight : (decrement (w := w)).Straight := ⟨trivial, trivial, trivial, trivial⟩

theorem load_descriptionFits (payloadWords : Nat) (hw : 16 < 2 ^ w) : DescriptionFits (load (w := w) payloadWords) := by
  have positive := (width_pos hw).ne'
  have word := (BitVec.ofNat w payloadWords).isLt
  simp [load, DescriptionFits, description, positive]
  omega

theorem decrement_descriptionFits (hw : 16 < 2 ^ w) : DescriptionFits (decrement (w := w)) := by
  have word := (1 : Word w).isLt
  change ∀ token ∈ [1, 2, 3, (1 : Word w).toNat, 1, 6, 1, 2, 2, 3, 1, 14, 0, 13, 0, 2], token < 2 ^ w
  intro token member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | exact word | exact lt_of_le_of_lt (by decide) hw

theorem load_exec (cost : CostModel) (tape : RandomTape w) (payload : Array (Word w)) (counter : Word w)
    (before : State w) (contents : before.bufs 0 = payload.push counter) (width : payload.size < 2 ^ w) :
    Caliper.Exec cost tape (load payload.size) before
      ((before.setReg 1 (BitVec.ofNat w payload.size)).setReg 2 counter)
      (cost.imm + cost.memLoad) 0 0 := by
  have read : Caliper.Exec cost tape (.memLoad 2 0 1) (before.setReg 1 (BitVec.ofNat w payload.size))
      ((before.setReg 1 (BitVec.ofNat w payload.size)).setReg 2 counter) cost.memLoad 0 0 := by
    convert Caliper.Exec.memLoad (C := cost) (tape := tape)
      (s := before.setReg 1 (BitVec.ofNat w payload.size)) (d := 2) (b := 0) (i := 1)
      (by simp [contents, BitVec.toNat_ofNat, Nat.mod_eq_of_lt width]) using 1
    simp [contents, BitVec.toNat_ofNat, Nat.mod_eq_of_lt width]
  simpa [load] using Caliper.Exec.seq (Caliper.Exec.imm (C := cost) (tape := tape)
    (s := before) (d := 1) (v := BitVec.ofNat w payload.size)) read

theorem decrement_exec (cost : CostModel) (tape : RandomTape w) (payload : Array (Word w)) (count : Nat)
    (before : State w) (contents : before.bufs 0 = payload.push (BitVec.ofNat w (count + 1)))
    (loaded : before.regs 2 = BitVec.ofNat w (count + 1)) (wellFormed : before.WellFormed) :
    ∃ after, Caliper.Exec cost tape decrement before after
      (cost.imm + (cost.bin .sub + (cost.memPop + cost.memPush))) 0 0 ∧
      after.bufs 0 = payload.push (BitVec.ofNat w count) ∧ after.regs 0 = before.regs 0 ∧ after.caps = before.caps := by
  have difference : BitVec.ofNat w (count + 1) - (1 : Word w) = BitVec.ofNat w count := by
    simp [BitVec.ofNat_add, BitVec.add_sub_cancel]
  let constant := before.setReg 3 1
  let reduced := constant.setReg 2 (BitVec.ofNat w count)
  let popped := reduced.setBuf 0 ((reduced.bufs 0).pop)
  let after := popped.setBuf 0 ((popped.bufs 0).push (popped.regs 2))
  have subtract : Caliper.Exec cost tape (.bin .sub 2 2 3) constant reduced (cost.bin .sub) 0 0 := by
    have value : BinOp.sub.eval (constant.regs 2) (constant.regs 3) = BitVec.ofNat w count := by
      change before.regs 2 - (1 : Word w) = BitVec.ofNat w count
      rw [loaded]
      exact difference
    change Caliper.Exec cost tape (.bin .sub 2 2 3) constant (constant.setReg 2 (BitVec.ofNat w count)) (cost.bin .sub) 0 0
    rw [← value]
    exact .bin
  have room : (popped.bufs 0).size < popped.caps 0 := by
    have enough := wellFormed.size_le_cap 0
    simp only [contents, Array.size_push] at enough
    simpa [popped, reduced, constant, contents] using (show payload.size < before.caps 0 by omega)
  have push : Caliper.Exec cost tape (.memPush 0 2) popped after cost.memPush 0 0 := .memPush room
  have execution := Caliper.Exec.seq (Caliper.Exec.imm (C := cost) (tape := tape) (s := before) (d := 3) (v := 1))
    (Caliper.Exec.seq subtract (Caliper.Exec.seq (Caliper.Exec.memPop (C := cost) (tape := tape) (b := 0) (s := reduced)) push))
  refine ⟨after, by simpa [decrement] using execution, ?_, ?_, rfl⟩
  · simp [after, popped, reduced, constant, contents]
  · simp [after, popped, reduced, constant]

end Signatures.Runtime.CaliperBackend.Counter
