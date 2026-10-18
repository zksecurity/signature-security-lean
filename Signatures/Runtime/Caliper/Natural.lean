import Signatures.Runtime.Caliper.Boolean
import Signatures.Runtime.Caliper.Saturating
import Signatures.Runtime.Caliper.SourceLists

/-! Implementations of source natural-number operations on bounded domains.
The source values remain `Nat`. Addition proves that its result cannot wrap;
subtraction executes a saturating branch, and comparisons inspect actual words. -/

namespace Signatures.Runtime.CaliperBackend.BoundedSource.Natural

open Caliper

variable {w : Nat} {A : Type}

def pair (left right : Nat) (hw : 16 < 2 ^ w) (leftFits : left ≤ 2 ^ w) (rightFits : right ≤ 2 ^ w) : Layout w (Nat × Nat) :=
  (Layout.counter w left (width_pos hw) leftFits).prod (Layout.counter w right (width_pos hw) rightFits) (by
    change 1 + 1 < 2 ^ w
    omega)

def words (value : Nat × Nat) : Word w × Word w := (BitVec.ofNat w value.1, BitVec.ofNat w value.2)

def binary (cost : CostModel) (op : BinOp) (left right : Nat) (hw : 16 < 2 ^ w)
    (leftFits : left ≤ 2 ^ w) (rightFits : right ≤ 2 ^ w) :
    Realizer cost (pair left right hw leftFits rightFits).representation (wordRepresentation w (width_pos hw))
      (fun value => op.eval (words value.val).1 (words value.val).2) :=
  (WordBinary.realizer cost op hw).viewInput _ (fun value : (pair left right hw leftFits rightFits).Value => words value.val) (fun _ => rfl)

def constant (cost : CostModel) (allocation : 1 ≤ cost.allocPerWord) (input : Layout w A)
    (bound value : Nat) (hw : 16 < 2 ^ w) (boundFits : bound ≤ 2 ^ w) (valid : value < bound) :
    Implementation cost input (Layout.counter w bound (width_pos hw) boundFits) (fun _ => value) where
  preserves _ _ := valid
  program := Assembly.realizer cost allocation input.representation _ _ [.literal (BitVec.ofNat w value)] hw rfl
    (by intro operand member; simp only [List.mem_singleton] at member; subst operand; trivial)
    (by intro source state represented operand member; simp only [List.mem_singleton] at member; subst operand; trivial)
    (fun _ _ _ => rfl)

def add (cost : CostModel) (left right : Nat) (hw : 16 < 2 ^ w) (sumFits : left + right ≤ 2 ^ w) :
    Implementation cost (pair left right hw (by omega) (by omega))
      (Layout.counter w (left + right) (width_pos hw) sumFits) (fun value => value.1 + value.2) where
  preserves value valid := Nat.add_lt_add valid.1 valid.2
  program := (binary cost .add left right hw (by omega) (by omega)).viewOutput _ _ (by
    intro value
    change [BitVec.ofNat w (value.val.1 + value.val.2)] = [BitVec.ofNat w value.val.1 + BitVec.ofNat w value.val.2]
    rw [BitVec.ofNat_add])

theorem subtract_words (left right : Nat) (leftFits : left < 2 ^ w) (rightFits : right < 2 ^ w) :
    Saturating.subtract (words (w := w) (left, right)) = BitVec.ofNat w (left - right) := by
  simp only [Saturating.subtract, words, BitVec.toNat_ofNat, Nat.mod_eq_of_lt leftFits, Nat.mod_eq_of_lt rightFits]
  split_ifs with underflow
  · rw [Nat.sub_eq_zero_of_le underflow.le]
    rfl
  · exact BitVec.ofNat_sub_ofNat_of_le left right rightFits (Nat.le_of_not_gt underflow)

def subtract (cost : CostModel) (left right : Nat) (hw : 16 < 2 ^ w)
    (leftFits : left ≤ 2 ^ w) (rightFits : right ≤ 2 ^ w) :
    Implementation cost (pair left right hw leftFits rightFits)
      (Layout.counter w left (width_pos hw) leftFits) (fun value => value.1 - value.2) where
  preserves value valid := (Nat.sub_le value.1 value.2).trans_lt valid.1
  program := ((Saturating.realizer cost hw).viewInput (pair left right hw leftFits rightFits).representation
    (fun value => words value.val) (fun _ => rfl)).viewOutput _ _ (by
      intro value
      change [BitVec.ofNat w (value.val.1 - value.val.2)] = [Saturating.subtract (words value.val)]
      rw [subtract_words _ _ (value.property.1.trans_le leftFits) (value.property.2.trans_le rightFits)])

theorem words_equal (left right : Nat) (leftFits : left < 2 ^ w) (rightFits : right < 2 ^ w) :
    (BitVec.ofNat w left = BitVec.ofNat w right) ↔ left = right := by
  constructor
  · intro equal
    have natural := congrArg BitVec.toNat equal
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt leftFits, Nat.mod_eq_of_lt rightFits] using natural
  · intro equal; rw [equal]

def equal (cost : CostModel) (left right : Nat) (hw : 16 < 2 ^ w)
    (leftFits : left ≤ 2 ^ w) (rightFits : right ≤ 2 ^ w) :
    Implementation cost (pair left right hw leftFits rightFits)
      (Layout.all (Representation.boolean w (width_pos hw))) (fun value => decide (value.1 = value.2)) where
  preserves _ _ := trivial
  program := (binary cost .eq left right hw leftFits rightFits).viewOutput _ _ (by
    intro value
    change [if decide (value.val.1 = value.val.2) then 1 else 0] =
      [BinOp.eq.eval (BitVec.ofNat w value.val.1) (BitVec.ofNat w value.val.2)]
    simp [BinOp.eval, words_equal _ _ (value.property.1.trans_le leftFits) (value.property.2.trans_le rightFits)])

def less (cost : CostModel) (left right : Nat) (hw : 16 < 2 ^ w)
    (leftFits : left ≤ 2 ^ w) (rightFits : right ≤ 2 ^ w) :
    Implementation cost (pair left right hw leftFits rightFits)
      (Layout.all (Representation.boolean w (width_pos hw))) (fun value => decide (value.1 < value.2)) where
  preserves _ _ := trivial
  program := (binary cost .ult left right hw leftFits rightFits).viewOutput _ _ (by
    intro value
    change [if decide (value.val.1 < value.val.2) then 1 else 0] =
      [BinOp.ult.eval (BitVec.ofNat w value.val.1) (BitVec.ofNat w value.val.2)]
    simp [BinOp.eval, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (value.property.1.trans_le leftFits),
      Nat.mod_eq_of_lt (value.property.2.trans_le rightFits)])

end Signatures.Runtime.CaliperBackend.BoundedSource.Natural
