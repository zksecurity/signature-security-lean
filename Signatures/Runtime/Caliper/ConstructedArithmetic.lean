import Signatures.Runtime.Caliper.Constructed

namespace Signatures.Runtime.CaliperBackend.BoundedSource.Constructed
open Caliper
variable {w : Nat}

/-- Natural addition with an explicit no-wrap bound. -/
def add (left right : Nat) (hw : 16 < 2 ^ w) (fits : left + right ≤ 2 ^ w) :
    Constructed (Natural.pair left right hw (by omega) (by omega))
      (Layout.counter w (left + right) (width_pos hw) fits) (fun value => value.1 + value.2) where
  implementation := Natural.add .unit left right hw fits
  budget := ⟨6, 27⟩
  bounded := ⟨fun _ => le_rfl, (WordBinary.descriptionWords_eq .add).le⟩
  buffers := 1
  buffers_le := le_rfl
  names slots := ⟨by change 3 ≤ slots + 27; omega, by change 1 ≤ slots + 27; omega⟩

/-- Word remainder implements natural remainder, including a zero divisor. -/
def modulo (left right : Nat) (hw : 16 < 2 ^ w) (leftFits : left ≤ 2 ^ w) (rightFits : right ≤ 2 ^ w) :
    Constructed (Natural.pair left right hw leftFits rightFits)
      (Layout.counter w left (width_pos hw) leftFits) (fun value => value.1 % value.2) where
  implementation :=
    { preserves := fun value valid => (Nat.mod_le value.1 value.2).trans_lt valid.1
      program := (Natural.binary .unit .umod left right hw leftFits rightFits).viewOutput _ _ (by
        intro value
        have dividend : value.val.1 < 2 ^ w := value.property.1.trans_le leftFits
        have divisor : value.val.2 < 2 ^ w := value.property.2.trans_le rightFits
        have result : value.val.1 % value.val.2 < 2 ^ w := (Nat.mod_le _ _).trans_lt dividend
        change [BitVec.ofNat w (value.val.1 % value.val.2)] =
          [BitVec.ofNat w value.val.1 % BitVec.ofNat w value.val.2]
        congr 1
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_ofNat, BitVec.toNat_umod, Nat.mod_eq_of_lt dividend,
          Nat.mod_eq_of_lt divisor, Nat.mod_eq_of_lt result]) }
  budget := ⟨6, 27⟩
  bounded := ⟨fun _ => le_rfl, (WordBinary.descriptionWords_eq .umod).le⟩
  buffers := 1
  buffers_le := le_rfl
  names slots := ⟨by change 3 ≤ slots + 27; omega, by change 1 ≤ slots + 27; omega⟩

/-- Saturating natural subtraction uses the existing comparison and branch. -/
def subtract (left right : Nat) (hw : 16 < 2 ^ w) (leftFits : left ≤ 2 ^ w) (rightFits : right ≤ 2 ^ w) :
    Constructed (Natural.pair left right hw leftFits rightFits)
      (Layout.counter w left (width_pos hw) leftFits) (fun value => value.1 - value.2) where
  implementation := Natural.subtract .unit left right hw leftFits rightFits
  budget := ⟨8, 38⟩
  bounded :=
    ⟨fun value => by
      change Saturating.time .unit (Natural.words value.val) ≤ 8
      rw [Saturating.time_unit],
      Saturating.descriptionWords_eq.le⟩
  buffers := 1
  buffers_le := le_rfl
  names slots := ⟨by change 4 ≤ slots + 38; omega, by change 1 ≤ slots + 38; omega⟩

end Signatures.Runtime.CaliperBackend.BoundedSource.Constructed
