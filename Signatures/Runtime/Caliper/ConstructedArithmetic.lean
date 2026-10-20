import Signatures.Runtime.Caliper.Constructed

namespace Signatures.Runtime.CaliperBackend.BoundedSource.Constructed
open Caliper
variable {w : Nat}

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
