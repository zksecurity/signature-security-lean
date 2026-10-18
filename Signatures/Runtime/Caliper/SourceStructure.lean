import Signatures.Runtime.Caliper.Pairing

/-! Structural implementations on the original source types. Product formation
and projections execute copies; branches execute stored-tag dispatch. Capacity
witnesses remain mathematical invariants and are never stored in the machine. -/

namespace Signatures.Runtime.CaliperBackend.BoundedSource

open Caliper

variable {w : Nat} {A B D : Type} {cost : CostModel}

def Implementation.first (allocation : 1 ≤ cost.allocPerWord)
    (left : Layout w A) (right : Layout w B) (hw : 16 < 2 ^ w)
    (fits : left.representation.encoding.words + right.representation.encoding.words < 2 ^ w) :
    Implementation cost (left.prod right fits) left Prod.fst where
  preserves _ valid := valid.1
  program := (firstRealizer cost allocation left.representation right.representation hw fits).viewInput _
    (productView left right) (fun _ => rfl)

def Implementation.second (allocation : 1 ≤ cost.allocPerWord)
    (left : Layout w A) (right : Layout w B) (hw : 16 < 2 ^ w)
    (fits : left.representation.encoding.words + right.representation.encoding.words < 2 ^ w) :
    Implementation cost (left.prod right fits) right Prod.snd where
  preserves _ valid := valid.2
  program := (secondRealizer cost allocation left.representation right.representation hw fits).viewInput _
    (productView left right) (fun _ => rfl)

def Implementation.pair {input : Layout w A} {left : Layout w B} {right : Layout w D}
    {f : A → B} {g : A → D} (first : Implementation cost input left f) (second : Implementation cost input right g)
    (allocation : 1 ≤ cost.allocPerWord) (hw : 16 < 2 ^ w)
    (firstNameFits : first.program.savedBuffer < 2 ^ w) (secondNameFits : second.program.savedBuffer < 2 ^ w)
    (duplicateFits : input.representation.encoding.words + input.representation.encoding.words < 2 ^ w)
    (middleFits : left.representation.encoding.words + input.representation.encoding.words < 2 ^ w)
    (outputFits : left.representation.encoding.words + right.representation.encoding.words < 2 ^ w) :
    Implementation cost input (left.prod right outputFits) (fun value => (f value, g value)) where
  preserves value valid := ⟨first.preserves value valid, second.preserves value valid⟩
  program := (Pairing.realizer first.program second.program allocation hw firstNameFits secondNameFits
    duplicateFits middleFits outputFits).viewOutput _ _ (fun _ => rfl)

def Implementation.branch {left : Layout w A} {right : Layout w B} {output : Layout w D}
    {f : A → D} {g : B → D} (first : Implementation cost left output f) (second : Implementation cost right output g)
    (allocation : 1 ≤ cost.allocPerWord) (hw : 16 < 2 ^ w)
    (fits : 1 + max left.representation.encoding.words right.representation.encoding.words < 2 ^ w) :
    Implementation cost (left.sum right (width_pos hw) fits) output (Sum.elim f g) where
  preserves value valid := by
    cases value with
    | inl value => exact first.preserves value valid
    | inr value => exact second.preserves value valid
  program := ((branchRealizer cost allocation left.representation right.representation output.representation
    first.program second.program hw fits).viewInput _ (sumView left right) (fun _ => rfl)).viewOutput _ _ (by
      rintro ⟨value, valid⟩
      cases value <;> rfl)

end Signatures.Runtime.CaliperBackend.BoundedSource
