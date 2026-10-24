import Proofs.Runtime.Caliper.ImplementationBounds
import Proofs.Runtime.Caliper.CheckedComposition
import Proofs.Runtime.Caliper.SourceListData

/-! Uniform source-level budgets for projections, shared-input pairing and
list construction. Every bound follows from the executed copying routines. -/

namespace Signatures.Runtime.CaliperBackend.BoundedSource

open Caliper

variable {w : Nat} {A B D : Type}

theorem Implementation.first_boundedBy (left : Layout w A) (right : Layout w B) (hw : 16 < 2 ^ w)
    (fits : left.representation.encoding.words + right.representation.encoding.words < 2 ^ w) :
    (Implementation.first (cost := .unit) (by decide) left right hw fits).BoundedBy
      (8 * left.representation.encoding.words) (26 * left.representation.encoding.words + 14) := by
  constructor
  · intro value
    change (selectSlice (w := w) 0 left.representation.encoding.words).staticTime .unit ≤ _
    simp only [selectSlice_staticTime, sliceWordTime, CostModel.unit]
    omega
  · exact (selectSlice_descriptionWords 0 left.representation.encoding.words).le

theorem Implementation.second_boundedBy (left : Layout w A) (right : Layout w B) (hw : 16 < 2 ^ w)
    (fits : left.representation.encoding.words + right.representation.encoding.words < 2 ^ w) :
    (Implementation.second (cost := .unit) (by decide) left right hw fits).BoundedBy
      (8 * right.representation.encoding.words) (26 * right.representation.encoding.words + 14) := by
  constructor
  · intro value
    change (selectSlice (w := w) left.representation.encoding.words right.representation.encoding.words).staticTime .unit ≤ _
    simp only [selectSlice_staticTime, sliceWordTime, CostModel.unit]
    omega
  · exact (selectSlice_descriptionWords left.representation.encoding.words right.representation.encoding.words).le

theorem Implementation.checkedPair_boundedBy {input : Layout w A} {left : Layout w B} {right : Layout w D}
    {f : A → B} {g : A → D} (first : Implementation .unit input left f) (second : Implementation .unit input right g)
    (hw : 16 < 2 ^ w)
    (duplicateFits : input.representation.encoding.words + input.representation.encoding.words < 2 ^ w)
    (middleFits : left.representation.encoding.words + input.representation.encoding.words < 2 ^ w)
    (outputFits : left.representation.encoding.words + right.representation.encoding.words < 2 ^ w)
    (firstTime firstWords secondTime secondWords : Nat)
    (firstBound : first.BoundedBy firstTime firstWords) (secondBound : second.BoundedBy secondTime secondWords)
    (implementation : Implementation .unit input (left.prod right outputFits) (fun value => (f value, g value)))
    (compiled : first.checkedPair second (by decide) hw duplicateFits middleFits outputFits = some implementation) :
    implementation.BoundedBy
      (firstTime + secondTime + 52 * input.representation.encoding.words + 36 * left.representation.encoding.words +
        16 * right.representation.encoding.words)
      (firstWords + secondWords + 169 * input.representation.encoding.words + 117 * left.representation.encoding.words +
        52 * right.representation.encoding.words + 124) := by
  unfold Implementation.checkedPair at compiled
  split at compiled
  next firstFits =>
    split at compiled
    next secondFits =>
      cases Option.some.inj compiled
      constructor
      · intro value
        have bound := Pairing.time_unit_le first.program second.program hw firstFits secondFits
          duplicateFits middleFits outputFits value
        have h₁ := firstBound.time_le value
        have h₂ := secondBound.time_le value
        exact bound.trans (by omega)
      · have bound := Pairing.descriptionWords_le first.program second.program (by decide) hw firstFits secondFits
          duplicateFits middleFits outputFits
        have h₁ := firstBound.code_le
        have h₂ := secondBound.code_le
        exact bound.trans (by omega)
    next rejected => contradiction
  next rejected => contradiction

theorem ListData.cons_boundedBy (entry : Layout w A) (capacity : Nat) (hw : 16 < 2 ^ w)
    (countFits : capacity + 1 < 2 ^ w)
    (storageFits : 1 + (capacity + 1) * entry.representation.encoding.words < 2 ^ w) :
    (ListData.cons .unit (by decide) entry capacity hw countFits storageFits).BoundedBy
      (8 * (1 + (capacity + 1) * entry.representation.encoding.words) + 5)
      (26 * (1 + (capacity + 1) * entry.representation.encoding.words) + 38) :=
  ⟨fun _ => ListConstruct.consCode_time_unit_le _ _, ListConstruct.consCode_descriptionWords_le _ _⟩

end Signatures.Runtime.CaliperBackend.BoundedSource
