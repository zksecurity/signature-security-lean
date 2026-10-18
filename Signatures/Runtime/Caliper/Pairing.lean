import Signatures.Runtime.Caliper.Reorder
import Signatures.Runtime.Caliper.SourceData
import Signatures.Runtime.Caliper.Retain

/-! Pair two executed local computations while preserving their common input.
The duplicate, saved state and permutations all execute charged copies. -/

namespace Signatures.Runtime.CaliperBackend.Pairing

open Caliper

variable {w : Nat} {A B D : Type}

def unitRepresentation (w : Nat) : Representation w Unit :=
  ⟨Encoding.unit w, by change 0 < 2 ^ w; positivity⟩

def swap (cost : CostModel) (allocation : 1 ≤ cost.allocPerWord)
    (left : Representation w A) (right : Representation w B) (hw : 16 < 2 ^ w)
    (fits : left.encoding.words + right.encoding.words < 2 ^ w) :
    Realizer cost (left.prod right fits) (right.prod left (by omega)) Prod.swap :=
  ((Reorder.realizer cost allocation left right (unitRepresentation w) hw (by simpa [unitRepresentation, Encoding.unit, Encoding.checked] using fits)).viewInput
    (left.prod right fits) (fun value => (value.1, (value.2, ()))) (by
      intro value
      simp [Representation.prod, Encoding.prod, Encoding.checked, unitRepresentation, Encoding.unit])).viewOutput
        (right.prod left (by omega)) Prod.swap (by
          intro value
          simp [Representation.prod, Encoding.prod, Encoding.checked, unitRepresentation, Encoding.unit])

def realizer {cost : CostModel} {input : Representation w A} {left : Representation w B}
    {right : Representation w D} {f : A → B} {g : A → D}
    (first : Realizer cost input left f) (second : Realizer cost input right g)
    (allocation : 1 ≤ cost.allocPerWord) (hw : 16 < 2 ^ w)
    (firstNameFits : first.savedBuffer < 2 ^ w) (secondNameFits : second.savedBuffer < 2 ^ w)
    (duplicateFits : input.encoding.words + input.encoding.words < 2 ^ w)
    (middleFits : left.encoding.words + input.encoding.words < 2 ^ w)
    (outputFits : left.encoding.words + right.encoding.words < 2 ^ w) :
    Realizer cost input (left.prod right outputFits) (fun value => (f value, g value)) :=
  ((((duplicateRealizer cost allocation input hw duplicateFits).then
    (first.retain allocation input hw firstNameFits duplicateFits middleFits)).then
      (swap cost allocation left input hw middleFits)).then
        (second.retain allocation left hw secondNameFits (by omega) (by omega))).then
          (swap cost allocation right left hw (by omega))

theorem swap_time_unit_le (left : Representation w A) (right : Representation w B)
    (hw : 16 < 2 ^ w) (fits : left.encoding.words + right.encoding.words < 2 ^ w) (value : A × B) :
    (swap .unit (by decide) left right hw fits).time value ≤
      8 * (left.encoding.words + right.encoding.words) := by
  exact Reorder.time_unit_le _ _ 0

theorem swap_descriptionWords_le (cost : CostModel) (allocation : 1 ≤ cost.allocPerWord)
    (left : Representation w A) (right : Representation w B)
    (hw : 16 < 2 ^ w) (fits : left.encoding.words + right.encoding.words < 2 ^ w) :
    descriptionWords (swap cost allocation left right hw fits).code ≤
      26 * (left.encoding.words + right.encoding.words) + 14 := by
  exact Reorder.descriptionWords_le _ _ 0

variable {input : Representation w A} {left : Representation w B} {right : Representation w D}
    {f : A → B} {g : A → D}

theorem time_unit_le (first : Realizer .unit input left f) (second : Realizer .unit input right g)
    (hw : 16 < 2 ^ w) (firstNameFits : first.savedBuffer < 2 ^ w) (secondNameFits : second.savedBuffer < 2 ^ w)
    (duplicateFits : input.encoding.words + input.encoding.words < 2 ^ w)
    (middleFits : left.encoding.words + input.encoding.words < 2 ^ w)
    (outputFits : left.encoding.words + right.encoding.words < 2 ^ w) (value : A) :
    (realizer first second (by decide) hw firstNameFits secondNameFits duplicateFits middleFits outputFits).time value ≤
      first.time value + second.time value + 52 * input.encoding.words + 36 * left.encoding.words + 16 * right.encoding.words := by
  have duplicate := Assembly.code_time_unit_le (Assembly.reads (w := w) 0 0 input.encoding.words ++ Assembly.reads 0 0 input.encoding.words)
  simp only [List.length_append, Assembly.reads_length] at duplicate
  change (duplicateRealizer .unit (by decide) input hw duplicateFits).time value ≤
    8 * (input.encoding.words + input.encoding.words) at duplicate
  have one := first.retain_time_unit_le input hw firstNameFits duplicateFits middleFits (value, value)
  have two := swap_time_unit_le left input hw middleFits (f value, value)
  have three := second.retain_time_unit_le left hw secondNameFits (by omega) (by omega) (value, f value)
  have four := swap_time_unit_le right left hw (by omega) (g value, f value)
  change _ + _ + _ + _ + _ ≤ _
  dsimp only [Realizer.then, Function.comp_apply, Prod.swap] at *
  omega

theorem descriptionWords_le {cost : CostModel}
    (first : Realizer cost input left f) (second : Realizer cost input right g)
    (allocation : 1 ≤ cost.allocPerWord) (hw : 16 < 2 ^ w)
    (firstNameFits : first.savedBuffer < 2 ^ w) (secondNameFits : second.savedBuffer < 2 ^ w)
    (duplicateFits : input.encoding.words + input.encoding.words < 2 ^ w)
    (middleFits : left.encoding.words + input.encoding.words < 2 ^ w)
    (outputFits : left.encoding.words + right.encoding.words < 2 ^ w) :
    descriptionWords (realizer first second allocation hw firstNameFits secondNameFits duplicateFits middleFits outputFits).code ≤
      descriptionWords first.code + descriptionWords second.code + 169 * input.encoding.words +
        117 * left.encoding.words + 52 * right.encoding.words + 124 := by
  have duplicate := Assembly.code_descriptionWords_le (Assembly.reads (w := w) 0 0 input.encoding.words ++ Assembly.reads 0 0 input.encoding.words)
  simp only [List.length_append, Assembly.reads_length] at duplicate
  change descriptionWords (duplicateRealizer cost allocation input hw duplicateFits).code ≤
    26 * (input.encoding.words + input.encoding.words) + 14 at duplicate
  have one := first.retain_descriptionWords_le allocation input hw firstNameFits duplicateFits middleFits
  have two := swap_descriptionWords_le cost allocation left input hw middleFits
  have three := second.retain_descriptionWords_le allocation left hw secondNameFits (by omega) (by omega)
  have four := swap_descriptionWords_le cost allocation right left hw (by omega)
  simp only [realizer, Realizer.then, descriptionWords_seq]
  omega

end Signatures.Runtime.CaliperBackend.Pairing
