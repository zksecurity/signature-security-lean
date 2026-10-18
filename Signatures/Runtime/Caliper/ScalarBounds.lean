import Signatures.Runtime.Caliper.Finite
import Signatures.Runtime.Caliper.SourceData

/-! Exact unit-cost time and stored-code bounds for the executed source scalar
operations. These are uniform in the admitted inputs and word width. -/

namespace Signatures.Runtime.CaliperBackend

open Caliper

variable {w : Nat} {A : Type}

theorem WordBinary.time_unit (op : BinOp) (hw : 16 < 2 ^ w) (value : Word w × Word w) :
    (WordBinary.realizer .unit op hw).time value = 6 := rfl

theorem Boolean.constant_time_unit (input : Representation w A) (value : Bool)
    (hw : 16 < 2 ^ w) (source : A) :
    (Boolean.constant .unit (by decide) input value hw).time source = 7 := rfl

theorem Boolean.select_time_unit (payload : Representation w A) (hw : 16 < 2 ^ w)
    (fits : 1 + payload.encoding.words < 2 ^ w) (value : Bool × A) :
    (Boolean.selectRealizer .unit payload hw fits).time value = 5 := rfl

namespace BoundedSource

theorem Natural.add_time_unit (left right : Nat) (hw : 16 < 2 ^ w) (fits : left + right ≤ 2 ^ w)
    (value : (Natural.pair left right hw (by omega) (by omega)).Value) :
    (Natural.add .unit left right hw fits).program.time value = 6 := rfl

theorem Natural.subtract_time_unit (left right : Nat) (hw : 16 < 2 ^ w)
    (leftFits : left ≤ 2 ^ w) (rightFits : right ≤ 2 ^ w)
    (value : (Natural.pair left right hw leftFits rightFits).Value) :
    (Natural.subtract .unit left right hw leftFits rightFits).program.time value = 8 :=
  Saturating.time_unit _

theorem Natural.equal_time_unit (left right : Nat) (hw : 16 < 2 ^ w)
    (leftFits : left ≤ 2 ^ w) (rightFits : right ≤ 2 ^ w)
    (value : (Natural.pair left right hw leftFits rightFits).Value) :
    (Natural.equal .unit left right hw leftFits rightFits).program.time value = 6 := rfl

theorem Natural.less_time_unit (left right : Nat) (hw : 16 < 2 ^ w)
    (leftFits : left ≤ 2 ^ w) (rightFits : right ≤ 2 ^ w)
    (value : (Natural.pair left right hw leftFits rightFits).Value) :
    (Natural.less .unit left right hw leftFits rightFits).program.time value = 6 := rfl

theorem Finite.ofNat_time_unit (inputBound bound : Nat) (hw : 16 < 2 ^ w)
    (inputFits : inputBound ≤ 2 ^ w) (outputFits : bound + 1 ≤ 2 ^ w)
    (value : (Layout.counter w inputBound (width_pos hw) inputFits).Value) :
    (Finite.ofNat .unit (by decide) inputBound bound hw inputFits outputFits).program.time value =
      if bound + 1 = 2 ^ w then 0 else 21 := by
  by_cases entire : bound + 1 = 2 ^ w <;> simp only [Finite.ofNat, entire, ↓reduceDIte, ↓reduceIte] <;> rfl

theorem Finite.ofNat_descriptionWords (cost : CostModel) (allocation : 1 ≤ cost.allocPerWord)
    (inputBound bound : Nat) (hw : 16 < 2 ^ w) (inputFits : inputBound ≤ 2 ^ w)
    (outputFits : bound + 1 ≤ 2 ^ w) :
    descriptionWords (Finite.ofNat cost allocation inputBound bound hw inputFits outputFits).program.code =
      if bound + 1 = 2 ^ w then 1 else 89 := by
  by_cases entire : bound + 1 = 2 ^ w <;> simp only [Finite.ofNat, entire, ↓reduceDIte, ↓reduceIte] <;> rfl

end BoundedSource
end Signatures.Runtime.CaliperBackend
