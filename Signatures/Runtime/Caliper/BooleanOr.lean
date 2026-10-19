import Signatures.Runtime.Caliper.Boolean
import Signatures.Runtime.Caliper.EncodedEquality

/-! Boolean disjunction executes the existing two-word bitwise instruction.
The input/output views use only the canonical zero/one Boolean encodings. -/
namespace Signatures.Runtime.CaliperBackend.Boolean
open Caliper
variable {w : Nat} (hw : 16 < 2 ^ w)

def pair : Representation w (Bool × Bool) :=
  (Representation.boolean w (width_pos hw)).prod (Representation.boolean w (width_pos hw))
    (by change 1 + 1 < 2 ^ w; omega)

def or : Realizer .unit (pair hw) (Representation.boolean w (width_pos hw))
    (fun value => value.1 || value.2) :=
  ((WordBinary.realizer .unit .or hw).viewInput (pair hw)
    (fun value => (if value.1 then 1 else 0, if value.2 then 1 else 0)) (fun _ => rfl)).viewOutput
      (Representation.boolean w (width_pos hw)) (fun value => value.1 || value.2) (by
        rintro ⟨lhs, rhs⟩
        cases lhs <;> cases rhs <;>
          simp [Representation.boolean, Encoding.boolean, Encoding.checked,
            wordRepresentation, wordEncoding, BinOp.eval])

theorem or_time (value : Bool × Bool) : (or hw).time value = 6 := rfl
theorem or_words : descriptionWords (or hw).code = 27 := rfl
theorem or_names : NamesBound (or hw).code 3 :=
  ⟨by change 3 ≤ 3; omega, by change 1 ≤ 3; omega⟩

end Signatures.Runtime.CaliperBackend.Boolean
