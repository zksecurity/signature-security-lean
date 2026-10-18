import Signatures.Runtime.Caliper.WordBinary
import Signatures.Runtime.Caliper.BoundedSource

/-! Canonical Boolean words and executed source conditional selection. A stored
true bit selects the left alternative, so selection executes a zero test on the
header to obtain the existing tagged-union convention. -/

namespace Signatures.Runtime.CaliperBackend

open Caliper

variable {w : Nat} {A : Type}

def Encoding.boolean (w : Nat) (hw : 0 < w) : Encoding w Bool :=
  .checked 1 (fun value => [if value then 1 else 0])
    (fun bytes => match bytes with
      | [value] => if value = 0 then some false else if value = 1 then some true else none
      | _ => none)
    (fun _ => rfl) (by intro value; cases value <;> simp [hw.ne'])

def Representation.boolean (w : Nat) (hw : 0 < w) : Representation w Bool :=
  ⟨Encoding.boolean w hw, Nat.one_lt_two_pow hw.ne'⟩

namespace Boolean

def constant (cost : CostModel) (allocation : 1 ≤ cost.allocPerWord) (input : Representation w A)
    (value : Bool) (hw : 16 < 2 ^ w) :
    Realizer cost input (Representation.boolean w (width_pos hw)) (fun _ => value) :=
  Assembly.realizer cost allocation input _ _ [.literal (if value then 1 else 0)] hw rfl
    (by intro operand member; simp only [List.mem_singleton] at member; subst operand; trivial)
    (by intro source state represented operand member; simp only [List.mem_singleton] at member; subst operand; trivial)
    (fun _ _ _ => rfl)

def select (value : Bool × A) : A ⊕ A := if value.1 then .inl value.2 else .inr value.2

theorem select_bytes (payload : Representation w A) (hw : 16 < 2 ^ w)
    (fits : 1 + payload.encoding.words < 2 ^ w) (value : Bool × A) :
    (payload.sum payload (width_pos hw) (by simpa using fits)).encoding.encode (select value) =
      (if value.1 then 0 else 1) :: payload.encoding.encode value.2 := by
  rcases value with ⟨condition, value⟩
  cases condition <;>
    change _ :: (payload.encoding.encode value ++ List.replicate (max payload.encoding.words payload.encoding.words - payload.encoding.words) 0) = _
  all_goals simp

def selectRealizer (cost : CostModel) (payload : Representation w A) (hw : 16 < 2 ^ w)
    (fits : 1 + payload.encoding.words < 2 ^ w) :
    Realizer cost ((Representation.boolean w (width_pos hw)).prod payload fits)
      (payload.sum payload (width_pos hw) (by simpa using fits)) select where
  code := CellArithmetic.code 0 .eq 0
  positive_width := width_pos hw
  description_fits := CellArithmetic.descriptionFits _ _ _ hw
  random_free := CellArithmetic.randomFree _ _ _
  time _ := (CellArithmetic.code (w := w) 0 .eq 0).staticTime cost
  net _ := 0
  workspace _ := 0
  correct tape value before represented := by
    have contents : (before.bufs 0).toList = (if value.1 then 1 else 0) :: payload.encoding.encode value.2 := represented.2.1
    obtain ⟨after, execution, result, zero, caps⟩ := CellArithmetic.exec_at cost tape []
      (payload.encoding.encode value.2) (if value.1 then 1 else 0) 0 .eq before contents (by simp)
    refine ⟨after, 0, 0, execution, ⟨zero.trans represented.1, ?_,
      execution.wellFormed_preserved represented.2.2.1, ?_⟩, le_rfl, le_rfl⟩
    · rw [select_bytes payload hw fits value]
      cases condition : value.1 <;> simpa [BinOp.eval, condition, (width_pos hw).ne'] using result
    · intro buffer; rw [caps]; exact represented.2.2.2 buffer

end Boolean
end Signatures.Runtime.CaliperBackend
