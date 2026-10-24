import Proofs.Runtime.BackendDataSize

/-! Recover list lengths from encoded size. Upper bounds on list encodings do
not imply this property: the chosen representation must charge positive space
for each cell. This contract concerns data encoding, not attacker algorithms.
-/

open PFunctor

namespace Signatures.Runtime.BackendProgram

universe v w

variable {C : StepClass.{0, v}} {Q : QuantitativeStepClass.{0, v, w} C}

structure ListLengthLaws (Q : QuantitativeStepClass.{0, v, w} C)
    (data : DataRepresentation C) : Prop where
  cons_ge : ∀ {A : Type} (a : C.Str A) (x : A) (xs : List A),
    Q.size (data.list a) xs + 1 ≤ Q.size (data.list a) (x :: xs)

namespace ListLengthLaws

variable {data : DataRepresentation C} (laws : ListLengthLaws Q data)

include laws in
theorem length_le_size {A : Type} (a : C.Str A) (xs : List A) :
    xs.length ≤ Q.size (data.list a) xs := by
  induction xs with
  | nil => exact Nat.zero_le _
  | cons x xs ih => exact (Nat.add_le_add_right ih 1).trans (laws.cons_ge a x xs)

/-- An additive cell encoding with a positive header supplies the recovery law.
The size equation is a property of the actual chosen backend representation. -/
theorem of_additive (header : Nat) (positive : 0 < header)
    (encoded : ∀ {A : Type} (a : C.Str A) (xs : List A),
      Q.size (data.list a) xs = (xs.map (Q.size a)).sum + (xs.length + 1) * header) :
    ListLengthLaws Q data := by
  constructor
  intro A a x xs
  rw [encoded, encoded]
  simp only [List.map_cons, List.sum_cons, List.length_cons]
  nlinarith

end ListLengthLaws

end Signatures.Runtime.BackendProgram
