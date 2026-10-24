import Proofs.Runtime.BackendListLength

/-! Recover the size of a nested payload from its enclosing list. Positive
cell accounting bounds lengths, but does not alone bound the stored elements;
this separate encoding law is needed for nested coefficient rows. -/

open PFunctor

namespace Signatures.Runtime.BackendProgram

universe v w

variable {C : StepClass.{0, v}} {Q : QuantitativeStepClass.{0, v, w} C}

structure ListPayloadLaws (Q : QuantitativeStepClass.{0, v, w} C)
    (data : DataRepresentation C) : Prop where
  head_le : ∀ {A : Type} (a : C.Str A) (x : A) (xs : List A),
    Q.size a x ≤ Q.size (data.list a) (x :: xs)

namespace ListPayloadLaws

variable {data : DataRepresentation C} (laws : ListPayloadLaws Q data) (lengths : ListLengthLaws Q data)

include laws lengths in
theorem member_size_le {A : Type} (a : C.Str A) (xs : List A) (x : A) (hx : x ∈ xs) :
    Q.size a x ≤ Q.size (data.list a) xs := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
      rcases List.mem_cons.mp hx with rfl | hx
      · exact laws.head_le a x ys
      · have ht := lengths.cons_ge a y ys
        exact (ih hx).trans (by omega)

theorem of_additive (header : Nat)
    (encoded : ∀ {A : Type} (a : C.Str A) (xs : List A),
      Q.size (data.list a) xs = (xs.map (Q.size a)).sum + (xs.length + 1) * header) :
    ListPayloadLaws Q data := by
  constructor
  intro A a x xs
  rw [encoded]
  simp only [List.map_cons, List.sum_cons]
  omega

end ListPayloadLaws

end Signatures.Runtime.BackendProgram
