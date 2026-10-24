import Proofs.Runtime.BackendExpression
import Proofs.Runtime.BackendSize

/-! Encoded-size bounds for the backend's actual list representation. These
contracts charge a header for each stored cell, including repeated entries.
They do not require a finite element universe or a runtime enumeration of it.
-/

open PFunctor

namespace Signatures.Runtime.BackendProgram

universe v w

variable {C : StepClass.{0, v}}
  {Q : QuantitativeStepClass.{0, v, w} C}

structure ListSizeLaws (Q : QuantitativeStepClass.{0, v, w} C)
    (data : DataRepresentation C) (header : Nat) : Prop where
  nil_le : ∀ {A : Type} (a : C.Str A), Q.size (data.list a) [] ≤ header
  cons_le : ∀ {A : Type} (a : C.Str A) (x : A) (xs : List A),
    Q.size (data.list a) (x :: xs) ≤ Q.size a x + Q.size (data.list a) xs + header

namespace ListSizeLaws

variable {data : DataRepresentation C} {header : Nat}
  (laws : ListSizeLaws Q data header)

include laws

theorem size_le_sum {A : Type} (a : C.Str A) (xs : List A) :
    Q.size (data.list a) xs ≤ (xs.map (Q.size a)).sum + (xs.length + 1) * header := by
  induction xs with
  | nil => simpa using laws.nil_le a
  | cons x xs ih =>
      have h := laws.cons_le a x xs
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      nlinarith

theorem size_le_length {A : Type} (a : C.Str A) (xs : List A) (width : Nat)
    (hwidth : ∀ x ∈ xs, Q.size a x ≤ width) :
    Q.size (data.list a) xs ≤ xs.length * (width + header) + header := by
  induction xs with
  | nil => simpa using laws.nil_le a
  | cons x xs ih =>
      have hx := hwidth x (by simp)
      have ht := ih (fun y hy => hwidth y (by simp [hy]))
      have h := laws.cons_le a x xs
      simp only [List.length_cons]
      nlinarith

theorem size_le_cap {A : Type} (a : C.Str A) (xs : List A) (width cap : Nat)
    (hwidth : ∀ x ∈ xs, Q.size a x ≤ width) (hcap : xs.length ≤ cap) :
    Q.size (data.list a) xs ≤ cap * (width + header) + header :=
  (laws.size_le_length a xs width hwidth).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ hcap) _)

end ListSizeLaws
end Signatures.Runtime.BackendProgram
