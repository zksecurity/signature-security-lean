import Proofs.Runtime.BackendProgram

/-! Representation laws for structured values at a common backend boundary.

The header allowance is explicit, so a variable word/address width can be
accounted for. These laws describe the chosen encoding; they do not assign a
machine cost or assume arbitrary caller states have bounded size.
-/

open PFunctor

namespace Signatures.Runtime.BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}

structure SizeLaws (Q : QuantitativeStepClass.{0, v, w} C) (header : Nat) : Prop where
  prod_le : ∀ {A B : Type} (a : C.Str A) (b : C.Str B) (input : A × B),
    Q.size (StepClass.HasProd.prod a b) input ≤ Q.size a input.1 + Q.size b input.2 + header
  fst_le : ∀ {A B : Type} (a : C.Str A) (b : C.Str B) (input : A × B),
    Q.size a input.1 ≤ Q.size (StepClass.HasProd.prod a b) input
  snd_le : ∀ {A B : Type} (a : C.Str A) (b : C.Str B) (input : A × B),
    Q.size b input.2 ≤ Q.size (StepClass.HasProd.prod a b) input
  sum_le : ∀ {A B : Type} (a : C.Str A) (b : C.Str B) (input : A ⊕ B),
    Q.size (StepClass.HasSum.sum a b) input ≤ Sum.elim (Q.size a) (Q.size b) input + header
  sum_payload_le : ∀ {A B : Type} (a : C.Str A) (b : C.Str B) (input : A ⊕ B),
    Sum.elim (Q.size a) (Q.size b) input ≤ Q.size (StepClass.HasSum.sum a b) input
  none_le : ∀ {A : Type} (a : C.Str A), Q.size (StepClass.HasOption.option a) none ≤ header
  some_le : ∀ {A : Type} (a : C.Str A) (input : A),
    Q.size (StepClass.HasOption.option a) (some input) ≤ Q.size a input + header
  some_payload_le : ∀ {A : Type} (a : C.Str A) (input : A),
    Q.size a input ≤ Q.size (StepClass.HasOption.option a) (some input)

namespace SizeLaws

variable {header : Nat} (laws : SizeLaws Q header)

include laws

theorem distribute_le {A B E : Type} (a : C.Str A) (b : C.Str B) (e : C.Str E)
    (input : (A ⊕ B) × E) :
    Q.size (StepClass.HasSum.sum (StepClass.HasProd.prod a e) (StepClass.HasProd.prod b e))
        (Sum.elim (fun x => Sum.inl (x, input.2)) (fun y => Sum.inr (y, input.2)) input.1) ≤
      Q.size (StepClass.HasSum.sum a b) input.1 + Q.size e input.2 + 2 * header := by
  obtain ⟨side, saved⟩ := input
  have hp := laws.sum_payload_le a b side
  cases side with
  | inl value =>
      have hs := laws.sum_le (StepClass.HasProd.prod a e) (StepClass.HasProd.prod b e) (.inl (value, saved))
      have hx := laws.prod_le a e (value, saved)
      dsimp at *
      omega
  | inr value =>
      have hs := laws.sum_le (StepClass.HasProd.prod a e) (StepClass.HasProd.prod b e) (.inr (value, saved))
      have hx := laws.prod_le b e (value, saved)
      dsimp at *
      omega

theorem getD_le {A : Type} (a : C.Str A) (input : Option A × A) :
    Q.size a (input.1.getD input.2) ≤ Q.size (StepClass.HasOption.option a) input.1 + Q.size a input.2 := by
  obtain ⟨value, fallback⟩ := input
  cases value with
  | none => simp
  | some value =>
      have h := laws.some_payload_le a value
      simp only [Option.getD_some]
      omega

end SizeLaws

end Signatures.Runtime.BackendProgram
