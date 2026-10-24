import Proofs.Runtime.BackendLocalCost

/-! Fold accounting with an invariant indexed by the remaining input length.
This charges growing accumulators such as reversed lists without requiring an
unbounded one-step closure of a fixed accumulator-size cap. -/

namespace Signatures.Runtime.BackendProgram

/-- Each step consumes one cell. The invariant can therefore reserve space for
the remaining cells while bounding the accumulated result and every fold fee. -/
theorem foldWork_bound_remaining {A B : Type} (step : A → B → B) (body : A → B → Nat)
    (fee : List A → B → Nat) (valid : A → Prop) (inv : Nat → B → Prop)
    (bodyTime tickTime cap : Nat)
    (hb : ∀ remaining < cap, ∀ x, valid x → ∀ acc, inv (remaining + 1) acc →
      body x acc ≤ bodyTime ∧ inv remaining (step x acc))
    (hf : ∀ xs, xs.length ≤ cap → (∀ x ∈ xs, valid x) → ∀ acc, inv xs.length acc →
      fee xs acc ≤ tickTime)
    (xs : List A) (hl : xs.length ≤ cap) (hx : ∀ x ∈ xs, valid x)
    (acc : B) (hi : inv xs.length acc) :
    foldWork step body fee xs acc ≤ xs.length * (bodyTime + tickTime) + tickTime := by
  induction xs generalizing acc with
  | nil => simpa only [foldWork, List.length_nil, Nat.zero_mul, Nat.zero_add] using hf [] hl hx acc hi
  | cons x xs ih =>
      obtain ⟨hb', hinv⟩ := hb xs.length (by simp only [List.length_cons] at hl; omega)
        x (hx x (by simp)) acc hi
      have ht := ih (by simp only [List.length_cons] at hl; omega)
        (fun y hy => hx y (by simp [hy])) (step x acc) hinv
      have hc := hf (x :: xs) hl hx acc hi
      simp only [foldWork, List.length_cons]
      nlinarith

end Signatures.Runtime.BackendProgram
