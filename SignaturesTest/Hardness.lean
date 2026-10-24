import Signatures
import Proofs
import VCVio.OracleComp.QueryTracking.QueryBound

/-! Hardness cannot be applied outside its certified class, and query bounds are not time bounds. -/

open BLS.ROM

open BilinearGroup

open OracleComp

namespace SignaturesTest.Hardness

-- Classical co-CDH adjudication preserves the challenge, solver call, and winning event.
example {F G₁ G₂ : Type} [Field F] [SampleableType F]
    [AddCommGroup G₁] [Module F G₁] [SampleableType G₁] [DecidableEq G₁]
    [AddCommGroup G₂] [Module F G₂]
    (g₁ : G₁) (g₂ : G₂) (B : BLS.CoCDH.CoCDHAdversary F G₁ G₂) :
    BLS.CoCDH.coCDHExp g₁ g₂ B = (do
      let x ← ($ᵗ F : ProbComp F)
      let h ← ($ᵗ G₁ : ProbComp G₁)
      let w ← B g₁ g₂ (x • g₁) (x • g₂) h
      pure (decide (w = x • h))) := by
  unfold BLS.CoCDH.coCDHExp
  apply bind_congr
  intro x
  apply bind_congr
  intro h
  apply bind_congr
  intro w
  by_cases hw : w = x • h <;> simp [hw]

-- The BLS game still performs the same final hash lookup, verification, and freshness check.
open AlgebraicGroupModel BLS.CoCDH.Tight in
example {F M G₁ G₂ Gₜ : Type} [Field F] [SampleableType F] [DecidableEq M]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [BilinearPairing F G₁ G₂ Gₜ] [DecidableEq Gₜ]
    (g₁ : G₁) (g₂ : G₂) (adv : AdversaryPK M G₁ G₂) :
    blsEufLazyPK (F := F) (Gₜ := Gₜ) g₁ g₂ adv = (do
      let x ← ($ᵗ F : ProbComp F)
      let ((m, sig), st) ←
        (simulateQ (BLS.ROM.Internal.oracle (F := F) g₁ (x • g₁))
          (cacheForgeryPK adv (x • g₂))).run ((fun _ => none), ∅)
      pure (decide (pairing (F := F) (Gₜ := Gₜ) sig g₂ =
          pairing (F := F) (Gₜ := Gₜ) (((st.1 m).getD 0) • g₁) (x • g₂)) &&
        decide (m ∉ st.2))) := by
  unfold blsEufLazyPK blsEufTightPK
  apply bind_congr
  intro x
  apply bind_congr
  rintro ⟨⟨m, sig⟩, cache, signed⟩
  by_cases h : pairing (F := F) (Gₜ := Gₜ) sig g₂ =
      pairing (F := F) (Gₜ := Gₜ) (((cache m).getD 0) • g₁) (x • g₂)
  · simp [h]
  · simp

-- Classical adjudication preserves exactly the former experiment with a supplied decider.
example {F G₁ G₂ : Type} [Field F] [SampleableType F] [DecidableEq F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    (g₁ : G₁) (g₂ : G₂) (B : AlgebraicGroupModel.DLog11Adversary F G₁ G₂) :
    AlgebraicGroupModel.dlog11Exp g₁ g₂ B = (do
      let x ← ($ᵗ F : ProbComp F)
      let y ← B g₁ (x • g₁) g₂ (x • g₂)
      pure (decide (y = x))) := by
  unfold AlgebraicGroupModel.dlog11Exp
  apply bind_congr
  intro x
  apply bind_congr
  intro y
  by_cases h : y = x <;> simp [h]

-- A hardness assumption alone cannot bound a solver excluded by its budget predicate.
example : Model.HardWithin (fun _ : Unit => (1 : ENNReal)) (fun _ _ => False) 0 0 := by
  intro _ h
  exact False.elim h

example : ¬ Model.HardWithin (fun _ : Unit => (1 : ENNReal)) (fun _ _ => True) 0 0 := by
  intro h
  exact (by simp : ¬ (1 : ENNReal) ≤ 0) (h () trivial)

-- Even an arbitrary pure function has zero oracle queries. No runtime conclusion follows.
example {α β : Type} (f : α → β) (x : α) :
    IsQueryBoundP (pure (f x) : ProbComp β) (fun _ => True) 0 := by
  simp

-- With no signing calls the Coron factor is exactly one, not zero.
example : Model.coronFactor 0 = 1 := by simp [Model.coronFactor]

end SignaturesTest.Hardness
