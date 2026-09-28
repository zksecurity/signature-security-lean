/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan
-/
import Signatures.LinearFunctional.Proofs.Adaptive

/-! # Proximity extraction with an explicit fresh-collision probability -/

open OracleComp AlgebraicGroupModel AlgebraicGroupModel.LinFunctional

namespace Proximity.Proofs

variable {F S G₁ G₂ Gₜ : Type} {ℓ : ℕ}
variable [Field F] [SampleableType F] [Fintype F] [DecidableEq F]
  [Fintype S] [DecidableEq S]
  [AddCommGroup G₁] [Module F G₁] [SampleableType G₁] [Fintype G₁]
  [AddCommGroup G₂] [Module F G₂]
  [AddCommGroup Gₜ] [Module F Gₜ]
  [BilinearPairing F G₁ G₂ Gₜ] [DecidableEq Gₜ]

def coordinateWeight (ℓ : ℕ) :
    (Option (Fin ℓ) × S) → ((Fin ℓ → F) × S) → F :=
  fun b ms => if b.2 = ms.2 then (match b.1 with | none => 1 | some k => ms.1 k) else 0

/-- The original non-collision property, stated on the exact-length representation. -/
def Noncollision (fo : DynForgery F ((Fin ℓ → F) × S) (Option (Fin ℓ) × S)) : Prop :=
  fo.2.mstar.1 ≠ fun k => ∑ q, fo.2.ξ q * (fo.2.v q).1 k

/-- Summing one coordinate over every topic recovers the full weighted message relation. -/
theorem sum_coordinate_coeff
    (fo : DynForgery F ((Fin ℓ → F) × S) (Option (Fin ℓ) × S)) (k : Fin ℓ) :
    ∑ s, dynDenomCoeff (coordinateWeight ℓ) fo (some k, s) =
      fo.2.mstar.1 k - ∑ q, fo.2.ξ q * (fo.2.v q).1 k := by
  simp only [dynDenomCoeff, Lcoeff, coordinateWeight]
  rw [Finset.sum_sub_distrib, Finset.sum_comm]
  simp [← Finset.mul_sum]

theorem noncollision_coeff
    (fo : DynForgery F ((Fin ℓ → F) × S) (Option (Fin ℓ) × S)) (hnc : Noncollision fo) :
    ∃ i, dynDenomCoeff (coordinateWeight ℓ) fo i ≠ 0 := by
  by_contra h
  push Not at h
  apply hnc
  funext k
  have heq := sum_coordinate_coeff fo k
  simp only [h, Finset.sum_const_zero] at heq
  exact sub_eq_zero.mp heq.symm

/-- Split off fresh collisions; extraction bounds the noncolliding winning executions. -/
theorem adaptive_security (g₁ : G₁) (g₂ : G₂)
    (adv : AdaptiveAdv F ((Fin ℓ → F) × S) (Option (Fin ℓ) × S) G₁ G₂)
    (hgen : Function.Bijective (fun ρ : F => ρ • g₁))
    (hpair : Function.Injective (fun c : F => c • (pairing (F := F) g₁ g₂ : Gₜ))) :
    Pr[dynForgerySucc (Gₜ := Gₜ) (coordinateWeight ℓ) g₁ g₂ |
        realGameDynAdaptive (coordinateWeight ℓ) g₂ adv] ≤
      Pr[= true | dlog11Exp g₁ g₂ (adaptiveGoodDlogReduction (coordinateWeight ℓ) adv)] +
      Pr[= true | dlog11Exp g₁ g₂ (adaptiveBadDlogReduction (coordinateWeight ℓ) adv)] +
      1 / (Fintype.card F : ENNReal) +
      Pr[fun x => x.1.Fresh ∧ ¬ Noncollision x.1 |
        realGameDynAdaptive (coordinateWeight ℓ) g₂ adv] := by
  classical
  let jk : DynForgery F ((Fin ℓ → F) × S) (Option (Fin ℓ) × S) → Option (Fin ℓ) × S :=
    fun fo => if h : ∃ i, dynDenomCoeff (coordinateWeight ℓ) fo i ≠ 0
      then h.choose else (none, fo.2.mstar.2)
  have hvand : ∀ fo, Noncollision fo → fo.Fresh →
      dynDenomCoeff (coordinateWeight ℓ) fo (jk fo) ≠ 0 := by
    intro fo h _
    have hex := noncollision_coeff fo h
    simpa only [jk, dite_eq_left hex] using hex.choose_spec
  refine le_trans (le_trans (probEvent_mono ?_)
    (probEvent_or_le (realGameDynAdaptive (coordinateWeight ℓ) g₂ adv)
      (fun x => Noncollision x.1 ∧ dynForgerySucc (Gₜ := Gₜ) (coordinateWeight ℓ) g₁ g₂ x)
      (fun x => x.1.Fresh ∧ ¬ Noncollision x.1))) ?_
  · intro x _ hsucc
    by_cases h : Noncollision x.1
    · exact Or.inl ⟨h, hsucc⟩
    · exact Or.inr ⟨hsucc.2, h⟩
  · exact add_le_add (functional_euf_cma_adaptive (Gₜ := Gₜ) (coordinateWeight ℓ)
      g₁ g₂ adv Noncollision jk hgen hvand hpair) le_rfl

end Proximity.Proofs
