/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan
-/
import Signatures.Model.BilinearGroup
import Proofs.AlgebraicGroupModel.Spec.AffineForm

/-!
# Pairing verification and the affine discrete-log relation

Pairing verification turns an algebraic representation into the scalar relation used by
the generic extraction-probability split.
-/

open BilinearGroup

namespace AlgebraicGroupModel

variable {F G₁ G₂ Gₜ : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [AddCommGroup Gₜ] [Module F Gₜ] [BilinearPairing F G₁ G₂ Gₜ]

/-- Scalar injectivity at the paired generators already gives it at the source generator. -/
theorem smul_left_injective_of_pairing (g₁ : G₁) (g₂ : G₂)
    (hpair : Function.Injective (fun c : F => c • (pairing (F := F) g₁ g₂ : Gₜ))) :
    Function.Injective (fun c : F => c • g₁) := by
  intro a b h
  apply hpair
  simpa only [pairing_smul_left] using
    congrArg (fun z : G₁ => (pairing (F := F) z g₂ : Gₜ)) h

/-- **Pairing-setting DLog relation.**  The verification equation `e(σ, g₂) = e(c·g₁, α·g₂)`,
together with the AGM soundness `σ = repr.eval α • g₁` and pairing nondegeneracy, forces the affine
discrete-log relation `repr.eval α = c·α`.  This is the hypothesis the generic forgery split
(`agm_forgery_extract_split`) consumes — a verifying forgery satisfies the DLog relation. -/
theorem pairing_dlog_relation (g₁ : G₁) (g₂ : G₂) {α c : F} {σ : G₁} {repr : AffineForm F}
    (hsound : σ = repr.eval α • g₁)
    (hverify : pairing (F := F) (Gₜ := Gₜ) σ g₂ = pairing (F := F) (Gₜ := Gₜ) (c • g₁) (α • g₂))
    (hpair : Function.Injective (fun x : F => x • (pairing (F := F) g₁ g₂ : Gₜ))) :
    repr.eval α = c * α := by
  apply hpair
  show repr.eval α • (pairing (F := F) g₁ g₂ : Gₜ) = (c * α) • pairing (F := F) g₁ g₂
  rw [← pairing_smul_left, ← hsound, hverify, pairing_smul_left, pairing_smul_right, smul_smul]

end AlgebraicGroupModel
