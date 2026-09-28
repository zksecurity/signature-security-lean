/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan
-/
import Signatures.LinearFunctional.Proofs.Extraction

/-!
# Exact-length linear-functional extraction

An interactive signing transcript has a run-dependent finite length.  Padding it to a global
`Fin Q` is unsound for freshness-sensitive games: a dummy message either equals the forgery or adds
a fake interpolation point.  This module instead packages each algebraic output with its exact
query count `Q` and reuses the fixed-`Q` algebra pointwise.

No sampling order is imposed here; `Adaptive.lean` handles concrete-base-dependent adversaries.
-/

open OracleComp AlgebraicGroupModel Finset

namespace AlgebraicGroupModel.LinFunctional

variable {F M ι : Type} [Field F] [SampleableType F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι]

/-- A forgery representation carrying its exact, run-dependent finite signing-transcript length. -/
abbrev DynForgery (F M ι : Type) := Σ Q : ℕ, Forgery F M ι Q

/-- The represented forged group element for an exact-length transcript. -/
def dynForgeryElem {G₁ : Type} [AddCommGroup G₁] [Module F G₁]
    (g₁ : G₁) (fo : DynForgery F M ι) (H : ι → G₁) (signO : M → G₁) : G₁ :=
  forgeryElem g₁ fo.2 H signO

/-- The verification target for an exact-length transcript. -/
def dynTargetElem {G₁ : Type} [AddCommGroup G₁] [Module F G₁]
    (w : ι → M → F) (fo : DynForgery F M ι) (H : ι → G₁) : G₁ :=
  targetElem w fo.2 H

/-- Standard message freshness over exactly the active transcript positions. -/
def DynForgery.Fresh (fo : DynForgery F M ι) : Prop :=
  ∀ q, fo.2.mstar ≠ fo.2.v q

variable {G₁ G₂ Gₜ : Type}
  [AddCommGroup G₁] [Module F G₁] [SampleableType G₁] [Fintype G₁]
  [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
  [BilinearPairing F G₁ G₂ Gₜ] [DecidableEq Gₜ]

/-- Pairing verification plus freshness for a dynamically sized representation. -/
def dynForgerySucc (w : ι → M → F) (g₁ : G₁) (g₂ : G₂)
    (x : DynForgery F M ι × F × (ι → G₁) × (M → G₁)) : Prop :=
  (pairing (F := F) (Gₜ := Gₜ) (dynForgeryElem g₁ x.1 x.2.2.1 x.2.2.2) g₂
      = pairing (F := F) (Gₜ := Gₜ) (dynTargetElem w x.1 x.2.2.1) (x.2.1 • g₂))
    ∧ x.1.Fresh

/-- Affine representation of a dynamically sized forgery. -/
def dynReprA (w : ι → M → F) (fo : DynForgery F M ι) (ρ : ι → F) : AffineForm F :=
  reprA w fo.2 ρ

end AlgebraicGroupModel.LinFunctional
