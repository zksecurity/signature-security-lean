/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan
-/
import Proofs.OOPS.SignatureHandle
import Proofs.LinearFunctional.Adaptive

/-! # OOPS extraction from the private-table proof backend -/

open BilinearGroup

open OracleComp AlgebraicGroupModel AlgebraicGroupModel.LinFunctional
open OOPS.Handle (oopsWMulti targetMessages forgery_coeff_ne_zero_multi)

namespace OOPS.Proofs

variable {F T G₁ G₂ Gₜ : Type}
variable [Field F] [SampleableType F] [Fintype F] [DecidableEq F]
  [Fintype T] [DecidableEq T]
  [AddCommGroup G₁] [Module F G₁] [SampleableType G₁] [Fintype G₁]
  [AddCommGroup G₂] [Module F G₂]
  [AddCommGroup Gₜ] [Module F Gₜ]
  [BilinearPairing F G₁ G₂ Gₜ] [DecidableEq Gₜ]

/-- Vandermonde reduction after the lazy source game has been translated to the backend. -/
theorem adaptive_security (g₁ : G₁) (g₂ : G₂) (d : ℕ)
    (adv : AdaptiveAdv F (F × T) (T × Fin (d + 1)) G₁ G₂)
    (hgen : Function.Bijective (fun ρ : F => ρ • g₁))
    (hpair : Function.Injective (fun c : F => c • (pairing (F := F) g₁ g₂ : Gₜ))) :
    Pr[fun x => (targetMessages x.1.2.v x.1.2.mstar.2).card ≤ d ∧
        dynForgerySucc (Gₜ := Gₜ) (oopsWMulti d) g₁ g₂ x |
      realGameDynAdaptive (G₁ := G₁) (oopsWMulti d) g₂ adv] ≤
      Pr[= true | dlog11Exp g₁ g₂ (adaptiveGoodDlogReduction (oopsWMulti d) adv)] +
      Pr[= true | dlog11Exp g₁ g₂ (adaptiveBadDlogReduction (oopsWMulti d) adv)] +
      1 / (Fintype.card F : ENNReal) := by
  classical
  let valid : DynForgery F (F × T) (T × Fin (d + 1)) → Prop := fun fo =>
    (targetMessages fo.2.v fo.2.mstar.2).card ≤ d
  let jk : DynForgery F (F × T) (T × Fin (d + 1)) → T × Fin (d + 1) := fun fo =>
    if h : ∃ j : Fin (d + 1),
        Lcoeff (oopsWMulti d) fo.2.mstar fo.2.v fo.2.ξ (fo.2.mstar.2, j) ≠ 0
      then (fo.2.mstar.2, h.choose)
      else (fo.2.mstar.2, ⟨0, Nat.succ_pos d⟩)
  have hvand : ∀ fo, valid fo → fo.Fresh → dynDenomCoeff (oopsWMulti d) fo (jk fo) ≠ 0 := by
    intro fo hdegree hfresh
    have hex := forgery_coeff_ne_zero_multi fo.2.v fo.2.mstar fo.2.ξ hdegree hfresh
    simp only [jk, dynDenomCoeff, dif_pos hex]
    exact hex.choose_spec
  exact functional_euf_cma_adaptive (Gₜ := Gₜ) (oopsWMulti d) g₁ g₂ adv
    valid jk hgen hvand hpair

end OOPS.Proofs
