/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan
-/
import Proofs.LinearFunctional.Adaptive

/-! # BLS freshness supplies a nonzero symbolic coefficient -/

open AlgebraicGroupModel.LinFunctional

namespace BLS.Proofs

variable {F M : Type} [Field F] [DecidableEq M]

def indicatorWeight : M → M → F := fun i m => if i = m then 1 else 0

/-- Freshness makes the target-message coordinate of the denominator equal to one. -/
theorem fresh_coefficient (fo : DynForgery F M M) (hfresh : fo.Fresh) :
    dynDenomCoeff indicatorWeight fo fo.2.mstar ≠ 0 := by
  have h : ∀ q, fo.2.mstar ≠ fo.2.v q := hfresh
  simp [dynDenomCoeff, Lcoeff, indicatorWeight, h]

end BLS.Proofs
