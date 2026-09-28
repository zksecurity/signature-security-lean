/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan
-/
import Mathlib.Algebra.BigOperators.Field

/-!
# Linear-functional signature weights

The BLS, OOPS, and Proximity AGM reductions share a target scalar
`μ(m) = ∑ i, ρ i * w i m`.  Their bad event is governed by the coordinate functional
`L i = w i m* - ∑ q, ξ q * w i (v q)`.
-/

open Finset

namespace AlgebraicGroupModel.LinFunctional

variable {F M ι : Type} [Field F] {Q : ℕ}

/-- The linear target `μ(m) = ∑ᵢ ρᵢ wᵢ(m)`. -/
def muW [Fintype ι] (w : ι → M → F) (ρ : ι → F) (m : M) : F := ∑ i, ρ i * w i m

/-- The `i`-th coordinate of the forgery functional
`Lᵢ = wᵢ(m*) - ∑_q ξ_q wᵢ(v_q)`. -/
def Lcoeff (w : ι → M → F) (mstar : M) (v : Fin Q → M) (ξ : Fin Q → F) (i : ι) : F :=
  w i mstar - ∑ q, ξ q * w i (v q)

end AlgebraicGroupModel.LinFunctional
