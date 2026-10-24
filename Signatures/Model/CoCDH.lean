/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan
-/
import Signatures.Model.DLog11
import Signatures.BLS.CoCDH.Spec.Assumption

/-!
# Hardness targets: co-CDH and `(1,1)`-DLog

The two assumptions the signature reductions land on:

* **co-CDH** (`coCDHExp`): given `(g₁, g₂, x·g₁, x·g₂, h)`, output `x·h` — the standard-model
  target of the BLS Coron reduction.
* **`(1,1)`-DLog** (`dlog11Exp`): given `(g₁, α·g₁, g₂, α·g₂)`, output `α` — the AGM target of the
  linear-functional (BLS / OOPS / Proximity) reductions.

We package their success probabilities as advantages and record the Coron loss factor.
-/

open OracleComp
open scoped ENNReal

namespace Model

variable {F G₁ G₂ : Type} [Field F] [SampleableType F]
  [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
  [AddCommGroup G₂] [Module F G₂]

/-- Advantage of a `(1,1)`-DLog adversary: the probability it recovers `α`. -/
noncomputable def dlog11Advantage (g₁ : G₁) (g₂ : G₂)
    (B : AlgebraicGroupModel.DLog11Adversary F G₁ G₂) : ℝ≥0∞ :=
  𝒟[AlgebraicGroupModel.dlog11Exp g₁ g₂ B] {true}

/-- Advantage of a co-CDH adversary: the probability it outputs `x·h`. -/
noncomputable def coCDHAdvantage (g₁ : G₁) (g₂ : G₂)
    (B : BLS.CoCDH.CoCDHAdversary F G₁ G₂) : ℝ≥0∞ :=
  𝒟[BLS.CoCDH.coCDHExp g₁ g₂ B] {true}

/-- The Coron reduction loss factor for `qS` signing queries,
`((qS+1)⁻¹ · (qS/(qS+1))^qS)⁻¹ ≈ e·qS` — the (non-tight) linear-in-`qS` loss. -/
noncomputable def coronFactor (qS : ℕ) : ℝ≥0∞ :=
  ((qS + 1 : ℝ≥0∞)⁻¹ * ((qS : ℝ≥0∞) / (qS + 1)) ^ qS)⁻¹

end Model
