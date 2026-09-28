/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan
-/
import VCVio.OracleComp.Constructions.SampleableType

/-!
# The `(1,1)`-Discrete Logarithm problem

The `(1,1)`-DLog problem (Bauer–Fuchsbauer–Loss) is the standard hardness assumption for AGM
reductions of pairing-based signatures: given `(g₁, α·g₁, g₂, α·g₂)` in `G₁² × G₂²`, output `α`.
It mirrors `DiffieHellman.dlogExp`, but with the challenge supplied in *both* source groups of a
bilinear pairing.
-/

open OracleComp

namespace AlgebraicGroupModel

variable {F G₁ G₂ : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]

/-- A `(1,1)`-DLog adversary receives the challenge `(g₁, α·g₁, g₂, α·g₂)` and tries to find `α`. -/
def DLog11Adversary (F G₁ G₂ : Type) := G₁ → G₁ → G₂ → G₂ → ProbComp F

section
variable [SampleableType F]

/-- The `(1,1)`-DLog experiment: sample `α`, hand the adversary `(g₁, α·g₁, g₂, α·g₂)`, and check
its guess. Equality in this winning predicate is mathematical, not a solver instruction. -/
noncomputable def dlog11Exp (g₁ : G₁) (g₂ : G₂)
    (adversary : DLog11Adversary F G₁ G₂) : ProbComp Bool := by
  classical
  exact do
    let α ← $ᵗ F
    let α' ← adversary g₁ (α • g₁) g₂ (α • g₂)
    return decide (α' = α)

end

end AlgebraicGroupModel
