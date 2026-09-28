/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan
-/
import Signatures.AlgebraicGroupModel.Spec.BilinearGroup
import VCVio.OracleComp.Constructions.SampleableType

/-!
# co-CDH (type-3 co-Computational Diffie–Hellman) — the standard-assumption BLS target

The security of BLS in the **type-3** pairing setting (`G₁ ≠ G₂`, no efficient isomorphism) reduces,
in the random-oracle model, to **co-CDH** — *not* to the algebraic-group-model DLog target of
`Signatures/BLS/Statement.lean`.  This is the assumption-based, non-AGM route.

**co-CDH (type-3).** Given `(g₁, g₂, x·g₁, x·g₂, h)` with `h ∈ G₁` a uniform challenge and `x` a
secret scalar, compute `x·h ∈ G₁`.  Intuition: the exponent `x` is exposed in *both* groups
(`x·g₁`, `x·g₂`) — which the BLS reduction needs (`x·g₁` to simulate signatures, `x·g₂` as the public
key) — yet applying it to a *fresh* `G₁` element `h` (unknown discrete log) is believed hard, since in
type-3 there is no map carrying `x` onto an arbitrary `G₁` point.  This is CDH in `G₁` with a `G₂`
co-hint; a BLS forgery on the challenge point `h` is exactly a co-CDH solution `x·h`.
-/

open OracleComp AlgebraicGroupModel

namespace BLS.CoCDH

variable {F G₁ G₂ Gₜ : Type} [Field F] [SampleableType F]
  [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
  [AddCommGroup G₂] [Module F G₂]

/-- A **co-CDH adversary**: receives `(g₁, g₂, x·g₁, x·g₂, h)` and outputs a candidate for `x·h`. -/
def CoCDHAdversary (_F G₁ G₂ : Type) := G₁ → G₂ → G₁ → G₂ → G₁ → ProbComp G₁

/-- **co-CDH experiment.**  Sample the secret `x` and a uniform challenge point `h ∈ G₁`; hand the
adversary `(g₁, g₂, x·g₁, x·g₂, h)`; it wins iff its output equals `x·h`.
Equality here judges success; it is not an instruction executed by the solver. -/
noncomputable def coCDHExp (g₁ : G₁) (g₂ : G₂)
    (adversary : CoCDHAdversary F G₁ G₂) : ProbComp Bool := by
  classical
  exact do
    let x ← ($ᵗ F : ProbComp F)
    let h ← ($ᵗ G₁ : ProbComp G₁)
    let w ← adversary g₁ g₂ (x • g₁) (x • g₂) h
    return decide (w = x • h)

end BLS.CoCDH
