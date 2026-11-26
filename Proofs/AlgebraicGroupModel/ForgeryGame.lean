/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan
-/
import Proofs.AlgebraicGroupModel.Extraction
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Generic AGM forgery game — the extraction-probability split

A scheme-agnostic bound for any AGM signature reduction.  An "AGM forgery game" is *any*
probabilistic computation `oa : ProbComp γ` whose output exposes three quantities:

* `success z` — the adversary won (produced a valid, fresh forgery);
* `repr z`    — the forgery's discrete-log as an affine form of the secret `α`;
* `c z`       — the verification target (`ρ*` or `μ*`, depending on the scheme).

The single AGM hypothesis (`hsound`) is that a winning forgery satisfies the verification equation
`repr.eval α = c·α` (this is what the pairing equation + AGM soundness force).  Then the reduction's
extracted value `repr.const / (c − repr.lin)` equals `α` *unless* the bad event `repr.lin = c`
occurs, giving

  `Pr[win]  ≤  Pr[extract = α]  +  Pr[win ∧ repr.lin = c]`.

The first term is the reduction's DLog success. Bounding the second requires a separate argument:
in the adaptive proofs it costs another DLog reduction plus `1/|F|`, not just a collision bound.
The collision lemma below applies only when the sampled coordinate is independent of its coefficients.
-/

open OracleComp

namespace AlgebraicGroupModel

variable {F γ : Type} [Field F] [DecidableEq F]

/-- **Generic AGM forgery → extraction split.**  For any forgery game, the win probability is at
most the reduction's extraction-success probability plus the bad-event probability `repr.lin = c`.
The cryptographic core is `extract_secret` applied pointwise on the good event.

The secret `α` is read off each game output (`secret : γ → F`), so this applies directly to a game
that *samples* `α` internally (as the EUF-CMA-to-DLog reductions do) — no need to fix `α` outside. -/
theorem agm_forgery_extract_split (oa : ProbComp γ)
    (success : γ → Prop) (repr : γ → AffineForm F) (c : γ → F) (secret : γ → F)
    (hsound : ∀ z ∈ support oa, success z → (repr z).eval (secret z) = c z * secret z) :
    Pr{let z ← oa}[success z]
      ≤ Pr{let z ← oa}[(repr z).const / (c z - (repr z).lin) = secret z]
        + Pr{let z ← oa}[success z ∧ (repr z).lin = c z] := by
  refine le_trans (prEvent_mono_of_support oa _ _ ?_) (prEvent_or_le oa _ _)
  intro z hz hsucc
  by_cases hlin : (repr z).lin = c z
  · exact Or.inr ⟨hsucc, hlin⟩
  · exact Or.inl (extract_secret (hsound z hz hsucc) hlin).symm

/-- **Affine deferred-sampling collision kernel.** If `a`, `b`, and `t` are fixed before a fresh
uniform `ρ` is sampled and `a ≠ 0`, then `a·ρ + b = t` is a singleton collision event. -/
theorem affine_uniform_collision {F : Type} [Field F] [Fintype F] [SampleableType F] [DecidableEq F]
    {γ : Type} (oa : ProbComp γ)
    (a b t : γ → F) (ha : ∀ z ∈ support oa, a z ≠ 0) :
    Pr{let w ← (do let z ← oa; let ρ ← ($ᵗ F : ProbComp F); pure (z, ρ))}[a w.1 * w.2 + b w.1 = t w.1]
      ≤ 1 / (Fintype.card F : ENNReal) := by
  apply prEvent_bind_le_of_forall_le_of_support
  intro z hz
  have heq (ρ : F) : a z * ρ + b z = t z ↔ ρ = (t z - b z) / a z := by
    rw [eq_div_iff (ha z hz), mul_comm ρ, eq_sub_iff_add_eq]
  simp only [prEvent_norm, heq, SampleableType.prEvent_uniformSample_eq_singleton, one_div]
  exact le_rfl

end AlgebraicGroupModel
