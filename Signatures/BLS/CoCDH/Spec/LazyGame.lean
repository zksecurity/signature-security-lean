/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan
-/
import Signatures.BLS.Spec.ROMInternal
import Signatures.Model.BilinearGroup

/-!
# BLS source-game adapters for the co-CDH proof

The ordinary attacker and lazy oracle are defined in `Signatures.BLS.Spec.ROM`.
These internal game definitions retain the source-game names used throughout the
co-CDH proof. The public experiment is in `Signatures.BLS.Game`.
-/

open OracleComp OracleSpec BilinearGroup BLS.ROM

namespace BLS.CoCDH.Tight

section Games

-- Fix messages and groups, a uniformly sampleable scalar field, and message equality.
variable {F M G₁ G₂ Gₜ : Type} [Field F] [SampleableType F] [DecidableEq M]
  -- G1 supports the group and scalar operations used to generate hashes and signatures.
  [AddCommGroup G₁] [Module F G₁]
  -- G2 holds keys and Gt holds pairing values, each with compatible F-module operations.
  [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
  -- Pairing defines signature validity; security hypotheses on its bases are stated separately.
  [BilinearPairing F G₁ G₂ Gₜ]

/-- Public-key-aware lazy BLS EUF-CMA game (before appending the verification hash query).
Target-group equality is a mathematical winning check, not a reduction instruction. -/
-- This helper reads the final hash from state; blsEufLazyPK below ensures that lookup exists.
noncomputable def blsEufTightPK (g₁ : G₁) (g₂ : G₂) (adv : AdversaryPK M G₁ G₂) :
    -- The game produces a probabilistic win bit, not a reduction or a security bound.
    ProbComp Bool := by
  -- Use classical equality for the mathematical pairing check, without asserting its runtime.
  classical
  -- Build the experiment's sequence of sampling, interaction, and final acceptance.
  exact do
    -- Sample the secret key uniformly over all F, including zero.
    let x ← ($ᵗ F : ProbComp F)
    -- Retain A's proposed pair and the oracle's final private state.
    let ((mstar, σstar), st) ←
      -- Give A x*g2; initialize the real signer with x*g1, an empty cache, and no signed messages.
      (simulateQ (BLS.ROM.Internal.oracle (F := F) g₁ (x • g₁)) (adv (x • g₂))).run
        ((fun _ => none), ∅)
    -- Check the candidate signature against g2 in the pairing's left-hand side.
    pure (decide (pairing (F := F) (Gₜ := Gₜ) σstar g₂
        -- Compare with H(mstar) and pk. The zero fallback matters only without the cache wrapper.
        = pairing (F := F) (Gₜ := Gₜ) (((st.1 mstar).getD 0) • g₁) (x • g₂))
      -- Winning additionally requires that mstar was never submitted to the signing oracle.
      && decide (mstar ∉ st.2))

/-- **Public-key-aware BLS EUF-CMA in the genuinely lazy ROM.**  Hashes, signatures, and the final
verification hash are all answered on demand; no full message-indexed table is sampled. -/
-- This is the actual lazy-ROM source game used by the co-CDH security statement.
noncomputable def blsEufLazyPK (g₁ : G₁) (g₂ : G₂) (adv : AdversaryPK M G₁ G₂) :
    -- Its Boolean output records signature validity together with fresh-message success.
    ProbComp Bool :=
  -- Append the verifier's hash lookup before evaluating the cached-hash acceptance predicate.
  blsEufTightPK (F := F) (Gₜ := Gₜ) g₁ g₂ (cacheForgeryPK adv)

end Games

end BLS.CoCDH.Tight
