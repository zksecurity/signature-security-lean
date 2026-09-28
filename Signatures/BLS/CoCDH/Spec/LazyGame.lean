/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan
-/
import Signatures.AlgebraicGroupModel.Spec.BilinearGroup
import VCVio.OracleComp.Constructions.SampleableType
import VCVio.OracleComp.QueryTracking.LoggingOracle

/-!
# BLS lazy random-oracle EUF-CMA game (faithful oracle model, co-CDH route)

The genuinely lazy ROM used by the Coron co-CDH reduction.  Crucially the random oracle is
**programmable / lazy**, not an eager table published in the public key: the co-CDH reduction must
be able to embed its challenge into the hash answers on demand, which an up-front table forbids.

Random-oracle answers are represented by their *discrete logarithms* `ρ` (cache `M → Option F`),
alongside the set of signed messages (`Finset M`) used for the freshness check:

* a **hash** query `m` returns `ρ_m · g₁` (sampling and caching `ρ_m` on first use);
* a **signing** query `m` records `m` and returns `ρ_m · X₁` (with `X₁ = x·g₁`, so `= x·H(m)`);
* private uniform randomness is forwarded untouched.

This file is statement-level: it contains only the model definitions (no proofs).
-/

open OracleComp OracleSpec AlgebraicGroupModel

namespace BLS.CoCDH.Tight

/-- The oracle interface of a BLS adversary: private uniform randomness, the (lazy) random oracle,
and the signing oracle.  The association matches VCVio's `ambient + signing` convention. -/
-- Request tags distinguish randomness n, hash message m, and signing message m, in that order.
abbrev advSpec (M G₁ : Type) := (unifSpec + (M →ₒ G₁)) + (M →ₒ G₁)

/-- A fixed-public-key lazy-game adversary with private randomness, hash, and signing oracles. -/
-- Unlike the AGM route, this adversary returns a raw message/signature pair with no coefficients.
abbrev TightAdv (M G₁ : Type) := OracleComp (advSpec M G₁) (M × G₁)

/-- A public-key-indexed family of lazy-game adversaries. -/
-- A receives the G2 verification key before adaptively using the oracle interface.
abbrev TightAdvPK (M G₁ G₂ : Type) := G₂ → TightAdv M G₁

-- M is the message type; G1 holds hashes/signatures and G2 holds verification keys.
variable {M G₁ G₂ : Type}

/-- Append the verification hash query to a fixed-key interactive adversary: the standard lazy-ROM
convention that verification samples and caches the forgery message's RO value on demand. -/
-- Extend a completed adversary run with the verifier's lookup of the proposed message hash.
noncomputable def cacheForgery (adv : TightAdv M G₁) : TightAdv M G₁ :=
  -- This extra query is in the same program and therefore shares the same persistent cache.
  (do
    -- First allow A to finish and choose its message/signature pair adaptively.
    let out ← adv
    -- Left-right selects hashing of out.1, not signing; the reply point itself is discarded here.
    let _ ← (liftM ((advSpec M G₁).query (Sum.inl (Sum.inr out.1))) :
      -- The lookup still returns G1, while its effect ensures the final message is in the cache.
      OracleComp (advSpec M G₁) G₁)
    -- Preserve A's pair exactly; only the cache has potentially gained a new hash value.
    pure out : OracleComp (advSpec M G₁) (M × G₁))

/-- Append the verification hash query pointwise to a public-key-indexed adversary. -/
-- Apply that same verification-hash wrapper after A receives its public key.
noncomputable def cacheForgeryPK (adv : TightAdvPK M G₁ G₂) : TightAdvPK M G₁ G₂ :=
  -- The wrapper neither changes pk nor restricts A's earlier requests.
  fun pk => cacheForgery (adv pk)

section Oracle

-- Scalar sampling supplies random hash exponents; message equality recognizes cache hits.
variable {F M G₁ : Type} [SampleableType F] [DecidableEq M] [SMul F G₁]

/-- Look up a cached random-oracle discrete logarithm, sampling and caching it on first use. -/
-- The private state pairs a partial scalar cache with the set of messages ever signed.
noncomputable def getDlogS (m : M) : StateT ((M → Option F) × Finset M) ProbComp F := do
  -- Read the cached exponent for m without modifying the signed-message set.
  match (← get).1 m with
  -- Repeated lookups reuse the same scalar, ensuring consistent hashes and signatures.
  | some ρ => pure ρ
  -- A first lookup has no cached exponent yet.
  | none =>
      -- Sample its exponent uniformly in F, independently of earlier sampling calls.
      let ρ ← (liftM ($ᵗ F) : StateT ((M → Option F) × Finset M) ProbComp F)
      -- Store only this new cache entry and preserve the signed-message set unchanged.
      modify (fun s => (Function.update s.1 m (some ρ), s.2))
      -- Return the same scalar that future lookups of m will reuse.
      pure ρ

/-- The lazy real BLS oracle. Private uniform queries are forwarded without touching the state;
hash queries return `ρ_m·g₁`; signing queries record `m` and return `ρ_m·X₁`. -/
-- g1 is the hash base; in the real game X1 is the secret-key multiple x*g1.
noncomputable def realOracle (g₁ X₁ : G₁) :
    -- Interpret all A's requests while privately carrying the scalar cache and signing set.
    QueryImpl (advSpec M G₁) (StateT ((M → Option F) × Finset M) ProbComp) :=
  -- Requests can be chosen adaptively; dispatch according to their sum-constructor tag.
  fun q => match q with
    -- Left-left requests a uniformly random number from 0 through n.
    | Sum.inl (Sum.inl n) =>
        -- Forward the request to the underlying probabilistic computation.
        (liftM (unifSpec.query n : ProbComp (Fin (n + 1))) :
          -- Lifting it into StateT leaves both the hash cache and signing set untouched.
          StateT ((M → Option F) × Finset M) ProbComp (Fin (n + 1)))
    -- Left-right is an explicit hash query on m.
    | Sum.inl (Sum.inr m) => do
        -- Reuse or lazily sample m's private hash exponent.
        let ρ ← getDlogS (F := F) m
        -- Reveal only the hash point, not its cached exponent.
        pure (ρ • g₁)
    -- Right is a signing query on m.
    | Sum.inr m => do
        -- Mark m as signed; repeating it does not create a second set entry.
        modify (fun s => (s.1, insert m s.2))
        -- Signing uses the same hash exponent as explicit and final-verification lookups.
        let ρ ← getDlogS (F := F) m
        -- Since X1 = x*g1 in the game, this point is x times the hash of m.
        pure (ρ • X₁)

end Oracle

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
noncomputable def blsEufTightPK (g₁ : G₁) (g₂ : G₂) (adv : TightAdvPK M G₁ G₂) :
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
      (simulateQ (realOracle (F := F) g₁ (x • g₁)) (adv (x • g₂))).run ((fun _ => none), ∅)
    -- Check the candidate signature against g2 in the pairing's left-hand side.
    pure (decide (pairing (F := F) (Gₜ := Gₜ) σstar g₂
        -- Compare with H(mstar) and pk. The zero fallback matters only without the cache wrapper.
        = pairing (F := F) (Gₜ := Gₜ) (((st.1 mstar).getD 0) • g₁) (x • g₂))
      -- Winning additionally requires that mstar was never submitted to the signing oracle.
      && decide (mstar ∉ st.2))

/-- **Public-key-aware BLS EUF-CMA in the genuinely lazy ROM.**  Hashes, signatures, and the final
verification hash are all answered on demand; no full message-indexed table is sampled. -/
-- This is the actual lazy-ROM source game used by the co-CDH security statement.
noncomputable def blsEufLazyPK (g₁ : G₁) (g₂ : G₂) (adv : TightAdvPK M G₁ G₂) :
    -- Its Boolean output records signature validity together with fresh-message success.
    ProbComp Bool :=
  -- Append the verifier's hash lookup before evaluating the cached-hash acceptance predicate.
  blsEufTightPK (F := F) (Gₜ := Gₜ) g₁ g₂ (cacheForgeryPK adv)

end Games

end BLS.CoCDH.Tight
