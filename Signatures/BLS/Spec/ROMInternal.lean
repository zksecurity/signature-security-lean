/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan
-/
import Signatures.BLS.Spec.ROM

/-! Tuple encoding retained by the reduction proofs. The ordinary handler is in
`ROM.lean`; `Proofs/ROM.lean` proves exact execution equality with this encoding. -/

open OracleComp OracleSpec

namespace BLS.ROM

/-- Internal source-game adapter: append verification's hash lookup to the attacker. -/
noncomputable def cacheForgery {M G₁ : Type} (adversary : Adversary M G₁) :
    OracleComp (advSpec M G₁) (M × G₁) := do
  let (message, signature) ← adversary
  let _ ← hash (G₁ := G₁) message
  return (message, signature)

/-- Internal public-key adapter used by the existing co-CDH reduction proofs. -/
noncomputable def cacheForgeryPK {M G₁ G₂ : Type}
    (adversary : AdversaryPK M G₁ G₂) : AdversaryPK M G₁ G₂ :=
  fun publicKey => cacheForgery (adversary publicKey)


end BLS.ROM

namespace BLS.ROM.Internal

def encodeState {F M : Type} (state : BLS.ROM.State F M) : (M → Option F) × Finset M :=
  (state.hashExponents, state.signedMessages)

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

/-- The honest BLS game oracle. Private uniform queries are forwarded without touching the state;
hash queries return `ρ_m·g₁`; signing queries record `m` and return `ρ_m·X₁`. -/
-- g1 is the hash base; in the real game X1 is the secret-key multiple x*g1.
noncomputable def oracle (g₁ X₁ : G₁) :
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

end BLS.ROM.Internal
