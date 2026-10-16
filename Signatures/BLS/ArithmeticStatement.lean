/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan
-/
import Signatures.Model.CoCDH
import Signatures.Model.Hardness
import Signatures.BLS.Proofs.LazyAGM
import Signatures.BLS.CoCDH.Proofs.ArbitraryMessages
import Signatures.Runtime.CoronCertificate
import Signatures.Runtime.AGMBadMachine
import Signatures.Runtime.KeyEquality
import Signatures.Runtime.ProximityWeight

/-! Detailed arithmetic-source BLS co-CDH security.

The public general-attacker endpoints are `BLS.agm_security` and
`BLS.cocdh_security` in `Statement.lean`. The superseded eager-table AGM wrapper
and its arithmetic-attacker alias have been retired. The co-CDH source-certified
endpoint below remains useful for the distinct arithmetic implementation model.
Original eager probability and resource lemmas remain in their supporting modules;
see `docs/API-MIGRATION.md` for the replacement interfaces.
-/

open OracleComp AlgebraicGroupModel
open Signatures.Runtime Signatures.Runtime.Coron
open scoped ENNReal

namespace BLS.Statement

-- F is the uniformly sampled scalar field; M is the message type; G1/G2/Gt are the groups.
variable {F M G₁ G₂ Gₜ : Type} [Field F] [SampleableType F]
  -- Compare messages for cache lookup and freshness.
  [DecidableEq M]
  -- Hashes/signatures live in G1, with scalar action and uniform sampling.
  [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
  -- Public keys live in G2; pairing results live in Gt. Group notation is additive.
  [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
  -- Supply the verification pairing; hpair below requires its base-point value to be nonzero.
  [BilinearPairing F G₁ G₂ Gₜ]

/-- BLS EUF-CMA security in the type-3 programmable ROM, with a certified machine budget.
The co-CDH challenge is (g1, g2, x*g1, x*g2, h); no G2-to-G1 map is assumed.
The source certificate bounds local work and all three query kinds, including qH = queries 1.
The compiler derives the named Coron solver's budget; the caller supplies hardness at that budget. -/
-- Messages may be infinite; equality supports cache lookup and freshness.
theorem bls_eufcma_of_cocdh_machine_hardness
    [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
    -- Fix the public base points and signing-call limit used in the Coron loss.
    (g₁ : G₁) (g₂ : G₂) (qS : Nat)
    -- The adaptive forger is inferred from cert; it need not be algebraic.
    {adv : BLS.CoCDH.Tight.TightAdvPK M G₁ G₂}
    -- Every signature-group point must be a scalar multiple of g1.
    (hgen : Function.Surjective (fun r : F => r • g₁))
    -- Require a nonzero pairing of the chosen base points.
    (hpair : (pairing (F := F) g₁ g₂ : Gₜ) ≠ 0)
    -- At every generated key, all reply paths have at most qS signing calls, including repeats.
    -- Query tags are ((randomness + hash) + signing): isRight selects signing only.
    (hqs : ∀ x : F, IsQueryBoundP (adv (x • g₂)) (·.isRight) qS)
    -- Arithmetic and sampling prices are explicit model contracts, not proved bit costs.
    {cost : PrimitiveCosts} (sampling : Machine.SamplingCosts)
    -- randomBound bounds private-random request arity; localTime bounds source local work.
    -- queries 0 = random-call budget, queries 1 = qH, queries 2 = signing-call budget.
    -- queries 2 and qS need not be equal: both bounds must hold; qS controls the Coron loss.
    {randomBound localTime : Nat} {queries : Fin 3 → Nat}
    -- Supply executable code equal to adv at every key, with all-path local/query bounds.
    -- These inferred indices are real premises, including the hash-query cap queries 1.
    (cert : SourceCertificate (F := F) cost randomBound localTime queries adv)
    -- The assumed maximum success probability for budget-bounded co-CDH solvers.
    (epsilon : ENNReal)
    -- Assume every co-CDH solver within the derived machine budget succeeds with probability...
    (hhard : Model.HardWithin (Model.coCDHAdvantage (F := F) g₁ g₂)
      -- ...in this arithmetic/sampling cost model...
      (coCDHWithin (F := F) (M := M) cost sampling)
      -- ...at most epsilon. targetBudget includes qH, other queries, local work, and setup.
      (cert.targetBudget sampling qS) epsilon) :
    -- Probability of a valid signature on a never-signed message in the same lazy-ROM game.
    𝒟[BLS.CoCDH.Tight.blsEufLazyPK (F := F) (Gₜ := Gₜ) g₁ g₂ adv] {true} ≤
      -- qS affects the probability loss; qH affects the budget at which hardness is assumed.
      Model.coronFactor qS * epsilon := by
  have reduction :
      𝒟[BLS.CoCDH.Tight.blsEufLazyPK (F := F) (Gₜ := Gₜ) g₁ g₂ adv] {true} ≤
        Model.coronFactor qS * Model.coCDHAdvantage g₁ g₂
          (BLS.CoCDH.coronReductionLazyPK (F := F) qS (BLS.CoCDH.Tight.cacheForgeryPK adv)) := by
     classical
    let : Fintype F := Fintype.ofFinite F
    let : Fintype G₁ := Fintype.ofSurjective (fun r : F => r • g₁) hgen
    have hscalar := smul_left_injective F hpair
    refine BLS.CoCDH.Proofs.security_arbitrary_messages g₁ g₂ qS adv
      ⟨smul_left_injective_of_pairing g₁ g₂ hscalar, hgen⟩ ?_ hqs
    intro x y h
    obtain ⟨a, rfl⟩ := hgen x
    obtain ⟨b, rfl⟩ := hgen y
    exact congrArg (fun c : F => c • g₁)
      (hscalar (by simpa only [pairing_smul_left] using h))
  exact reduction.trans (mul_le_mul_right (hhard _ (cert.within sampling qS)) _)


end BLS.Statement
