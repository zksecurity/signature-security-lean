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

/-! # Detailed arithmetic-source BLS security statements

The public general-attacker AGM endpoint is `BLS.security` in `BLS/Statement.lean`:
curve, security parameter, query allowances, and algebraic adversary. Its
`SecurityModel` exposes primitive contracts and attacker resources; both lazy
solver budgets are derived. The declarations below retain their existing names.

Source-certified co-CDH and AGM security endpoints below derive solver budgets
from attacker implementations and resource bounds. The AGM conclusion includes
both DLog branches plus `1/|F|`; these existing machine solvers charge full-domain
private tables even though the security game uses a lazy random oracle. The
general-attacker endpoint above uses the proved lazy general-caller replacement.
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

section AGM

open Signatures.Runtime.AGM

variable [DecidableEq F] [Fintype M] [DecidableEq G₁] [DecidableEq G₂]

/-- An implementation of the BLS algebraic attacker in the arithmetic source
language, with semantic equality at every public key and all-path bounds on
local work, random/hash/sign calls, and output coefficient lengths.

BLS uses the message type for both hash indices and signed messages. The generic
AGM certificate's two identity conversions and internal `key` type tags are
fixed here; `key` is a machine type tag, not a signing secret key. This alias
does not claim coverage of unrestricted efficient attackers. -/
abbrev ArithmeticAttackerCertificate (cost : PrimitiveCosts)
    (randomBound localTime : Nat) (queries : Fin 3 → Nat) (gammaLength xiLength : Nat)
    (A : Model.LazyAGM.Adversary F M M G₁ G₂) :=
  SourceCertificate (F := F) (K := M) (M := M) (indexTy := key) (messageTy := key)
    cost (Equiv.refl M) (Equiv.refl M) randomBound localTime queries gammaLength xiLength A

/-- BLS AGM for a certified arithmetic-source attacker. Both exact DLog solver
budgets are derived, and hardness at those budgets bounds their success by
`goodEpsilon` and `badEpsilon`. The resulting forgery bound is their sum plus
`1/|F|`. These existing solver implementations charge full finite-domain tables;
the lazy general-caller replacement is exposed by `BLS.security` in `Statement.lean`. -/
-- This is the machine-bounded security endpoint; no separate unbounded wrapper is exposed.
theorem bls_lazy_agm_of_dlog_machine_hardness
    -- Fix public base points; the certified adaptive algebraic adversary A is inferred from cert.
    (g₁ : G₁) (g₂ : G₂) {A : Model.LazyAGM.Adversary F M M G₁ G₂}
    -- Every signature-group point must be a scalar multiple of g1.
    (hgen : Function.Surjective (fun r : F => r • g₁))
    -- Require a nonzero pairing of the chosen base points; no G2-to-G1 map is assumed.
    (hpair : (pairing (F := F) g₁ g₂ : Gₜ) ≠ 0)
    -- Fix arithmetic and sampling prices; these are model contracts, not proved bit costs.
    {cost : PrimitiveCosts} (sampling : Machine.SamplingCosts)
    -- queries: 0 = private-random calls, 1 = hash calls (qH), 2 = signing calls.
    -- randomBound bounds private-random request arity; localTime bounds source local work.
    -- queries 1 is qH; queries 0 and 2 bound random and signing calls on all adaptive paths.
    -- gammaLength/xiLength bound output hash/signing coefficient-list lengths.
    {randomBound localTime : Nat} {queries : Fin 3 → Nat} {gammaLength xiLength : Nat}
    -- Actual arithmetic-source code implementing A, together with proofs of these bounds.
    (cert : ArithmeticAttackerCertificate cost randomBound localTime queries gammaLength xiLength A)
    -- Maximum DLog success probabilities at the two derived budgets below.
    -- ENNReal is the nonnegative extended reals. Separate bounds allow different solver costs.
    (goodEpsilon badEpsilon : ENNReal)
    -- Assume every DLog solver in the following machine class and budget has success <= goodEpsilon...
    (hgoodHard : Model.HardWithin (Model.dlog11Advantage g₁ g₂)
      -- ...for recovering x from (g1,x*g1,g2,x*g2), with these arithmetic/sampling prices...
      (dlogWithin (F := F) (K := M) (M := M) cost sampling)
      -- ...at the derived good-solver budget, including queries, local work, and private-table setup.
      (cert.goodBudget sampling (cost.keyEq + 5) (cost.keyEq + cost.field + 8)) goodEpsilon)
    -- Make the analogous assumption for the bad-branch budget and badEpsilon...
    (hbadHard : Model.HardWithin (Model.dlog11Advantage g₁ g₂)
      -- ...for recovering x from (g1,x*g1,g2,x*g2), with these arithmetic/sampling prices...
      (dlogWithin (F := F) (K := M) (M := M) cost sampling)
      -- ...at the derived bad-solver budget, which also charges its masked-base construction.
      (cert.badBudget sampling (cost.keyEq + 5) (cost.keyEq + cost.field + 8)) badEpsilon) :
    -- Probability that the same lazy-ROM BLS game returns a valid signature on a never-signed message.
    𝒟[BLS.LazyAGM.game (Gₜ := Gₜ) g₁ g₂ A] {true} ≤
      -- Add both hardness bounds and retain the residual 1/|F| term; neither branch is omitted.
      -- Freshness guarantees a nonzero coefficient, not a nonzero evaluated expression.
      -- The independent hidden-slope collision is still charged by 1/|F|.
      goodEpsilon + badEpsilon + 1 / (Nat.card F : ENNReal) := by
  have reduction :
      𝒟[BLS.LazyAGM.game (Gₜ := Gₜ) g₁ g₂ A] {true} ≤
        Model.dlog11Advantage g₁ g₂ (Model.LazyAGM.goodReduction BLS.Proofs.indicatorWeight A) +
        Model.dlog11Advantage g₁ g₂ (Model.LazyAGM.badReduction BLS.Proofs.indicatorWeight A) +
        1 / (Nat.card F : ENNReal) := by
   classical
    let : Fintype F := Fintype.ofFinite F
    let : Fintype G₁ := Fintype.ofSurjective (fun r : F => r • g₁) hgen
    have hpair := smul_left_injective F hpair
    rw [Nat.card_eq_fintype_card]
    exact BLS.LazyAGM.Proofs.security g₁ g₂ A
      ⟨smul_left_injective_of_pairing g₁ g₂ hpair, hgen⟩ hpair
  have heq := KeyEquality.bls_value (F := F) (G₁ := G₁) (G₂ := G₂) (K := M) (M := M) cost
  have hw := Weights.bls_value (F := F) (G₁ := G₁) (G₂ := G₂) (K := M) (M := M) cost
  have he := fun x y => (KeyEquality.bls_steps (F := F) (G₁ := G₁) (G₂ := G₂) (K := M) (M := M) cost x y).le
  have hc := fun i m => (Weights.bls_steps (F := F) (G₁ := G₁) (G₂ := G₂) (K := M) (M := M) cost i m).le
  exact reduction.trans (add_le_add
    (add_le_add (hgoodHard _ (cert.goodWithin sampling KeyEquality.bls heq Weights.bls BLS.Proofs.indicatorWeight hw _ _ he hc))
      (hbadHard _ (cert.badWithin sampling KeyEquality.bls heq Weights.bls BLS.Proofs.indicatorWeight hw _ _ he hc))) le_rfl)

end AGM

end BLS.Statement
