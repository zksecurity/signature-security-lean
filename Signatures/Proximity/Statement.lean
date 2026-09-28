/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan
-/
import Signatures.Proximity.Proofs.LazyAGM
import Signatures.Runtime.AGMBadMachine
import Signatures.Runtime.KeyEquality
import Signatures.Runtime.ProximityWeight
import Signatures.Model.Hardness

/-! Concrete machine-bounded Proximity security; source games and reduction lemmas are unchanged. -/

open OracleComp AlgebraicGroupModel
open Signatures.Runtime Signatures.Runtime.AGM
open scoped ENNReal

namespace Proximity.Statement

variable {F S G₁ G₂ Gₜ : Type} [Field F] [SampleableType F]
  [DecidableEq F] [Fintype S] [DecidableEq S] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
  [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
  [BilinearPairing F G₁ G₂ Gₜ]

/-- Proximity AGM with structural vector encoding, charged coordinate reads, and
both complete solver budgets. Fresh collisions contribute their actual source-game probability. -/
-- This is the machine-bounded security endpoint; no separate unbounded wrapper is exposed.
theorem proximity_lazy_agm_of_dlog_machine_hardness
    -- Fix public base points and the number ell of message-vector coordinates.
    (g₁ : G₁) (g₂ : G₂) (ell : Nat)
    -- A queries constant/coordinate hashes and signs vector/slot pairs, returning an algebraic forgery.
    {A : Model.LazyAGM.Adversary F (Option (Fin ell) × S) ((Fin ell → F) × S) G₁ G₂}
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
    -- Supply executable source code, all-key semantic equality to A, and all-path resource bounds.
    (cert : SourceCertificate (F := F) (K := S) (M := S)
      -- Encode hash indices and signed messages as these first-order machine types.
      (indexTy := Weights.proximityKey ell) (messageTy := Weights.proximityTupleMessage ell)
      -- These equivalences connect the source's machine values to the game's index/message types.
      cost (Weights.proximityKeyEquiv ell) (Weights.proximityMessageEquiv ell)
      -- The certificate fixes these inferred resource indices for this exact adversary.
      randomBound localTime queries gammaLength xiLength A)
    -- Allow separate assumed success bounds for the two DLog reductions.
    (goodEpsilon badEpsilon : ENNReal)
    -- Assume every DLog solver in the following machine class and budget has success <= goodEpsilon...
    (hgoodHard : Model.HardWithin (Model.dlog11Advantage g₁ g₂)
      -- ...for recovering x from (g1,x*g1,g2,x*g2), with these arithmetic/sampling prices...
      (dlogWithin (F := F) (K := S) (M := S) cost sampling)
      -- ...at the derived good-solver budget, including queries, local work, and private-table setup.
      (cert.goodBudget sampling (cost.keyEq + 3 * cost.natOp + 17)
        -- Include the dimension-dependent cost of reading and weighting vector coordinates.
        (Weights.proximityTupleBound cost ell)) goodEpsilon)
    -- Make the analogous assumption for the bad-branch budget and badEpsilon...
    (hbadHard : Model.HardWithin (Model.dlog11Advantage g₁ g₂)
      -- ...for recovering x from (g1,x*g1,g2,x*g2), with these arithmetic/sampling prices...
      (dlogWithin (F := F) (K := S) (M := S) cost sampling)
      -- ...at the derived bad-solver budget, which also charges its masked-base construction.
      (cert.badBudget sampling (cost.keyEq + 3 * cost.natOp + 17)
        -- Include the dimension-dependent cost of reading and weighting vector coordinates.
        (Weights.proximityTupleBound cost ell)) badEpsilon) :
    -- Probability of a valid fresh vector/slot forgery; collisions are not rejected by the game.
    𝒟[Proximity.LazyAGM.game (Gₜ := Gₜ) g₁ g₂ A] {true} ≤
      -- Add both hardness bounds and retain the residual 1/|F| term; neither branch is omitted.
      goodEpsilon + badEpsilon + 1 / (Nat.card F : ENNReal) +
      -- Actual probability of a fresh output vector equaling its signed-vector combination.
      -- This is measured in the same lazy interaction, not assumed zero or negligible.
      𝒟[Proximity.LazyAGM.collisionGame g₂ A] {true} := by
  have reduction :
      𝒟[Proximity.LazyAGM.game (Gₜ := Gₜ) g₁ g₂ A] {true} ≤
        Model.dlog11Advantage g₁ g₂ (Model.LazyAGM.goodReduction (Proximity.Proofs.coordinateWeight ell) A) +
        Model.dlog11Advantage g₁ g₂ (Model.LazyAGM.badReduction (Proximity.Proofs.coordinateWeight ell) A) +
        1 / (Nat.card F : ENNReal) + 𝒟[Proximity.LazyAGM.collisionGame g₂ A] {true} := by
    classical
    let : Fintype F := Fintype.ofFinite F
    let : Fintype G₁ := Fintype.ofSurjective (fun r : F => r • g₁) hgen
    have hpair := smul_left_injective F hpair
    rw [Nat.card_eq_fintype_card]
    exact Proximity.LazyAGM.Proofs.security g₁ g₂ A
      ⟨smul_left_injective_of_pairing g₁ g₂ hpair, hgen⟩ hpair
  have heq := KeyEquality.proximity_value (F := F) (G₁ := G₁) (G₂ := G₂) (K := S) (M := S) cost ell
  have hw := Weights.proximityTuple_decoded (F := F) (G₁ := G₁) (G₂ := G₂) (K := S) (M := S) cost ell
  have he := KeyEquality.proximity_steps_le (F := F) (G₁ := G₁) (G₂ := G₂) (K := S) (M := S) cost ell
  have hc := Weights.proximityTuple_steps_le (F := F) (G₁ := G₁) (G₂ := G₂) (K := S) (M := S) cost ell
  exact reduction.trans (add_le_add (add_le_add
    (add_le_add (hgoodHard _ (cert.goodWithin sampling (KeyEquality.proximity ell) heq (Weights.proximityTuple ell)
      (Proximity.Proofs.coordinateWeight ell) hw _ _ he hc))
      (hbadHard _ (cert.badWithin sampling (KeyEquality.proximity ell) heq (Weights.proximityTuple ell)
      (Proximity.Proofs.coordinateWeight ell) hw _ _ he hc))) le_rfl) le_rfl)

end Proximity.Statement
