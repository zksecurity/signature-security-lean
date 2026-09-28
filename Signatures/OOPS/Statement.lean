/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan
-/
import Signatures.OOPS.Proofs.LazyAGM
import Signatures.Runtime.AGMBadMachine
import Signatures.Runtime.KeyEquality
import Signatures.Runtime.ProximityWeight
import Signatures.Model.Hardness

/-! Concrete machine-bounded OOPS security; source games and reduction lemmas are unchanged. -/

open OracleComp AlgebraicGroupModel
open Signatures.Runtime Signatures.Runtime.AGM
open scoped ENNReal

namespace OOPS.Statement

variable {F T G₁ G₂ Gₜ : Type} [Field F] [SampleableType F]
  [DecidableEq F] [Fintype T] [DecidableEq T] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
  [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
  [BilinearPairing F G₁ G₂ Gₜ]

/-- OOPS AGM with charged degree-dependent weights and both complete solver budgets.
The game's original target-topic distinct-message restriction remains unchanged. -/
-- This is the machine-bounded security endpoint; no separate unbounded wrapper is exposed.
theorem oops_lazy_agm_of_dlog_machine_hardness
    -- Fix public base points and one degree d for the entire game, not a degree per query.
    (g₁ : G₁) (g₂ : G₂) (d : Nat)
    -- A queries topic/degree hashes and signs scalar/topic pairs, returning an algebraic forgery.
    {A : Model.LazyAGM.Adversary F (T × Fin (d + 1)) (F × T) G₁ G₂}
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
    (cert : SourceCertificate (F := F) (K := T) (M := T)
      -- Encode hash indices and signed messages as these first-order machine types.
      (indexTy := Weights.oopsKey d) (messageTy := Weights.oopsMessage)
      -- These equivalences connect the source's machine values to the game's index/message types.
      cost (Equiv.refl (T × Fin (d + 1))) (Equiv.refl (F × T))
      -- The certificate fixes these inferred resource indices for this exact adversary.
      randomBound localTime queries gammaLength xiLength A)
    -- Allow separate assumed success bounds for the two DLog reductions.
    (goodEpsilon badEpsilon : ENNReal)
    -- Assume every DLog solver in the following machine class and budget has success <= goodEpsilon...
    (hgoodHard : Model.HardWithin (Model.dlog11Advantage g₁ g₂)
      -- ...for recovering x from (g1,x*g1,g2,x*g2), with these arithmetic/sampling prices...
      (dlogWithin (F := F) (K := T) (M := T) cost sampling)
      -- ...at the derived good-solver budget, including queries, local work, and private-table setup.
      (cert.goodBudget sampling (cost.keyEq + 3 * cost.natOp + 17) (Weights.oopsBound cost d)) goodEpsilon)
    -- Make the analogous assumption for the bad-branch budget and badEpsilon...
    (hbadHard : Model.HardWithin (Model.dlog11Advantage g₁ g₂)
      -- ...for recovering x from (g1,x*g1,g2,x*g2), with these arithmetic/sampling prices...
      (dlogWithin (F := F) (K := T) (M := T) cost sampling)
      -- ...at the derived bad-solver budget, which also charges its masked-base construction.
      (cert.badBudget sampling (cost.keyEq + 3 * cost.natOp + 17) (Weights.oopsBound cost d)) badEpsilon) :
    -- Probability of a valid fresh scalar/topic forgery, with <= d distinct signed messages on
    -- its topic. This per-topic winning condition is separate from the total signing-call budget.
    𝒟[OOPS.LazyAGM.game (Gₜ := Gₜ) g₁ g₂ d A] {true} ≤
      -- Add both hardness bounds and retain the residual 1/|F| term; neither branch is omitted.
      -- Freshness and the winning degree rule guarantee a nonzero coefficient by Vandermonde.
      -- The expression can still evaluate to zero: the hidden-slope collision costs 1/|F|.
      goodEpsilon + badEpsilon + 1 / (Nat.card F : ENNReal) := by
  have reduction :
      𝒟[OOPS.LazyAGM.game (Gₜ := Gₜ) g₁ g₂ d A] {true} ≤
        Model.dlog11Advantage g₁ g₂ (Model.LazyAGM.goodReduction (OOPS.Handle.oopsWMulti d) A) +
        Model.dlog11Advantage g₁ g₂ (Model.LazyAGM.badReduction (OOPS.Handle.oopsWMulti d) A) +
        1 / (Nat.card F : ENNReal) := by
    classical
    let : Fintype F := Fintype.ofFinite F
    let : Fintype G₁ := Fintype.ofSurjective (fun r : F => r • g₁) hgen
    have hpair := smul_left_injective F hpair
    rw [Nat.card_eq_fintype_card]
    exact OOPS.LazyAGM.Proofs.security g₁ g₂ d A
      ⟨smul_left_injective_of_pairing g₁ g₂ hpair, hgen⟩ hpair
  have heq := KeyEquality.oops_value (F := F) (G₁ := G₁) (G₂ := G₂) (K := T) (M := T) cost d
  have hw := Weights.oops_value (F := F) (G₁ := G₁) (G₂ := G₂) (K := T) (M := T) cost d
  have he := KeyEquality.oops_steps_le (F := F) (G₁ := G₁) (G₂ := G₂) (K := T) (M := T) cost d
  have hc := Weights.oops_steps_le (F := F) (G₁ := G₁) (G₂ := G₂) (K := T) (M := T) cost d
  exact reduction.trans (add_le_add
    (add_le_add (hgoodHard _ (cert.goodWithin sampling (KeyEquality.oops d) heq (Weights.oops d) (OOPS.Handle.oopsWMulti d) hw _ _ he hc))
      (hbadHard _ (cert.badWithin sampling (KeyEquality.oops d) heq (Weights.oops d) (OOPS.Handle.oopsWMulti d) hw _ _ he hc))) le_rfl)

end OOPS.Statement
