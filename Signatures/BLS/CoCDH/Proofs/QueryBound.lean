/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan
-/
import Signatures.BLS.CoCDH.Proofs.Coron
import Signatures.Model.CoCDH
import VCVio.OracleComp.QueryTracking.QueryBound

/-! # From the public signing-query budget to the Coron counting bound -/

open OracleComp OracleSpec AlgebraicGroupModel BLS.CoCDH.Tight

namespace BLS.CoCDH.Proofs

variable {F M G₁ : Type} [SampleableType F] [DecidableEq M]

section Counting

variable [SMul F G₁]

/-- Only signing queries can enlarge the signed-message set, by at most one. -/
theorem realOracle_step_card (g₁ X₁ : G₁) (q : (advSpec M G₁).Domain)
    (st : (M → Option F) × Finset M)
    (p : (advSpec M G₁).Range q × ((M → Option F) × Finset M))
    (hp : p ∈ support ((realOracle (F := F) g₁ X₁ q).run st)) :
    p.2.2.card ≤ st.2.card + if Sum.isRight q = true then 1 else 0 := by
  rcases q with (n | m) | m
  · simp [realOracle] at hp
    obtain ⟨u, rfl⟩ := hp
    simp
  · have h := (realOracle_hash_state g₁ X₁ m st p hp).1
    simp [h]
  · simp only [realOracle, StateT.run_bind, StateT.run_modify, StateT.run_pure,
      pure_bind, mem_support_bind_iff] at hp
    obtain ⟨r, hr, hp⟩ := hp
    have heq : p = (r.1 • X₁, r.2) := hp
    have hs := getDlogS_snd_preserved m (st.1, insert m st.2) r hr
    rw [heq]
    simpa [hs] using Finset.card_insert_le m st.2

/-- A syntactic signing-query bound controls every reachable signed-message set. Hash and
private-randomness queries are unrestricted, and duplicate signing queries still consume budget. -/
theorem signed_card_le_queryBound {B : Type} (g₁ X₁ : G₁)
    (oa : OracleComp (advSpec M G₁) B) (n : ℕ)
    (hbound : IsQueryBoundP oa (fun i => Sum.isRight i = true) n)
    (st : (M → Option F) × Finset M) (z : B × ((M → Option F) × Finset M))
    (hz : z ∈ support ((simulateQ (realOracle (F := F) g₁ X₁) oa).run st)) :
    z.2.2.card ≤ st.2.card + n := by
  induction oa using OracleComp.inductionOn generalizing n st z with
  | pure b =>
      have heq : z = (b, st) := by simpa using hz
      subst z
      simp
  | query_bind q k ih =>
      rw [isQueryBoundP_query_bind_iff] at hbound
      simp only [simulateQ_bind, StateT.run_bind, simulateQ_spec_query,
        mem_support_bind_iff] at hz
      obtain ⟨p, hp, hz⟩ := hz
      have hs := realOracle_step_card g₁ X₁ q st p hp
      have hi := ih p.1 _ (hbound.2 p.1) p.2 z hz
      by_cases hq : Sum.isRight q = true <;> simp [hq] at hs hi hbound
      · omega
      · omega

end Counting

section Security

variable {G₂ Gₜ : Type} [Field F] [Fintype F]
  [Fintype M] [AddCommGroup G₁] [Module F G₁] [SampleableType G₁] [Fintype G₁]
  [DecidableEq G₁] [AddCommGroup G₂] [Module F G₂]
  [AddCommGroup Gₜ] [Module F Gₜ] [BilinearPairing F G₁ G₂ Gₜ] [DecidableEq Gₜ]

/-- The current lazy-ROM source game is bounded by the current lazy Coron reduction, under
the syntactic query budget on generated keys. Both caches remain lazy; eager tables occur only
in the proof. -/
theorem security (g₁ : G₁) (g₂ : G₂) (qS : ℕ) (adv : TightAdvPK M G₁ G₂)
    (hgen : Function.Bijective (fun r : F => r • g₁))
    (hinj : Function.Injective (fun z : G₁ => pairing (F := F) (Gₜ := Gₜ) z g₂))
    (hqs : ∀ x : F, IsQueryBoundP (adv (x • g₂)) (fun i => Sum.isRight i = true) qS) :
    𝒟[blsEufLazyPK (F := F) (Gₜ := Gₜ) g₁ g₂ adv] {true} ≤
      Model.coronFactor qS * Model.coCDHAdvantage g₁ g₂
        (coronReductionLazyPK (F := F) qS (cacheForgeryPK adv)) := by
  rw [Model.coronFactor, Model.coCDHAdvantage, evalDist_apply_singleton, evalDist_apply_singleton]
  apply Coron.bls_eufcma_le_cocdh_coron_lazy_pk g₁ g₂ qS adv hgen hinj
  intro x out hout
  simpa using signed_card_le_queryBound g₁ (x • g₁) (adv (x • g₂)) qS
    (hqs x) ((fun _ => none), ∅) out hout

end Security

end BLS.CoCDH.Proofs
