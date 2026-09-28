/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan
-/
import Signatures.BLS.CoCDH.Spec.LazyGame

/-! # Cache invariants for the lazy BLS source game -/

open OracleComp OracleSpec AlgebraicGroupModel
namespace BLS.CoCDH.Tight

variable {F M G₁ : Type} [SampleableType F] [DecidableEq M] [SMul F G₁]

/-- Explicit run equation for the lazy discrete-log lookup. -/
lemma getDlogS_run (m : M) (st : (M → Option F) × Finset M) :
    (getDlogS (F := F) m).run st = (match st.1 m with
      | some ρ => pure (ρ, st)
      | none => ($ᵗ F) >>= fun ρ => pure (ρ, (Function.update st.1 m (some ρ), st.2))) := by
  cases hc : st.1 m with
  | some ρ =>
      simp only [getDlogS, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, hc]
  | none =>
      simp only [getDlogS, StateT.run_bind, StateT.run_get, StateT.run_monadLift, StateT.run_modify,
        StateT.run_pure, pure_bind, bind_assoc, hc]
      rfl

/-- Lookup preserves the signing set and caches exactly the scalar it returns. -/
lemma getDlogS_state (m : M) (st : (M → Option F) × Finset M)
    (z : F × ((M → Option F) × Finset M))
    (hz : z ∈ support ((getDlogS (F := F) m).run st)) :
    z.2.2 = st.2 ∧ z.2.1 m = some z.1 := by
  rw [getDlogS_run] at hz
  cases hc : st.1 m with
  | some ρ =>
      simp only [hc, mem_support_pure_iff] at hz
      subst z
      exact ⟨rfl, hc⟩
  | none =>
      simp only [hc, mem_support_bind_iff, mem_support_pure_iff] at hz
      obtain ⟨ρ, _, rfl⟩ := hz
      simp

lemma getDlogS_snd_preserved (m : M) (st : (M → Option F) × Finset M)
    (z : F × ((M → Option F) × Finset M))
    (hz : z ∈ support ((getDlogS (F := F) m).run st)) : z.2.2 = st.2 :=
  (getDlogS_state m st z hz).1

/-- Hashing preserves the signing set and leaves its message cached. -/
lemma realOracle_hash_state (g₁ X₁ : G₁) (m : M)
    (st : (M → Option F) × Finset M) :
    ∀ z ∈ support ((realOracle (F := F) g₁ X₁ (Sum.inl (Sum.inr m))).run st),
      z.2.2 = st.2 ∧ (z.2.1 m).isSome := by
  intro z hz
  simp only [realOracle, StateT.run_bind, StateT.run_pure, support_bind, support_pure,
    Set.mem_iUnion, Set.mem_singleton_iff] at hz
  obtain ⟨p, hp, hz⟩ := hz
  subst hz
  obtain ⟨hsigned, hcache⟩ := getDlogS_state m st p hp
  exact ⟨hsigned, by simp [hcache]⟩

end BLS.CoCDH.Tight
