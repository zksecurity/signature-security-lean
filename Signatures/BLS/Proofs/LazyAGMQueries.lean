import Signatures.BLS.Spec.LazyAGMReduction
import VCVio.OracleComp.QueryTracking.QueryBound

/-! Structural query and transcript bounds for the actual lazy AGM programs.
These bounds do not price local computation or encode a runtime certificate;
they supply finite loop/cache bounds for that later compilation. -/

open OracleComp OracleSpec Model.LazyAGM

namespace BLS.LazyAGM.Reduction

variable {F M R G₁ G₂ α : Type}

theorem privateSim_queries (hash sign : R → G₁)
    (oa : OracleComp (advSpec M M G₁) α) (tr : Transcript M M G₁) (q : Nat)
    (hq : IsTotalQueryBound oa q) :
    IsTotalQueryBound ((simulateQ (privateOracle hash sign) oa).run tr) q := by
  apply IsTotalQueryBound.simulateQ_run_of_step hq
  intro query tr
  rcases query with ((n | m) | m) <;>
    simp [privateOracle, handler, IsTotalQueryBound]

theorem privateSim_transcript (hash sign : R → G₁)
    (oa : OracleComp (advSpec M M G₁) α) (tr : Transcript M M G₁) (q : Nat)
    (hq : IsTotalQueryBound oa q) (z : α × Transcript M M G₁)
    (hz : z ∈ support ((simulateQ (privateOracle hash sign) oa).run tr)) :
    z.2.1.length + z.2.2.length ≤ tr.1.length + tr.2.length + q := by
  induction oa using OracleComp.inductionOn generalizing q tr with
  | pure a =>
    have he : z = (a, tr) := by simpa using hz
    subst z
    simp
  | query_bind query next ih =>
    rw [isTotalQueryBound_query_bind_iff] at hq
    rcases query with ((n | m) | m) <;>
      simp [privateOracle, handler, StateT.run_bind] at hz
    · obtain ⟨r, hr⟩ := hz
      have hb := ih r tr (q - 1) (hq.2 r) hr
      omega
    · obtain ⟨r, hr⟩ := hz
      have hb := ih (hash r) (tr.1 ++ [(m, hash r)], tr.2) (q - 1) (hq.2 (hash r)) hr
      simp only [List.length_append, List.length_singleton] at hb
      omega
    · obtain ⟨r, hr⟩ := hz
      have hb := ih (sign r) (tr.1, tr.2 ++ [(m, sign r)]) (q - 1) (hq.2 (sign r)) hr
      simp only [List.length_append, List.length_singleton] at hb
      omega

theorem privateRun_queries (hash sign : R → G₁) (A : Adversary F M M G₁ G₂)
    (pk : G₂) (q : Nat) (hq : IsTotalQueryBound (A.main pk) q) :
    IsTotalQueryBound (privateRun hash sign A pk) q :=
  privateSim_queries hash sign (A.main pk) ([], []) q hq

theorem privateRun_transcript (hash sign : R → G₁) (A : Adversary F M M G₁ G₂)
    (pk : G₂) (q : Nat) (hq : IsTotalQueryBound (A.main pk) q)
    (z : Output F M × Transcript M M G₁) (hz : z ∈ support (privateRun hash sign A pk)) :
    z.2.1.length + z.2.2.length ≤ q := by
  simpa using privateSim_transcript hash sign (A.main pk) ([], []) q hq z hz

theorem evalTerms_queries [AddCommMonoid R] [SMul F R] (terms : List (M × F)) :
    IsTotalQueryBound (evalTerms (G₁ := R) terms) terms.length := by
  induction terms with
  | nil => trivial
  | cons p rest ih =>
    simp only [evalTerms, List.length_cons, isTotalQueryBound_query_bind_iff]
    refine ⟨by omega, fun sampled => ?_⟩
    rw [Nat.add_sub_cancel, bind_pure_comp]
    exact (isQueryBound_map_iff (evalTerms rest) (fun r => p.2 • sampled + r)
      rest.length _ _).2 ih

variable [Field F] [AddCommGroup G₁] [Module F G₁]

/-- At most two private-interface requests per attacker request, plus the final
target. This counts forwarded randomness and cache hits as requests too. -/
theorem goodProgram_queries (g X : G₁) (pk : G₂) (A : Adversary F M M G₁ G₂)
    (q : Nat) (hq : IsTotalQueryBound (A.main pk) q) :
    IsTotalQueryBound (goodProgram g X pk A) (2 * q + 1) := by
  unfold goodProgram
  apply (isTotalQueryBound_bind_of_mem_support
    (privateRun_queries (fun r : F => r • g) (fun r => r • X) A pk q hq)
    (suffixBound := q + 1) ?_).mono (by omega)
  rintro ⟨out, tr⟩ hz
  have htr := privateRun_transcript (fun r : F => r • g) (fun r => r • X) A pk q hq _ hz
  dsimp only at htr
  have ht := isTotalQueryBound_bind (evalTerms_queries (R := F) (traceTerms out.γ tr.1))
    (fun hashes => isTotalQueryBound_bind (evalTerms_queries (R := F) (traceTerms out.ξ tr.2))
      (fun signatures => show IsTotalQueryBound (do
        let target ← (liftM ((baseSpec M F).query (.inr out.mstar)) : OracleComp (baseSpec M F) F)
        pure ((out.β + hashes) / (target - signatures))) 1 from by
          simp [IsTotalQueryBound]))
  apply ht.mono
  simp only [traceTerms, List.length_mapIdx]
  omega

theorem badProgram_queries (g X : G₁) (pk : G₂) (kappa : F) (A : Adversary F M M G₁ G₂)
    (q : Nat) (hq : IsTotalQueryBound (A.main pk) q) :
    IsTotalQueryBound (badProgram g X pk kappa A) (2 * q + 1) := by
  unfold badProgram
  apply (isTotalQueryBound_bind_of_mem_support
    (privateRun_queries (fun masks : F × F => masks.1 • X + masks.2 • g)
      (fun masks => kappa • (masks.1 • X + masks.2 • g)) A pk q hq)
    (suffixBound := q + 1) ?_).mono (by omega)
  rintro ⟨out, tr⟩ hz
  have htr := privateRun_transcript (fun masks : F × F => masks.1 • X + masks.2 • g)
    (fun masks => kappa • (masks.1 • X + masks.2 • g)) A pk q hq _ hz
  dsimp only at htr
  have ht := isTotalQueryBound_bind (evalTerms_queries (R := F × F) (traceTerms out.ξ tr.2))
    (fun signatures => show IsTotalQueryBound (do
      let target ← (liftM ((baseSpec M (F × F)).query (.inr out.mstar)) :
        OracleComp (baseSpec M (F × F)) (F × F))
      pure (-(target.2 - signatures.2) / (target.1 - signatures.1))) 1 from by
        simp [IsTotalQueryBound])
  apply ht.mono
  simp only [traceTerms, List.length_mapIdx]
  omega

end BLS.LazyAGM.Reduction
