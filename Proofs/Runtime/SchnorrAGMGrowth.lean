import Proofs.Runtime.SchnorrAGMExecution
import Proofs.Schnorr.AGMCacheGrowth

/-! Storage capacity of the actual finite-list Schnorr AGM state. The bounds
count hash/sign queries and the final target, independently of the message or
group domain cardinality. They do not yet bound encoded byte sizes or runtime. -/

open OracleComp OracleSpec AlgebraicGroupModel.Interaction Schnorr.AGM

namespace Signatures.Runtime.SchnorrAGM

variable {F G M : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G] [DecidableEq M] [SampleableType F]

theorem handler_growth (g pk : G) (s : State F G M)
    (q : Explained F (Request M) (Group G))
    (p : Message (Reply F M q.value.data) (Group G) × State F G M)
    (hp : p ∈ support ((handler g pk q).run s)) :
    p.2.cache.length ≤ s.cache.length + Reduction.cacheCharge q ∧
      p.2.representations.length ≤ s.representations.length + (if Reduction.signRequest q then 1 else 0) ∧
      p.2.signed.length ≤ s.signed.length + (if Reduction.signRequest q then 1 else 0) := by
  rcases q with ⟨⟨request, groups⟩, coefficients⟩
  cases request with
  | random n =>
      simp only [handler, StateT.run, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at hp
      obtain ⟨v, _, rfl⟩ := hp
      by_cases h : groups () = [] <;>
        simp [Reduction.cacheCharge, Reduction.signRequest, h, rejected]
  | hash m =>
      simp only [handler, StateT.run] at hp
      split at hp
      · rename_i R coeff hg hc
        simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hp
        obtain ⟨t, ht, rfl⟩ := hp
        obtain ⟨hcache, hreps, hsigned⟩ := read_growth (m, R) (flatten coeff s.representations) s t ht
        exact ⟨hcache, by simp [Reduction.signRequest, hreps],
          by simp [Reduction.signRequest, hsigned]⟩
      · simp only [support_pure, Set.mem_singleton_iff] at hp
        cases hp
        simp [Reduction.cacheCharge, Reduction.signRequest, rejected]
  | sign m =>
      by_cases h : groups () = []
      · simp only [handler, StateT.run, h, ne_eq, not_true_eq_false, ite_false,
          mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hp
        obtain ⟨c, _, z, _, rfl⟩ := hp
        obtain ⟨hcache, hreps, hsigned⟩ := signedState_growth s g pk m c z
        exact ⟨hcache, hreps.le, hsigned.le⟩
      · simp only [handler, StateT.run, h, ne_eq, not_false_eq_true, ite_true,
          support_pure, Set.mem_singleton_iff] at hp
        cases hp
        simp [Reduction.cacheCharge, Reduction.signRequest, rejected]

/-- Bounds follow every actual adaptive path; private randomness consumes no cache capacity. -/
theorem simulate_growth {A : Type} (g pk : G)
    (program : OracleComp (explainedSpec F (Group G) (Request M) (Reply F M)) A)
    (qS qH : Nat)
    (hS : IsQueryBoundP program (fun q => Reduction.signRequest q = true) qS)
    (hH : IsQueryBoundP program (fun q => Reduction.hashRequest q = true) qH)
    (s : State F G M) (p : A × State F G M)
    (hp : p ∈ support ((simulateQ (handler g pk) program).run s)) :
    p.2.cache.length ≤ s.cache.length + qS + qH ∧
      p.2.representations.length ≤ s.representations.length + qS ∧
      p.2.signed.length ≤ s.signed.length + qS := by
  induction program using OracleComp.inductionOn generalizing qS qH s with
  | pure a =>
      have he : p = (a, s) := by simpa using hp
      subst p
      dsimp only
      exact ⟨by omega, by omega, by omega⟩
  | query_bind q next ih =>
      rw [isQueryBoundP_query_bind_iff] at hS hH
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hp
      obtain ⟨mid, hmid, hp⟩ := hp
      obtain ⟨hcache, hreps, hsigned⟩ := handler_growth g pk s q mid hmid
      obtain ⟨htcache, htreps, htsigned⟩ := ih mid.1 _ _ (hS.2 mid.1) (hH.2 mid.1) mid.2 hp
      cases hq : q.value.data <;>
        simp [Reduction.cacheCharge, Reduction.signRequest, Reduction.hashRequest, hq] at hcache hreps hsigned htcache htreps htsigned hS hH <;>
        exact ⟨by omega, by omega, by omega⟩

theorem finish_growth (g pk : G) (out : Explained F (M × F) (Group G))
    (s : State F G M) (p : (Bool × F) × State F G M)
    (hp : p ∈ support ((finish g pk out).run s)) :
    p.2.cache.length ≤ s.cache.length + 1 ∧
      p.2.representations = s.representations ∧ p.2.signed = s.signed := by
  simp only [finish] at hp
  split at hp
  · rename_i R coeff hg hc
    simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind,
      mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hp
    obtain ⟨mid, hmid, rfl⟩ := hp
    exact read_growth (out.value.data.1, R) (flatten coeff s.representations) s mid hmid
  · have he : p = ((false, 0), s) := by simpa using hp
    subst p
    exact ⟨Nat.le_succ _, rfl, rfl⟩

/-- The whole reduction stores at most `qS + qH + 1` encountered pairs, at most
`qS + 2` affine basis entries, and at most `qS` signed-message entries. -/
theorem run_growth (g pk : G) (adv : Adversary F G M) (qS qH : Nat)
    (hS : IsQueryBoundP (adv.main (initial g pk)) (fun q => Reduction.signRequest q = true) qS)
    (hH : IsQueryBoundP (adv.main (initial g pk)) (fun q => Reduction.hashRequest q = true) qH)
    (p : (Bool × F) × State F G M) (hp : p ∈ support (run g pk adv)) :
    p.2.cache.length ≤ qS + qH + 1 ∧
      p.2.representations.length ≤ qS + 2 ∧ p.2.signed.length ≤ qS := by
  simp only [run, StateT.run_bind, mem_support_bind_iff] at hp
  obtain ⟨mid, hmid, hp⟩ := hp
  obtain ⟨hcache, hreps, hsigned⟩ := simulate_growth g pk _ qS qH hS hH {} mid hmid
  obtain ⟨htcache, htreps, htsigned⟩ := finish_growth g pk mid.1 mid.2 p hp
  simp only [List.length_nil, initialRepresentations, List.length_cons, Nat.zero_add] at hcache hreps hsigned
  rw [htreps, htsigned]
  exact ⟨by omega, by omega, hsigned⟩

end Signatures.Runtime.SchnorrAGM
