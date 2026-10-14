import Signatures.Schnorr.Proofs.AGMReductionSound

/-! Preserve representation validity through the complete adaptive explained program. -/

open OracleComp OracleSpec AlgebraicGroupModel.Interaction

namespace Schnorr.AGM.Reduction

variable {F G M : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G] [DecidableEq M] [SampleableType F]

theorem handler_spec (g pk : G) (s : State F G M) (hs : s.Valid g pk)
    (q : Explained F (Request M) (Group G))
    (hq : q.Valid (representedBasis g pk s.representations))
    (reply : Message (Reply F M q.value.data) (Group G)) (t : State F G M)
    (h : (reply, t) ∈ support ((handler g pk q).run s)) :
    t.Valid g pk ∧ representedBasis g pk t.representations =
      extend (representedBasis g pk s.representations) reply.groups := by
  rcases q with ⟨⟨request, groups⟩, coeffs⟩
  cases request with
  | random n =>
      simp only [handler, StateT.run] at h
      rw [mem_support_bind_iff] at h
      obtain ⟨v, _, h⟩ := h
      simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      by_cases he : groups () = []
      · simp only [he]
        exact ⟨hs, by funext u; simp [extend]⟩
      · simp only [he]
        exact ⟨rejected_valid g pk s hs, by funext u; simp [rejected, extend]⟩
  | hash m =>
      simp only [handler, StateT.run] at h
      split at h
      · rename_i R coeff hR hcoeff
        obtain ⟨co, hco, _, heval⟩ := valid_singleton g pk R s.representations
          ⟨⟨Request.hash m, groups⟩, coeffs⟩ hq hR
        have hco' : co = coeff := List.singleton_injective (hco.symm.trans hcoeff)
        subst co
        rw [mem_support_bind_iff] at h
        obtain ⟨⟨c, st⟩, hc, h⟩ := h
        simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        have hr := read_spec g pk s hs (m, R) (flatten coeff s.representations) heval c t hc
        refine ⟨hr.1, ?_⟩
        rw [hr.2.1]
        funext u
        simp [extend, scalarReply]
      · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        exact ⟨rejected_valid g pk s hs, by funext u; simp [rejected, extend, scalarReply]⟩
  | sign m =>
      by_cases he : groups () = []
      · simp only [handler, StateT.run, he, ne_eq, not_true_eq_false, ite_false] at h
        rw [mem_support_bind_iff] at h
        obtain ⟨c, _, h⟩ := h
        rw [mem_support_bind_iff] at h
        obtain ⟨z, _, h⟩ := h
        simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        exact ⟨signedState_valid g pk s hs m c z, signedState_basis g pk s m c z⟩
      · simp only [handler, StateT.run, he, ne_eq, not_false_eq_true, ite_true,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        exact ⟨rejected_valid g pk s hs, by funext u; simp [rejected, extend, scalarReply]⟩

/-- The algebraicity certificate applies on every adaptive reply path. -/
theorem simulate_valid (g pk : G)
    (program : OracleComp (explainedSpec F (Group G) (Request M) (Reply F M))
      (Explained F (M × F) (Group G)))
    (s : State F G M) (hs : s.Valid g pk)
    (halg : IsAlgebraic (representedBasis g pk s.representations) program)
    (out : Explained F (M × F) (Group G)) (t : State F G M)
    (h : (out, t) ∈ support ((simulateQ (handler g pk) program).run s)) :
    t.Valid g pk ∧ out.Valid (representedBasis g pk t.representations) := by
  induction program using OracleComp.inductionOn generalizing s out t with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      exact ⟨hs, halg⟩
  | query_bind q next ih =>
      obtain ⟨hq, hn⟩ := (isAlgebraic_query _ _ _).mp halg
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at h
      rw [mem_support_bind_iff] at h
      obtain ⟨⟨reply, st⟩, hr, h⟩ := h
      have hstep := handler_spec g pk s hs q hq reply st hr
      exact ih reply st hstep.1 (by rw [hstep.2]; exact hn reply) out t h

/-- In the actual named reduction, every accepted nonbad run returns the secret. -/
theorem run_extract (g : G) (hg : Function.Injective (fun x : F => x • g))
    (x : F) (adv : Adversary F G M) (answer : Bool × F) (t : State F G M)
    (h : (answer, t) ∈ support (run g (x • g) adv))
    (hwin : answer.1 = true) (hbad : t.bad = false) : answer.2 = x := by
  simp only [run, StateT.run_bind] at h
  rw [mem_support_bind_iff] at h
  obtain ⟨⟨out, st⟩, hr, h⟩ := h
  have hsim := simulate_valid g (x • g) (adv.main (initial g (x • g))) {}
    (initial_valid g (x • g)) (by simpa using adv.algebraic (initial g (x • g))) out st hr
  exact finish_sound g hg x st hsim.1 out hsim.2 answer t h hwin hbad

end Schnorr.AGM.Reduction
