import Signatures.Schnorr.Proofs.AGMHonest

/-! Honest instrumentation has only paths already covered by the reduction's
representation invariant. Its padded challenge is irrelevant on cache hits. -/

open OracleComp OracleSpec AlgebraicGroupModel.Interaction OracleComp.DeferredSampling

namespace Schnorr.AGM.Reduction

variable {F G M : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G] [DecidableEq M] [SampleableType F]

omit [DecidableEq F] [DecidableEq G] [DecidableEq M] [SampleableType F] in
theorem shiftedCommit (g : G) (x c r : F) :
    (r + c * x) • g - c • (x • g) = r • g := by
  rw [add_smul, mul_smul, add_sub_cancel_right]

theorem honestSign_normal (g : G) (x : F) (s : State F G M) (m : M) :
    𝒮[honestSign g x s m] = 𝒮[do
      let r ← $ᵗ F
      let c ← match s.cache (m, r • g) with
        | some e => pure e.challenge
        | none => $ᵗ F
      pure (signingOutput g (x • g) s m c (r + c * x))] := by
  rw [honestSign, evalSPMF_bind_comm]
  apply evalSPMF_bind_congr_left
  intro r
  cases hc : s.cache (m, r • g) with
  | none => simp only [Option.map_none, Option.getD_none]
  | some e =>
      simp only [Option.map_some, Option.getD_some, pure_bind]
      exact evalSPMF_bind_const_neverFails ($ᵗ F) (by simp) _

theorem honestSign_support (g : G) (x : F) (s : State F G M) (m : M)
    (p : Message F (Group G) × State F G M) (hp : p ∈ support (honestSign g x s m)) :
    p ∈ support (simulatedSign g (x • g) s m) := by
  simp only [honestSign, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hp
  obtain ⟨c, _, r, _, rfl⟩ := hp
  simp only [simulatedSign, mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
  exact ⟨_, by simp, _, by simp, rfl⟩

set_option backward.isDefEq.respectTransparency false in
theorem honestHandler_support (g : G) (x : F) (s : State F G M)
    (q : Explained F (Request M) (Group G))
    (p : Message (Reply F M q.value.data) (Group G) × State F G M)
    (hp : p ∈ support ((honestHandler g x q).run s)) :
    p ∈ support ((handler g (x • g) q).run s) := by
  rcases q with ⟨⟨request, groups⟩, coeffs⟩
  cases request with
  | random n => exact hp
  | hash m => exact hp
  | sign m =>
      by_cases he : groups () = []
      · simp only [honestHandler, handler, StateT.run, he, ne_eq, not_true_eq_false,
          ite_false] at hp ⊢
        exact honestSign_support g x s m p hp
      · change p ∈ support (if groups () ≠ [] then pure (scalarReply (0 : F), rejected s)
          else honestSign g x s m) at hp
        rw [if_pos he] at hp
        simpa only [handler, StateT.run, if_pos he] using hp

theorem honestSimulate_support {A : Type} (g : G) (x : F)
    (program : OracleComp (explainedSpec F (Group G) (Request M) (Reply F M)) A)
    (s : State F G M) (p : A × State F G M)
    (hp : p ∈ support ((simulateQ (honestHandler g x) program).run s)) :
    p ∈ support ((simulateQ (handler g (x • g)) program).run s) := by
  induction program using OracleComp.inductionOn generalizing s p with
  | pure a => exact hp
  | query_bind q next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        mem_support_bind_iff] at hp ⊢
      obtain ⟨⟨reply, st⟩, hr, hp⟩ := hp
      exact ⟨(reply, st), honestHandler_support g x s q (reply, st) hr, ih reply st p hp⟩

end Schnorr.AGM.Reduction
