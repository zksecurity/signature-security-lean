import Proofs.Schnorr.AGMHonest
import Proofs.Schnorr.AGMReductionProbability

/-! Cache growth is charged only to hash and signing requests, never private draws. -/

open OracleComp OracleSpec AlgebraicGroupModel.Interaction

namespace Schnorr.AGM.Reduction

variable {F G M : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G] [DecidableEq M] [SampleableType F]

def signRequest (q : Explained F (Request M) (Group G)) : Bool :=
  match q.value.data with | .sign _ => true | _ => false

def cacheCharge (q : Explained F (Request M) (Group G)) : Nat :=
  match q.value.data with | .random _ => 0 | _ => 1

theorem handler_cacheBound (g pk : G) (s : State F G M) (k : Nat) (hk : CacheBound s k)
    (q : Explained F (Request M) (Group G))
    (reply : Message (Reply F M q.value.data) (Group G)) (t : State F G M)
    (h : (reply, t) ∈ support ((handler g pk q).run s)) :
    CacheBound t (k + cacheCharge q) := by
  rcases q with ⟨⟨request, groups⟩, coeffs⟩
  cases request with
  | random n =>
      simp only [handler, StateT.run, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at h
      obtain ⟨v, _, rfl, rfl⟩ := h
      by_cases he : groups () = []
      · simpa [cacheCharge, he] using hk
      · simpa [cacheCharge, he] using hk.rejected
  | hash m =>
      simp only [handler, StateT.run] at h
      split at h
      · rename_i R coeff hR hcoeff
        rw [mem_support_bind_iff] at h
        obtain ⟨⟨c, st⟩, hc, h⟩ := h
        simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        exact hk.read (m, R) (flatten coeff s.representations) c t hc
      · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        exact hk.rejected.mono (Nat.le_succ k)
  | sign m =>
      by_cases he : groups () = []
      · simp only [handler, StateT.run, he, ne_eq, not_true_eq_false, ite_false,
          mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h
        obtain ⟨c, _, z, _, rfl, rfl⟩ := h
        exact hk.signedState g pk m c z
      · simp only [handler, StateT.run, he, ne_eq, not_false_eq_true, ite_true,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        exact hk.rejected.mono (Nat.le_succ k)

end Schnorr.AGM.Reduction
