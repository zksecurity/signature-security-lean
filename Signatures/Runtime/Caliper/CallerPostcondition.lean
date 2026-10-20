import Signatures.Runtime.Caliper.CallerControl

/-! Store invariants at every supported caller exit, including early return and
fuel cutoff. Unlike a pending-state invariant, this postcondition is retained
when the caller returns its result and a subsequent phase uses the store. -/

namespace Signatures.Runtime.CaliperBackend.CallerControl
open OracleComp OracleSpec

variable {I C Q R B S : Type} {spec : OracleSpec I}
    (advance : C × R → B ⊕ (Q × C)) (H : Q × S → OracleComp spec (R × S))

theorem start_store (invariant : Nat → S → Prop)
    (weaken : ∀ small large saved, small ≤ large → invariant large saved → invariant small saved)
    (step : ∀ remaining q saved, invariant (remaining + 1) saved →
      ∀ reply ∈ support (H (q, saved)), invariant remaining reply.2)
    (fuel : Nat) (value : Packet C Q B S) (valid : invariant fuel value.2)
    (answer : Packet C Q B S) (reached : answer ∈ support (start advance H fuel value)) :
    invariant 0 answer.2 := by
  induction fuel generalizing value answer with
  | zero =>
    rcases value with ⟨result | pending, saved⟩ <;>
      simp only [start, denote_zero, suspended, support_pure, Set.mem_singleton_iff] at reached <;>
      subst answer <;> exact valid
  | succ fuel ih =>
    rcases value with ⟨result | pending, saved⟩
    · simp only [start, support_pure, Set.mem_singleton_iff] at reached
      subst answer
      exact weaken 0 (fuel + 1) saved (Nat.zero_le _) valid
    · change answer ∈ support (denote advance H (fuel + 1) (pending, saved)) at reached
      rw [denote_succ, mem_support_bind_iff] at reached
      obtain ⟨reply, supported, reached⟩ := reached
      exact ih (advance (pending.2, reply.1), reply.2)
        (step fuel pending.1 saved valid reply supported) answer reached

/-- A store postcondition retained at returns and cutoffs when handler admission
depends on the pending caller state, rather than on the private store alone. -/
theorem start_store_on (invariant : Nat → Frame C Q S → Prop)
    (preserves : ∀ remaining value, invariant (remaining + 1) value →
      ∀ reply ∈ support (H (value.1.1, value.2)), Valid invariant remaining (advance (value.1.2, reply.1), reply.2))
    (post : S → Prop)
    (step : ∀ remaining value, invariant (remaining + 1) value → post value.2 →
      ∀ reply ∈ support (H (value.1.1, value.2)), post reply.2)
    (fuel : Nat) (value : Packet C Q B S) (valid : Valid invariant fuel value) (stored : post value.2)
    (answer : Packet C Q B S) (reached : answer ∈ support (start advance H fuel value)) : post answer.2 := by
  induction fuel generalizing value answer with
  | zero =>
      rcases value with ⟨result | pending, saved⟩ <;>
        simp only [start, denote_zero, suspended, support_pure, Set.mem_singleton_iff] at reached <;>
        subst answer <;> exact stored
  | succ fuel ih =>
      rcases value with ⟨result | pending, saved⟩
      · simp only [start, support_pure, Set.mem_singleton_iff] at reached
        subst answer
        exact stored
      · change answer ∈ support (denote advance H (fuel + 1) (pending, saved)) at reached
        rw [denote_succ, mem_support_bind_iff] at reached
        obtain ⟨reply, supported, reached⟩ := reached
        exact ih (advance (pending.2, reply.1), reply.2)
          (preserves fuel (pending, saved) valid reply supported)
          (step fuel (pending, saved) valid stored reply supported) answer reached

end Signatures.Runtime.CaliperBackend.CallerControl
