import Proofs.Runtime.BackendBudget

/-! Native iteration bounds with an invariant indexed by the remaining
iterations. This permits counters and caches to grow within a fixed total cap
without assuming that one more iteration is valid after the loop finishes. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {I : Type} {spec : OracleSpec I} {iface : Interface (C := C) spec}
  (control : ControlCosts) (queryCost : (i : I) → spec.Range i → Nat)

theorem iterationRun_bound_remaining {S : Type} (inv : Nat → S → Prop)
    (fee : Nat → S → Nat) (body : S → OracleComp spec (Run S))
    (bodyTime tickTime cap : Nat)
    (hb : ∀ remaining < cap, ∀ state, inv (remaining + 1) state →
      ∀ z ∈ support (body state), inv remaining z.value ∧ z.steps ≤ bodyTime)
    (hc : ∀ remaining ≤ cap, ∀ state, inv remaining state → fee remaining state ≤ tickTime)
    (count : Nat) (hcount : count ≤ cap) (state : S) (hi : inv count state) (z : Run S)
    (hz : z ∈ support (iterationRun fee body count state)) :
    inv 0 z.value ∧ z.steps ≤ count * (bodyTime + tickTime) + tickTime := by
  induction count generalizing state z with
  | zero =>
      simp only [iterationRun, support_pure, Set.mem_singleton_iff] at hz
      subst z
      exact ⟨hi, by simpa using hc 0 hcount state hi⟩
  | succ count ih =>
      simp only [iterationRun, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨step, hstep, rest, hrest, rfl⟩ := hz
      obtain ⟨hinv, ht⟩ := hb count (by omega) state hi step hstep
      obtain ⟨hout, hu⟩ := ih (by omega) step.value hinv rest hrest
      have hfee := hc (count + 1) hcount state hi
      exact ⟨hout, by dsimp; nlinarith⟩

theorem Bounds.iterate_remaining {S : Type} {s : C.Str S} (counter : C.Str Nat)
    (body : Code Q spec iface s s) (inv : Nat → S → Prop) (bodyTime tickTime cap : Nat)
    (hb : ∀ remaining < cap, Bounds control queryCost body
      (inv (remaining + 1)) (inv remaining) bodyTime)
    (hc : ∀ remaining ≤ cap, ∀ state, inv remaining state → control.loop remaining
      (Q.size (StepClass.HasProd.prod counter s) (remaining, state)) ≤ tickTime) :
    Bounds control queryCost (.iterate counter body)
      (fun p => p.1 ≤ cap ∧ inv p.1 p.2) (inv 0)
      (cap * (bodyTime + tickTime) + tickTime) := by
  intro input hp z hz
  obtain ⟨hout, ht⟩ := iterationRun_bound_remaining inv _ _ bodyTime tickTime cap hb hc
    input.1 hp.1 input.2 hp.2 z hz
  exact ⟨hout, ht.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hp.1) _)⟩

end Signatures.Runtime.BackendProgram
