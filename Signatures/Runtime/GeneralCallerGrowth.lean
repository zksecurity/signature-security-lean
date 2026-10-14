import Signatures.Runtime.GeneralCallerBudget
import Signatures.Runtime.GeneralCallerRefinement

/-! Growing-storage bounds for general oracle callers. The caller's symbolic
price certificate bounds actual state growth, including repeated requests.
Linear cache scans give quadratic overhead without a final-state-size premise. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.GeneralCaller

variable {I A B : Type} {spec : OracleSpec I}
  {C : StepClass} [C.HasProd] [C.HasSum] [C.HasOption]
  [DecidableEq I] {Q : QuantitativeStepClass C}
  {bd : Boundary C spec.toPFunctor A B}
  (R : Caller (Q := Q) (bd := bd))
  {K J S : Type} [Fintype K] {target : OracleSpec J}

theorem Budget.state_growth (contract : ReplyContract spec) (kind : I → K)
    (fuel : Nat) (input : A) (localTime : Nat) (queries : K → Nat)
    (hsource : Budget R contract kind fuel input localTime queries)
    (implementation : Handler (spec := spec) (StateT S (OracleComp target)))
    (increase : K → Nat) (inv : S → Prop) (size : S → Nat)
    (hstep : ∀ i s, inv s →
      ∀ z ∈ support ((implementation i).run s),
        inv z.2 ∧ contract.allows i z.1.value ∧ size z.2 ≤ size s + increase (kind i))
    (s : S) (hs : inv s) (z : Run (Option B) × S)
    (hz : z ∈ support ((run R implementation fuel input).run s)) :
    inv z.2 ∧ size z.2 ≤ size s + ∑ k, queries k * increase k := by
  have he := congrArg (fun p => p.run s) (zeroHandler_erase R implementation fuel input)
  simp only [StateT.run_map] at he
  have hmem : (z.1.value, z.2) ∈ support
      ((fun p : Run (Option B) × S => (p.1.value, p.2)) <$>
        ((run R (zeroHandler implementation) fuel input).run s)) := by
    rw [he, support_map]
    exact ⟨z, hz, rfl⟩
  rw [support_map] at hmem
  obtain ⟨⟨r, s'⟩, hr, hv⟩ := hmem
  have hstate : s' = z.2 := congrArg Prod.snd hv
  subst s'
  let scale := localTime + 1
  have h := Budget.potential_bound R contract kind fuel input localTime queries hsource
    (zeroHandler implementation) (fun k => scale * increase k) inv (fun s => (scale * size s : Nat))
    (by
      intro i state hi p hp
      simp only [zeroHandler, StateT.run_map, support_map, Set.mem_image] at hp
      obtain ⟨⟨u, next⟩, hu, rfl⟩ := hp
      obtain ⟨hn, ha, hg⟩ := hstep i state hi (u, next) hu
      refine ⟨hn, ha, ?_⟩
      dsimp
      have hm := Nat.mul_le_mul_left scale hg
      simp only [Nat.mul_add, Nat.add_comm] at hm
      have hm' : (scale * size next : Nat) ≤ scale * increase (kind i) + scale * size state := hm
      simpa using (show (scale * size next : Int) ≤ scale * increase (kind i) + scale * size state by
        exact_mod_cast hm'))
    s hs (r, z.2) hr
  refine ⟨h.1, ?_⟩
  have hn : r.steps + scale * size z.2 ≤
      localTime + ∑ k, queries k * (scale * increase k) + scale * size s := by
    exact_mod_cast h.2
  have hsum : (∑ k, queries k * (scale * increase k)) = scale * ∑ k, queries k * increase k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hsum] at hn
  by_contra hbad
  have hg : size s + (∑ k, queries k * increase k) + 1 ≤ size z.2 := by omega
  have hm := Nat.mul_le_mul_left scale hg
  dsimp [scale] at hn hm
  nlinarith

/-- A handler's linear growing-state cost yields a concrete quadratic total overhead.
The counter is incremented on every call, including cache hits. The counter invariant and
its updates must be proved for the actual handlers; initialization and extraction are separate. -/
theorem Budget.growing_handler_bound (contract : ReplyContract spec) (kind : I → K)
    (fuel : Nat) (input : A) (localTime : Nat) (queries : K → Nat)
    (hsource : Budget R contract kind fuel input localTime queries)
    (implementation : Handler (spec := spec) (StateT S (OracleComp target)))
    (price : K → Nat) (slope : Nat) (inv : S → Prop) (count : S → Nat)
    (hstep : ∀ i s, inv s →
      ∀ z ∈ support ((implementation i).run s),
        inv z.2 ∧ contract.allows i z.1.value ∧
          count z.2 = count s + 1 ∧ z.1.steps ≤ price (kind i) + slope * count s)
    (s : S) (hs : inv s) (hzero : count s = 0) (z : Run (Option B) × S)
    (hz : z ∈ support ((run R implementation fuel input).run s)) :
    inv z.2 ∧ z.1.steps ≤ localTime + (∑ k, queries k * price k) + slope * (∑ k, queries k) ^ 2 := by
  have hg := Budget.state_growth R contract kind fuel input localTime queries hsource
    implementation (fun _ => 1) inv count (by
      intro i state hi p hp
      obtain ⟨hn, ha, hc, _⟩ := hstep i state hi p hp
      exact ⟨hn, ha, hc.le⟩) s hs z hz
  have hcount : count z.2 ≤ ∑ k, queries k := by simpa [hzero] using hg.2
  have hp := Budget.potential_bound R contract kind fuel input localTime queries hsource
    implementation price inv (fun state => -(slope * count state ^ 2 : Nat)) (by
      intro i state hi p hmem
      obtain ⟨hn, ha, hc, ht⟩ := hstep i state hi p hmem
      refine ⟨hn, ha, ?_⟩
      rw [hc]
      have ht' : (p.1.steps : Int) ≤ price (kind i) + slope * count state := by exact_mod_cast ht
      push_cast
      nlinarith [Nat.cast_nonneg (α := Int) slope, Nat.cast_nonneg (α := Int) (count state)]) s hs z hz
  refine ⟨hp.1, ?_⟩
  have hi : (z.1.steps : Int) ≤
      (localTime + (∑ k, queries k * price k) + slope * count z.2 ^ 2 : Nat) := by
    have h := hp.2
    simp [hzero] at h
    push_cast at h ⊢
    omega
  have hn : z.1.steps ≤ localTime + (∑ k, queries k * price k) + slope * count z.2 ^ 2 := by
    exact_mod_cast hi
  apply hn.trans
  exact Nat.add_le_add_left (Nat.mul_le_mul_left slope (Nat.pow_le_pow_left hcount 2)) _

/-- A concrete growing-storage bound for an implementation with no execution counter.
Each query may add at most one cell, while its full cost is linear in current storage size.
The proof instruments calls, then erases that instrumentation with exact cost preservation. -/
theorem Budget.linear_state_bound (contract : ReplyContract spec) (kind : I → K)
    (fuel : Nat) (input : A) (localTime : Nat) (queries : K → Nat)
    (hsource : Budget R contract kind fuel input localTime queries)
    (implementation : Handler (spec := spec) (StateT S (OracleComp target)))
    (price : K → Nat) (slope : Nat) (inv : S → Prop) (size : S → Nat)
    (hstep : ∀ i s, inv s →
      ∀ z ∈ support ((implementation i).run s),
        inv z.2 ∧ contract.allows i z.1.value ∧
          size z.2 ≤ size s + 1 ∧ z.1.steps ≤ price (kind i) + slope * size s)
    (s : S) (hs : inv s) (hzero : size s = 0) (z : Run (Option B) × S)
    (hz : z ∈ support ((run R implementation fuel input).run s)) :
    inv z.2 ∧ size z.2 ≤ ∑ k, queries k ∧
      z.1.steps ≤ localTime + (∑ k, queries k * price k) + slope * (∑ k, queries k) ^ 2 := by
  have hg := Budget.state_growth R contract kind fuel input localTime queries hsource
    implementation (fun _ => 1) inv size (by
      intro i state hi p hp
      obtain ⟨hn, ha, hc, _⟩ := hstep i state hi p hp
      exact ⟨hn, ha, hc⟩) s hs z hz
  refine ⟨hg.1, by simpa [hzero] using hg.2, ?_⟩
  have href := run_countCalls_refines R implementation fuel input (s, 0)
  have hmem : z ∈ support
      ((fun p : Run (Option B) × (S × Nat) => (p.1, p.2.1)) <$>
        (run R (countCalls implementation) fuel input).run (s, 0)) := by
    rw [href]
    exact hz
  rw [support_map] at hmem
  obtain ⟨⟨r, state, count⟩, hr, he⟩ := hmem
  have hz' : (r, state) = z := he
  subst z
  have hb := Budget.growing_handler_bound R contract kind fuel input localTime queries hsource
    (countCalls implementation) price slope (fun p => inv p.1 ∧ size p.1 ≤ p.2) Prod.snd (by
      intro i p hi out hout
      simp only [countCalls, StateT.run, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at hout
      obtain ⟨u, hu, rfl⟩ := hout
      obtain ⟨hn, ha, hs', ht⟩ := hstep i p.1 hi.1 u hu
      refine ⟨⟨hn, by dsimp; omega⟩, ha, rfl, ?_⟩
      dsimp
      exact ht.trans (Nat.add_le_add_left (Nat.mul_le_mul_left slope hi.2) _))
    (s, 0) ⟨hs, by simp [hzero]⟩ rfl (r, state, count) hr
  exact hb.2

end Signatures.Runtime.GeneralCaller
