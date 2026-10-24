import Proofs.Runtime.RejectionSampling
import VCVio.OracleComp.QueryTracking.QueryBound.Basic

/-! Probability accounting for computations with a sticky failure marker.
On unmarked outcomes the implementation is a subdistribution of the ideal
law. Missing mass is charged to failure, not treated as an ideal sample. -/

namespace Signatures.Runtime.MarkedProbability

open scoped ENNReal

variable {A B : Type}

noncomputable def bad (p : PMF (A × Bool)) : ℝ≥0∞ := ∑' a, p (a, true)

def GoodLe (p : PMF (A × Bool)) (q : PMF A) : Prop := ∀ a, p (a, false) ≤ q a

noncomputable def bind (p : PMF (A × Bool)) (f : A → PMF (B × Bool)) : PMF (B × Bool) :=
  p.bind fun x => (f x.1).map fun y => (y.1, x.2 || y.2)

theorem mass_split (p : PMF (A × Bool)) : (∑' a, p (a, false)) + bad p = 1 := by
  have h := p.tsum_coe
  rw [ENNReal.tsum_prod'] at h
  simpa only [tsum_fintype, Fintype.sum_bool, ENNReal.tsum_add, bad, add_comm] using h

theorem good_mass_le_one (p : PMF (A × Bool)) : (∑' a, p (a, false)) ≤ 1 := by
  rw [← mass_split p]
  exact le_add_right (le_refl _)

theorem bad_eq_map (p : PMF (A × Bool)) : bad p = (p.map Prod.snd) true := by
  classical
  rw [PMF.map_apply, ENNReal.tsum_prod']
  simp [bad, tsum_fintype]

theorem bind_good (p : PMF (A × Bool)) (f : A → PMF (B × Bool)) (b : B) :
    bind p f (b, false) = ∑' a, p (a, false) * f a (b, false) := by
  classical
  rw [bind, PMF.bind_apply, ENNReal.tsum_prod']
  simp only [tsum_fintype, Fintype.sum_bool, PMF.map_apply, ENNReal.tsum_prod']
  simp [Prod.ext_iff]

theorem bad_bind (p : PMF A) (f : A → PMF (B × Bool)) :
    bad (p.bind f) = ∑' a, p a * bad (f a) := by
  simp only [bad, PMF.bind_apply]
  rw [ENNReal.tsum_comm]
  simp only [ENNReal.tsum_mul_left]

theorem bad_mark (p : PMF (A × Bool)) (b : Bool) :
    bad (p.map (fun x => (x.1, b || x.2))) = if b then 1 else bad p := by
  cases b with
  | false =>
    change bad (p.map id) = bad p
    rw [PMF.map_id]
  | true =>
    rw [bad_eq_map, PMF.map_comp]
    simp [Function.comp_def]

theorem bind_bad (p : PMF (A × Bool)) (f : A → PMF (B × Bool)) :
    bad (bind p f) = bad p + ∑' a, p (a, false) * bad (f a) := by
  rw [bind, bad_bind]
  simp only [bad_mark]
  rw [ENNReal.tsum_prod']
  simp only [tsum_fintype, Fintype.sum_bool, Bool.false_eq_true, ite_true, ite_false,
    mul_one, ENNReal.tsum_add, bad]

theorem GoodLe.pure (a : A) : GoodLe (PMF.pure (a, false)) (PMF.pure a) := by
  classical
  intro b
  simp [PMF.pure_apply, Prod.ext_iff]

theorem bad_pure (a : A) : bad (PMF.pure (a, false)) = 0 := by
  simp [bad, PMF.pure_apply]

theorem GoodLe.bind {p : PMF (A × Bool)} {q : PMF A}
    {f : A → PMF (B × Bool)} {g : A → PMF B}
    (hp : GoodLe p q) (hf : ∀ a, GoodLe (f a) (g a)) : GoodLe (bind p f) (q.bind g) := by
  intro b
  rw [bind_good, PMF.bind_apply]
  exact ENNReal.tsum_le_tsum (fun a => mul_le_mul' (hp a) (hf a b))

theorem bind_bad_le {p : PMF (A × Bool)} {f : A → PMF (B × Bool)} {ε δ : ℝ≥0∞}
    (hp : bad p ≤ ε) (hf : ∀ a, bad (f a) ≤ δ) : bad (bind p f) ≤ ε + δ := by
  rw [bind_bad]
  apply add_le_add hp
  calc
    _ ≤ ∑' a, p (a, false)*δ := ENNReal.tsum_le_tsum fun a => mul_le_mul' (le_refl _) (hf a)
    _ = (∑' a, p (a, false))*δ := ENNReal.tsum_mul_right
    _ ≤ 1*δ := mul_le_mul' (good_mass_le_one p) (le_refl δ)
    _ = δ := one_mul _

theorem GoodLe.map {p : PMF (A × Bool)} {q : PMF A} (h : GoodLe p q) (f : A → B) :
    GoodLe (p.map (fun x => (f x.1, x.2))) (q.map f) := by
  classical
  intro b
  simp only [PMF.map_apply, ENNReal.tsum_prod', tsum_fintype, Fintype.sum_bool, Prod.ext_iff]
  simp only [Bool.false_eq_true, and_false, ite_false, and_true]
  apply ENNReal.tsum_le_tsum
  intro a
  split <;> simp_all [h a]

theorem bad_map (p : PMF (A × Bool)) (f : A → B) :
    bad (p.map (fun x => (f x.1, x.2))) = bad p := by
  rw [bad_eq_map, bad_eq_map, PMF.map_comp]
  rfl

/-- Any Boolean observation has ideal success probability at most actual
success probability plus the implementation's marked failure probability. -/
theorem event_le_add_bad {p : PMF (A × Bool)} {q : PMF A} (h : GoodLe p q) (test : A → Bool) :
    (q.map test) true ≤ (p.map (fun x => test x.1)) true + bad p := by
  let marked := p.map (fun x => (test x.1, x.2))
  let ideal := q.map test
  have hm : GoodLe marked ideal := h.map test
  have hi := ideal.tsum_coe
  have hp := mass_split marked
  simp only [tsum_fintype, Fintype.sum_bool] at hi hp
  have hfalse := hm false
  have hle : ideal true + marked (false, false) ≤
      marked (true, false) + bad marked + marked (false, false) := by
    calc
      _ ≤ ideal true + ideal false := add_le_add (le_refl _) hfalse
      _ = 1 := hi
      _ = _ := by rw [← hp]; ac_rfl
  have hle := ENNReal.le_of_add_le_add_right (marked.apply_ne_top (false, false)) hle
  have hb : bad marked = bad p := bad_map p test
  have he : (p.map (fun x => test x.1)) true = marked (true, true) + marked (true, false) := by
    have hh : p.map (fun x => test x.1) = marked.map Prod.fst :=
      (PMF.map_comp (fun x : A × Bool => (test x.1, x.2)) p Prod.fst).symm
    rw [hh, PMF.map_apply]
    simp [tsum_fintype, Fintype.sum_prod_type]
  change ideal true ≤ _
  rw [he, ← hb]
  exact hle.trans (add_le_add (le_add_left (le_refl _)) (le_refl _))

section OracleTree

open OracleComp

variable {I : Type} {spec : OracleSpec I}

/-- Interpret an adaptive oracle tree while retaining the OR of all sampler
failure markers. Future queries still execute on marked paths. -/
noncomputable def simulate (impl : (q : spec.Domain) → PMF (spec.Range q × Bool))
    (code : OracleComp spec A) : PMF (A × Bool) :=
  PFunctor.FreeM.rec (fun a => PMF.pure (a, false)) (fun q _ next => bind (impl q) next) code

theorem simulate_pure (impl : (q : spec.Domain) → PMF (spec.Range q × Bool)) (a : A) :
    simulate impl (pure a) = PMF.pure (a, false) := rfl

theorem simulate_query_bind (impl : (q : spec.Domain) → PMF (spec.Range q × Bool))
    (q : spec.Domain) (next : spec.Range q → OracleComp spec A) :
    simulate impl ((liftM (spec.query q) : OracleComp spec _) >>= next) =
      bind (impl q) (fun reply => simulate impl (next reply)) := rfl

/-- A conventional stateful interpreter for the same sticky marker. -/
noncomputable def stateImpl (impl : (q : spec.Domain) → PMF (spec.Range q × Bool)) :
    QueryImpl spec (StateT Bool PMF) := fun q flag =>
  (impl q).map (fun out => (out.1, flag || out.2))

theorem simulate_state (impl : (q : spec.Domain) → PMF (spec.Range q × Bool))
    (code : OracleComp spec A) (flag : Bool) :
    (simulateQ (stateImpl impl) code).run flag =
      (simulate impl code).map (fun out => (out.1, flag || out.2)) := by
  induction code using OracleComp.inductionOn generalizing flag with
  | pure a => simp [simulate_pure, StateT.run_pure, PMF.pure_map]
  | query_bind q next ih =>
    rw [simulateQ_bind, simulateQ_spec_query]
    change ((impl q).map (fun out => (out.1, flag || out.2))).bind
      (fun out => (simulateQ (stateImpl impl) (next out.1)).run out.2) = _
    simp only [PMF.bind_map, ih, simulate_query_bind, bind, PMF.map_bind, PMF.map_comp]
    simp only [Function.comp_def, Bool.or_assoc]

theorem simulate_state_false (impl : (q : spec.Domain) → PMF (spec.Range q × Bool))
    (code : OracleComp spec A) :
    (simulateQ (stateImpl impl) code).run false = simulate impl code := by
  rw [simulate_state]
  change (simulate impl code).map id = _
  exact PMF.map_id _

theorem simulate_map (impl : (q : spec.Domain) → PMF (spec.Range q × Bool))
    (f : A → B) (code : OracleComp spec A) :
    simulate impl (f <$> code) = (simulate impl code).map (fun out => (f out.1, out.2)) := by
  rw [← simulate_state_false, simulateQ_map, StateT.run_map, simulate_state_false]
  rfl

/-- Every adaptive branch is charged against the same decreasing budget.
The kernel obligations are needed only for requests whose weight fits the
initial limit; this permits width conditions derived from source budgets. -/
theorem simulate_bound (impl : (q : spec.Domain) → PMF (spec.Range q × Bool))
    (ideal : QueryImpl spec PMF) (weight : spec.Domain → Nat) (limit : Nat) (ε : ℝ≥0∞)
    (hgood : ∀ q, weight q ≤ limit → GoodLe (impl q) (ideal q))
    (hbad : ∀ q, weight q ≤ limit → bad (impl q) ≤ weight q * ε)
    (code : OracleComp spec A) (n : Nat) (hn : n ≤ limit)
    (hb : IsQueryBound code n (fun q left => weight q ≤ left) (fun q left => left-weight q)) :
    GoodLe (simulate impl code) (simulateQ ideal code) ∧ bad (simulate impl code) ≤ n*ε := by
  induction code using OracleComp.inductionOn generalizing n with
  | pure a =>
    exact ⟨GoodLe.pure a, by rw [simulate_pure, bad_pure]; exact bot_le⟩
  | query_bind q next ih =>
    rw [isQueryBound_query_bind_iff] at hb
    have hnext := fun reply => ih reply (n-weight q) (by omega) (hb.2 reply)
    rw [simulate_query_bind, simulateQ_bind, simulateQ_spec_query]
    constructor
    · exact (hgood q (hb.1.trans hn)).bind (fun reply => (hnext reply).1)
    · have h := bind_bad_le (hbad q (hb.1.trans hn)) (fun reply => (hnext reply).2)
      have he : (weight q : ℝ≥0∞)*ε + (n-weight q : Nat)*ε = n*ε := by
        have heN : weight q+(n-weight q) = n := by omega
        rw [← add_mul, ← Nat.cast_add, heN]
      exact h.trans_eq he

end OracleTree

end Signatures.Runtime.MarkedProbability
