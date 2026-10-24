import VCVio.OracleComp.QueryTracking.CostModel
import VCVio.OracleComp.QueryTracking.QueryBound

/-!
# Compositional operation accounting

Costs here measure explicit operations, not Lean VM time. A source adversary's local work and
implementations of the charged primitives require separate implementation certificates. In
particular, no cost bound for an arbitrary pure function is inferred from its query count.
-/

open OracleComp OracleSpec

namespace Model.OperationCost

variable {I K α : Type} {spec : OracleSpec I} [Fintype K] [DecidableEq K]

/-- Per-capability bounds on every adaptive continuation, including repeated queries. -/
def Bounded (kind : I → K) (budget : K → Nat) (oa : OracleComp spec α) : Prop :=
  ∀ k, IsQueryBoundP oa (fun i => kind i = k) (budget k)

/-- Total operation allowance from per-capability prices and query budgets. -/
def allowance (price budget : K → Nat) : Nat := ∑ k, price k * budget k

private theorem allowance_step (price budget : K → Nat) (k : K) (h : 0 < budget k) :
    price k + allowance price (fun j => if k = j then budget j - 1 else budget j) =
      allowance price budget := by
  classical
  unfold allowance
  calc
    price k + ∑ j, price j * (if k = j then budget j - 1 else budget j) =
        ∑ j, ((if k = j then price j else 0) +
          price j * (if k = j then budget j - 1 else budget j)) := by
      simp [Finset.sum_add_distrib]
    _ = ∑ j, price j * budget j := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases heq : k = j
      · subst j
        simp only [ite_true]
        calc
          price k + price k * (budget k - 1) = price k * ((budget k - 1) + 1) := by ring
          _ = price k * budget k := by rw [Nat.sub_add_cancel h]
      · simp [heq]

/-- An actual costed handler, bounded for each query, yields a concrete weighted budget for
the whole adaptive simulation. This theorem does not assume the final solver's cost bound. -/
theorem simulate_bound {J : Type} {target : OracleSpec J}
    (kind : I → K) (price budget : K → Nat)
    (impl : QueryImpl spec (AddWriterT Nat (OracleComp target)))
    (hstep : ∀ i, AddWriterT.PathwiseCostAtMost (impl i) (price (kind i)))
    (oa : OracleComp spec α) (hbudget : Bounded kind budget oa) :
    AddWriterT.PathwiseCostAtMost (simulateQ impl oa) (allowance price budget) := by
  induction oa using OracleComp.inductionOn generalizing budget with
  | pure x =>
      simp [AddWriterT.PathwiseCostAtMost]
  | query_bind i next ih =>
      have hb := fun k => (isQueryBoundP_query_bind_iff
        (fun j => kind j = k) i next (budget k)).mp (hbudget k)
      have positive : 0 < budget (kind i) := (hb (kind i)).1.resolve_left (by simp)
      have hnext : ∀ u, Bounded kind
          (fun k => if kind i = k then budget k - 1 else budget k) (next u) :=
        fun u k => (hb k).2 u
      rw [simulateQ_bind, simulateQ_query]
      have h := AddWriterT.pathwiseCostAtMost_bind (hstep i)
        (fun u => ih u _ (hnext u))
      simpa [allowance_step price budget (kind i) positive] using h

/-- Price instrumentation is observationally invisible after erasing the accumulated cost. -/
theorem erase_instrument {J : Type} {target : OracleSpec J}
    (impl : QueryImpl spec (OracleComp target)) (price : I → Nat)
    (oa : OracleComp spec α) :
    Prod.fst <$> (simulateQ (impl.withAddCost price) oa).run = simulateQ impl oa := by
  exact QueryImpl.fst_map_run_withCost impl _ oa

/-- A selected-query budget controls a state counter whose increase is at most one on
selected queries and zero otherwise. The handler may otherwise be fully stateful. -/
theorem state_growth {J S : Type} {target : OracleSpec J}
    (impl : QueryImpl spec (StateT S (OracleComp target)))
    (p : I → Prop) [DecidablePred p] (size : S → Nat)
    (hstep : ∀ i s z, z ∈ support ((impl i).run s) →
      size z.2 ≤ size s + if p i then 1 else 0)
    (oa : OracleComp spec α) (q : Nat) (hq : IsQueryBoundP oa p q)
    (s : S) (z : α × S) (hz : z ∈ support ((simulateQ impl oa).run s)) :
    size z.2 ≤ size s + q := by
  induction oa using OracleComp.inductionOn generalizing q s z with
  | pure a =>
      have heq : z = (a, s) := by simpa using hz
      subst z
      simp
  | query_bind i next ih =>
      rw [isQueryBoundP_query_bind_iff] at hq
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        mem_support_bind_iff] at hz
      obtain ⟨u, hu, hz⟩ := hz
      have hs := hstep i s u hu
      have hc := ih u.1 _ (hq.2 u.1) u.2 z hz
      by_cases h : p i <;> simp [h] at hq hs hc <;> omega

end Model.OperationCost
