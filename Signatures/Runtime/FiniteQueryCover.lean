import VCVio.OracleComp.QueryTracking.QueryBound

/-! A finitely branching oracle computation has a finite proof-only query
cover. This is an existence theorem about the inductive computation tree,
not an algorithm for finding the cover and not an efficiency bound. -/

open OracleComp OracleSpec
open scoped BigOperators

namespace Signatures.Runtime.FiniteQueryCover

variable {I A : Type} {spec : OracleSpec I} [DecidableEq I]

/-- An independently proved bound for one oracle family can replace its
coordinate in a coarser per-family bound. -/
theorem replace_bound (main : OracleComp spec A) (bounds : I → Nat) (target : I)
    (n : Nat) (bounded : IsPerIndexQueryBound main bounds)
    (targetBound : IsQueryBoundP main (· = target) n) :
    IsPerIndexQueryBound main (Function.update bounds target n) := by
  induction main using OracleComp.inductionOn generalizing bounds n with
  | pure _ => trivial
  | query_bind i next ih =>
      rw [isPerIndexQueryBound_query_bind_iff] at bounded ⊢
      rw [isQueryBoundP_query_bind_iff] at targetBound
      refine ⟨?_, fun answer => ?_⟩
      · by_cases hi : i = target
        · subst i
          simpa using targetBound.1.resolve_left (by simp)
        · simpa [hi] using bounded.1
      · apply (ih answer _ _ (bounded.2 answer) (targetBound.2 answer)).mono
        intro j
        by_cases hi : i = target <;> by_cases hj : j = i <;>
          by_cases ht : j = target <;> simp_all

variable [∀ i, Finite (spec.Range i)]

/-- Every branch has finite depth and each query has finitely many replies.
The resulting finite cover may be very large; it never needs to be executed. -/
theorem exists_bound (main : OracleComp spec A) :
    ∃ (families : Finset I) (n : Nat),
      IsPerIndexQueryBound main (fun i => if i ∈ families then n else 0) := by
  classical
  induction main using OracleComp.inductionOn with
  | pure _ => exact ⟨∅, 0, trivial⟩
  | query_bind i next ih =>
      let : Fintype (spec.Range i) := Fintype.ofFinite _
      choose families bound bounded using ih
      let cover := insert i (Finset.univ.biUnion families)
      let capacity := 1 + ∑ answer, bound answer
      refine ⟨cover, capacity, ?_⟩
      rw [isPerIndexQueryBound_query_bind_iff]
      refine ⟨by simp [cover, capacity], fun answer => ?_⟩
      apply (bounded answer).mono
      have hcap : bound answer ≤ ∑ a, bound a :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ answer)
      intro j
      by_cases hj : j ∈ families answer
      · have hcover : j ∈ cover :=
          Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨answer, Finset.mem_univ _, hj⟩)
        by_cases hji : j = i
        · subst j
          simpa [hj, cover, capacity] using hcap
        · simpa [hj, hcover, hji, capacity] using Nat.le_add_left_of_le hcap
      · simp only [ite_eq_right hj]
        exact Nat.zero_le _

/-- A finite collection of computations shares a finite cover and capacity.
Finiteness is needed for this input collection, not for the oracle universe. -/
theorem exists_bound_family {K : Type} [Finite K] (main : K → OracleComp spec A) :
    ∃ (families : Finset I) (n : Nat), ∀ k,
      IsPerIndexQueryBound (main k) (fun i => if i ∈ families then n else 0) := by
  classical
  let : Fintype K := Fintype.ofFinite _
  choose families bound bounded using fun k => exists_bound (main k)
  refine ⟨Finset.univ.biUnion families, ∑ k, bound k, fun k => (bounded k).mono ?_⟩
  intro i
  by_cases hi : i ∈ families k
  · have hcover : i ∈ Finset.univ.biUnion families :=
      Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, hi⟩
    simpa [hi, hcover] using
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k) :
        bound k ≤ ∑ x, bound x)
  · simp [hi]

end Signatures.Runtime.FiniteQueryCover
