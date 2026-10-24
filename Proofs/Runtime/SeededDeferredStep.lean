import VCVio.OracleComp.QueryTracking.SeededOracle
import Proofs.Runtime.SeededMeasure

/-! One-step deferred sampling for dependent oracle families. The generated
seed is a probability-proof artifact. The runtime implementation must not
enumerate its family list or allocate its unused entries. -/

open OracleComp OracleSpec
open MeasureTheory

namespace Signatures.Runtime.SeededDeferred

variable {I A : Type} {spec : OracleSpec I} [DecidableEq I]

/-- Remaining per-family capacity after consuming one request. -/
def debit (budget : I → Nat) (i : I) : I → Nat :=
  Function.update budget i (budget i - 1)

theorem debit_covers (budget : I → Nat) (families : List I)
    (cover : SeedListCovers budget families) (i : I) :
    SeedListCovers (debit budget i) families := by
  intro j hj
  apply cover j
  by_cases h : j = i
  · subst j
    simp only [debit, Function.update_self] at hj
    omega
  · simpa only [debit, Function.update_of_ne h] using hj

private theorem counts_eq (budget : I → Nat) (families : List I)
    (unique : families.Nodup) (cover : SeedListCovers budget families) (i : I) :
    budget i * families.count i = budget i := by
  by_cases h : budget i = 0
  · simp [h]
  · rw [List.count_eq_one_of_mem unique (cover i (Nat.pos_of_ne_zero h)), Nat.mul_one]

variable [∀ i, SampleableType (spec.Range i)] [IsUniformSpec spec]
  [∀ i, MeasurableSpace (spec.Range i)] [∀ i, DiscreteMeasurableSpace (spec.Range i)]

private theorem prepend_probability (budget : I → Nat) (families : List I)
    (unique : families.Nodup) (cover : SeedListCovers budget families)
    (i : I) (positive : 0 < budget i) (answer : spec.Range i) (rest : QuerySeed spec)
    [MeasurableSpace (QuerySeed spec)] [MeasurableSingletonClass (QuerySeed spec)] :
    𝒟[generateSeed spec budget families] {rest.prependValues [answer]} =
      𝒟[(liftM (spec.query i) : OracleComp spec _)] {answer} *
        𝒟[generateSeed spec (debit budget i) families] {rest} := by
  have hc := counts_eq budget families unique cover
  have hf : (fun j => budget j * families.count j) = budget := funext hc
  have hd : families.dedup = families := List.dedup_eq_self.mpr unique
  have hp : 0 < budget i * families.count i := by simpa only [hc] using positive
  simpa only [evalDist_apply_singleton, hf, hc, hd, debit, probOutput_query] using
    probOutput_generateSeed_prependValues spec budget families answer rest hp

variable [unifSpec ⊂ₒ spec] [unifSpec ˡ⊂ₒ spec]
  [MeasurableSpace A]

/-- Move the next queried reply out of the preallocated seed. The continuation
may inspect the entire residual seed, so this preserves its joint law with the
reply rather than only the marginal distribution of that reply. -/
theorem generate_bind_step (budget : I → Nat) (families : List I)
    (unique : families.Nodup) (cover : SeedListCovers budget families)
    (i : I) (positive : 0 < budget i) (next : QuerySeed spec → OracleComp spec A) :
    𝒟[do
      let seed ← liftComp (generateSeed spec budget families) spec
      next seed] =
    𝒟[do
      let answer ← (liftM (spec.query i) : OracleComp spec _)
      let rest ← liftComp (generateSeed spec (debit budget i) families) spec
      next (rest.prependValues [answer])] := by
  classical
  apply measure_of_compat
  apply congrArg SPMF.toMeasure
  apply evalSPMF_ext
  intro result
  let : MeasurableSpace (QuerySeed spec) := ⊤
  let : MeasurableSpace (spec.Range i) := ⊤
  let : MeasurableSpace A := ⊤
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  simp_rw [probOutput_liftComp]
  have hrange : Function.support (fun seed : QuerySeed spec =>
      𝒟[generateSeed spec budget families] {seed} * 𝒟[next seed] {result}) ⊆
      Set.range (fun p : spec.Range i × QuerySeed spec => p.2.prependValues [p.1]) := by
    intro seed hs
    simp only [evalDist_apply_singleton] at hs
    have hmem : seed ∈ support (generateSeed spec budget families) := by
      by_contra h
      exact hs (by simp [(probOutput_eq_zero_iff _ _).mpr h])
    have hpos : 0 < budget i * families.count i := by
      simpa only [counts_eq budget families unique cover] using positive
    obtain ⟨answer, rest, hcons⟩ := exists_cons_of_mem_support_generateSeed
      spec budget families seed i hmem hpos
    exact ⟨(answer, seed.update i rest),
      QuerySeed.eq_prependValues_of_pop_eq_some (QuerySeed.pop_eq_some_of_cons seed i answer rest hcons)⟩
  simp only [evalDist_apply_singleton] at hrange
  rw [← (QuerySeed.prependValues_singleton_injective i).tsum_eq hrange,
    ENNReal.tsum_prod']
  have hp := fun (answer : spec.Range i) (rest : QuerySeed spec) =>
    prepend_probability (spec := spec) budget families unique cover i positive answer rest
  simp only [evalDist_apply_singleton] at hp
  simp_rw [hp, mul_assoc,
    ENNReal.tsum_mul_left, probOutput_bind_eq_tsum, probOutput_liftComp]

/-- Consuming that freshly exposed seed head leaves precisely the independent
seed with one fewer entry in its family. -/
theorem query_bind_step (budget : I → Nat) (families : List I)
    (unique : families.Nodup) (cover : SeedListCovers budget families)
    (i : I) (positive : 0 < budget i)
    (next : spec.Range i → QuerySeed spec → OracleComp spec A) :
    𝒟[do
      let seed ← liftComp (generateSeed spec budget families) spec
      let reply ← (seededOracle i).run seed
      next reply.1 reply.2] =
    𝒟[do
      let answer ← (liftM (spec.query i) : OracleComp spec _)
      let rest ← liftComp (generateSeed spec (debit budget i) families) spec
      next answer rest] := by
  rw [generate_bind_step budget families unique cover i positive]
  congr 1
  congr 1
  funext answer
  congr 1
  funext rest
  rw [seededOracle.run_cons (QuerySeed.prependValues_singleton rest answer), pure_bind]
  simp only [QuerySeed.prependValues, QuerySeed.update_idem, QuerySeed.update_eq_self]

end Signatures.Runtime.SeededDeferred
