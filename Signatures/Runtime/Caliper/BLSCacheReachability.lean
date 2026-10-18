import Signatures.Runtime.Caliper.CacheLayout
import Signatures.Runtime.Caliper.SourcePrefix
import Signatures.BLS.Proofs.LazyAGMList

/-! Query-count bounds establish the Caliper cache input invariant at every
reachable adaptive source call, including before the final insertion. No table
indexed by the complete message domain is constructed. -/

namespace Signatures.Runtime.CaliperBackend.BLSCache

open BoundedSource OracleComp OracleSpec Model.LazyAGM
open BLS.LazyAGM.Reduction

variable {w : Nat} {M R A : Type} [DecidableEq M] [SampleableType R]
    (layout : CacheLayout w M R)

def allowedQuery : (baseSpec M R).Domain → Prop
  | .inl _ => True
  | .inr message => layout.key.valid message

def entriesFit (cache : List (M × R)) : Prop :=
  ∀ entry ∈ cache, layout.key.valid entry.1 ∧ layout.value.valid entry.2

theorem query_entries (sampleFits : ∀ value ∈ support ($ᵗ R : ProbComp R), layout.value.valid value)
    (query : (baseSpec M R).Domain) (allowed : allowedQuery layout query)
    (cache : List (M × R)) (valid : entriesFit layout cache)
    (answer : (baseSpec M R).Range query × List (M × R))
    (supported : answer ∈ support ((privateListOracle query).run cache)) :
    entriesFit layout answer.2 := by
  rcases query with n | message
  · rw [privateListOracle_random] at supported
    simp only [support_map, Set.mem_image] at supported
    obtain ⟨value, _, rfl⟩ := supported
    exact valid
  · rw [privateListOracle_lookup] at supported
    split at supported
    · simp only [support_pure, Set.mem_singleton_iff] at supported
      subst answer
      exact valid
    · simp only [support_map, Set.mem_image] at supported
      obtain ⟨value, sampled, rfl⟩ := supported
      intro entry member
      rcases List.mem_cons.mp member with equal | old
      · subst entry
        exact ⟨allowed, sampleFits value sampled⟩
      · exact valid entry old

theorem prefix_entries (sampleFits : ∀ value ∈ support ($ᵗ R : ProbComp R), layout.value.valid value)
    {main residual : OracleComp (baseSpec M R) A} {initial cache : List (M × R)} {used : Nat}
    (queries : AllQueriesSatisfy main (allowedQuery layout)) (valid : entriesFit layout initial)
    (path : SourcePrefix privateListOracle main initial residual cache used) :
    entriesFit layout cache := by
  induction path with
  | start => exact valid
  | step path answer supported ih =>
    exact query_entries layout sampleFits _ (path.allowed queries).1 _ ih answer supported

/-- Immediately before any represented cache query, the table fits and one
slot remains. Hits at full capacity are supported by the cache implementation;
this conservative total-query allowance also reserves space for a fresh key. -/
theorem ready (sampleFits : ∀ value ∈ support ($ᵗ R : ProbComp R), layout.value.valid value)
    {main : OracleComp (baseSpec M R) A} {initial cache : List (M × R)} {used budget : Nat}
    (queries : AllQueriesSatisfy main (allowedQuery layout)) (valid : entriesFit layout initial)
    (bounded : IsTotalQueryBound main budget) (capacity : initial.length + budget ≤ layout.capacityPred + 1)
    (message : M) (next : R → OracleComp (baseSpec M R) A)
    (path : SourcePrefix privateListOracle main initial (queryBind (.inr message) next) cache used)
    (default : R) (defaultFits : layout.value.valid default) :
    layout.input.valid (message, default, cache, ()) := by
  have limits := path.queryBound bounded
  have remaining := limits.2.1
  have growth := path.growth List.length privateListOracle_growth
  have keyFits : layout.key.valid message := (path.allowed queries).1
  have stored := prefix_entries layout sampleFits queries valid path
  change (layout.key.valid message ∧ layout.value.valid default ∧
    (cache.length ≤ layout.capacityPred + 1 ∧ entriesFit layout cache) ∧ True) ∧
    ((lookupValue message default cache).1 = false → cache.length ≤ layout.capacityPred)
  exact ⟨⟨keyFits, defaultFits, ⟨by omega, stored⟩, trivial⟩, fun _ => by omega⟩

section Reductions

variable {F G₁ G₂ : Type} [Field F] [SampleableType F]
    [AddCommGroup G₁] [Module F G₁]

/-- The existing good reduction's query theorem supplies capacity `2*q+1`,
including its extraction and final-target requests. -/
theorem good_ready (scalarLayout : CacheLayout w M F)
    (scalarFits : ∀ scalar, scalarLayout.value.valid scalar)
    (g X : G₁) (pk : G₂) (adversary : Adversary F M M G₁ G₂)
    (q : Nat) (bounded : IsTotalQueryBound (adversary.main pk) q)
    (capacity : 2 * q ≤ scalarLayout.capacityPred)
    (messages : AllQueriesSatisfy (goodProgram g X pk adversary) (allowedQuery scalarLayout))
    (message : M) (next : F → OracleComp (baseSpec M F) F)
    (cache : List (M × F)) (used : Nat)
    (path : SourcePrefix privateListOracle (goodProgram g X pk adversary) []
      (queryBind (.inr message) next) cache used) :
    scalarLayout.input.valid (message, 0, cache, ()) :=
  ready scalarLayout (fun scalar _ => scalarFits scalar) messages (by simp [entriesFit])
    (goodProgram_queries g X pk adversary q bounded) (by simp only [List.length_nil]; omega)
    message next path 0 (scalarFits 0)

/-- The bad reduction uses the same capacity, with scalar pairs as entries. -/
theorem bad_ready (pairLayout : CacheLayout w M (F × F))
    (pairFits : ∀ pair, pairLayout.value.valid pair)
    (g X : G₁) (pk : G₂) (kappa : F) (adversary : Adversary F M M G₁ G₂)
    (q : Nat) (bounded : IsTotalQueryBound (adversary.main pk) q)
    (capacity : 2 * q ≤ pairLayout.capacityPred)
    (messages : AllQueriesSatisfy (badProgram g X pk kappa adversary) (allowedQuery pairLayout))
    (message : M) (next : (F × F) → OracleComp (baseSpec M (F × F)) F)
    (cache : List (M × (F × F))) (used : Nat)
    (path : SourcePrefix privateListOracle (badProgram g X pk kappa adversary) []
      (queryBind (.inr message) next) cache used) :
    pairLayout.input.valid (message, (0, 0), cache, ()) :=
  ready pairLayout (fun pair _ => pairFits pair) messages (by simp [entriesFit])
    (badProgram_queries g X pk kappa adversary q bounded) (by simp only [List.length_nil]; omega)
    message next path (0, 0) (pairFits (0, 0))

end Reductions

end Signatures.Runtime.CaliperBackend.BLSCache
