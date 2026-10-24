import Proofs.LinearFunctional.LazyAGMCache

/-! Streaming weighted extraction, one transcript occurrence at a time.
Evaluating a message before applying its coefficient preserves the complete
oracle computation. In particular, zero coefficients still perform every
lookup. The expanded source list is used only in the equality proof. -/

namespace Signatures.Runtime.WeightedAGM.Batching
open OracleComp OracleSpec Model.LazyAGM
open BLS.LazyAGM.Reduction (privateListOracle)

variable {F K M G R : Type} [Semiring F] [AddCommMonoid R] [Module F R]

theorem evalTerms_scale (coefficient : F) (terms : List (K × F)) :
    (evalTerms (terms.map fun term => (term.1, coefficient * term.2)) :
      OracleComp (baseSpec K R) R) =
      (fun value => coefficient • value) <$> evalTerms terms := by
  induction terms with
  | nil => simp [evalTerms]
  | cons term terms ih =>
      simp only [List.map_cons, evalTerms, map_bind]
      apply bind_congr
      intro answer
      rw [ih]
      simp only [bind_map_left, map_pure, smul_add, mul_smul]

theorem evalTerms_append (left right : List (K × F)) :
    (evalTerms (left ++ right) : OracleComp (baseSpec K R) R) = (do
      let first ← evalTerms left
      let second ← evalTerms right
      pure (first + second)) := by
  induction left with
  | nil => simp only [List.nil_append, evalTerms, pure_bind, zero_add, bind_pure]
  | cons term left ih =>
      simp only [List.cons_append, evalTerms, ih, bind_assoc, pure_bind]
      apply bind_congr
      intro answer
      apply bind_congr
      intro first
      apply bind_congr
      intro second
      rw [add_assoc]

abbrev Row (M G F : Type) := (M × G) × F

def expanded (terms : M → List (K × F)) (rows : List (Row M G F)) : List (K × F) :=
  rows.flatMap fun row => (terms row.1.1).map fun term => (term.1, row.2 * term.2)

def step (terms : M → List (K × F)) (accumulator : R) (row : Row M G F) :
    OracleComp (baseSpec K R) R :=
  (fun value => accumulator + row.2 • value) <$> evalTerms (terms row.1.1)

def execute (terms : M → List (K × F)) (rows : List (Row M G F)) (accumulator : R) :
    OracleComp (baseSpec K R) R :=
  rows.foldlM (step terms) accumulator

/-- This is equality of query computations, before choosing any cache handler. -/
theorem execute_source (terms : M → List (K × F)) (rows : List (Row M G F))
    (accumulator : R) :
    execute terms rows accumulator =
      (fun value => accumulator + value) <$> evalTerms (expanded terms rows) := by
  induction rows generalizing accumulator with
  | nil => simp [execute, expanded, evalTerms]
  | cons row rows ih =>
      simp only [execute, List.foldlM_cons, step, bind_map_left] at ih ⊢
      simp only [expanded, List.flatMap_cons, evalTerms_append, evalTerms_scale,
        bind_map_left, map_bind, map_pure]
      apply bind_congr
      intro answer
      rw [ih]
      simp only [bind_pure_comp]
      congr 1
      funext value
      exact add_assoc accumulator (row.2 • answer) value

def chronologicalRows (transcript : List (M × G)) (coefficients : List F) :
    List (Row M G F) :=
  transcript.reverse.mapIdx fun n token => (token, tokenCoeff coefficients n)

theorem expanded_signedTerms (terms : M → List (K × F)) (transcript : List (M × G))
    (coefficients : List F) :
    expanded terms (chronologicalRows transcript coefficients) =
      WeightedReduction.signedTerms terms coefficients transcript.reverse := by
  simp only [expanded, chronologicalRows, WeightedReduction.signedTerms,
    List.flatMap, List.mapIdx_eq_zipIdx_map, List.map_map, Function.comp_def]

theorem execute_signedTerms (terms : M → List (K × F)) (transcript : List (M × G))
    (coefficients : List F) (accumulator : R) :
    execute terms (chronologicalRows transcript coefficients) accumulator =
      (fun value => accumulator + value) <$>
        evalTerms (WeightedReduction.signedTerms terms coefficients transcript.reverse) := by
  rw [execute_source, expanded_signedTerms]

/-- Counts every occurrence, including repeated indices and zero coefficients. -/
def reads (terms : M → List (K × F)) (rows : List (Row M G F)) : Nat :=
  (rows.map fun row => (terms row.1.1).length).sum

theorem expanded_length (terms : M → List (K × F)) (rows : List (Row M G F)) :
    (expanded terms rows).length = reads terms rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      simp only [expanded, List.flatMap_cons, List.length_append, List.length_map,
        reads, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]

omit [Semiring F] in
theorem reads_bound (terms : M → List (K × F)) (capacity : Nat)
    (bounded : ∀ message, (terms message).length ≤ capacity) (rows : List (Row M G F)) :
    reads terms rows ≤ capacity * rows.length := by
  induction rows with
  | nil => simp [reads]
  | cons row rows ih =>
      have size := bounded row.1.1
      simp only [reads, List.map_cons, List.sum_cons] at ih ⊢
      simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
      omega

theorem chronological_reads_bound (terms : M → List (K × F)) (capacity : Nat)
    (bounded : ∀ message, (terms message).length ≤ capacity)
    (transcript : List (M × G)) (coefficients : List F) :
    reads terms (chronologicalRows transcript coefficients) ≤ capacity * transcript.length := by
  simpa only [chronologicalRows, List.length_mapIdx, List.length_reverse] using
    reads_bound terms capacity bounded (chronologicalRows transcript coefficients)

section Cache
variable [DecidableEq K] [SampleableType R]

noncomputable def cachedStep (terms : M → List (K × F)) (state : R × List (K × R)) (row : Row M G F) :
    ProbComp (R × List (K × R)) :=
  (fun answer => (state.1 + row.2 • answer.1, answer.2)) <$>
    (simulateQ privateListOracle (evalTerms (terms row.1.1))).run state.2

noncomputable def cached (terms : M → List (K × F)) (rows : List (Row M G F)) (state : R × List (K × R)) :
    ProbComp (R × List (K × R)) :=
  rows.foldlM (cachedStep terms) state

theorem cached_simulate (terms : M → List (K × F)) (rows : List (Row M G F))
    (state : R × List (K × R)) :
    cached terms rows state =
      (simulateQ privateListOracle (execute terms rows state.1)).run state.2 := by
  induction rows generalizing state with
  | nil => simp [cached, execute]
  | cons row rows ih =>
      simp only [cached, List.foldlM_cons, cachedStep, bind_map_left] at ih ⊢
      simp only [execute, List.foldlM_cons, step, bind_map_left, simulateQ_bind,
        StateT.run_bind]
      apply bind_congr
      intro answer
      exact ih (state.1 + row.2 • answer.1, answer.2)

/-- Preserves the entire ordered cache, not merely the returned scalar. -/
theorem cached_source (terms : M → List (K × F)) (rows : List (Row M G F))
    (state : R × List (K × R)) :
    cached terms rows state =
      (fun answer => (state.1 + answer.1, answer.2)) <$>
        (simulateQ privateListOracle (evalTerms (expanded terms rows))).run state.2 := by
  rw [cached_simulate, execute_source, simulateQ_map, StateT.run_map]

theorem cached_signedTerms (terms : M → List (K × F)) (transcript : List (M × G))
    (coefficients : List F) (state : R × List (K × R)) :
    cached terms (chronologicalRows transcript coefficients) state =
      (fun answer => (state.1 + answer.1, answer.2)) <$>
        (simulateQ privateListOracle
          (evalTerms (WeightedReduction.signedTerms terms coefficients transcript.reverse))).run state.2 := by
  rw [cached_source, expanded_signedTerms]

theorem cache_growth (terms : M → List (K × F)) (rows : List (Row M G F))
    (state answer : R × List (K × R)) (reached : answer ∈ support (cached terms rows state)) :
    answer.2.length ≤ state.2.length + reads terms rows := by
  rw [cached_source] at reached
  simp only [support_map, Set.mem_image] at reached
  obtain ⟨result, supported, rfl⟩ := reached
  have growth := (WeightedReduction.evalTerms_list_preserves (expanded terms rows) state.2 result supported).2.2
  rwa [expanded_length] at growth

theorem remaining_room (terms : M → List (K × F)) (rows : List (Row M G F))
    (state answer : R × List (K × R)) (capacity remaining : Nat)
    (reserved : state.2.length + reads terms rows + remaining ≤ capacity)
    (reached : answer ∈ support (cached terms rows state)) :
    answer.2.length + remaining ≤ capacity := by
  have growth := cache_growth terms rows state answer reached
  omega

end Cache
end Signatures.Runtime.WeightedAGM.Batching
