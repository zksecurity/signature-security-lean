import Signatures.Model.RandomOracle
import VCVio.EvalDist.Monad.Measure

/-! Two facts about adaptive execution used to relate games that differ only in how
their oracle keeps state. `flattened` runs a handler that logs into a writer layer
through a stateful implementation of its target oracles, as one stateful handler
carrying the log; `evalDist_simulateQ_run_proj` says that if every single query of
one stateful handler has the distribution of another's through a projection of
states, so does every adaptive program. -/

open OracleComp OracleSpec MeasureTheory

namespace Model.Simulation

section Flatten
variable {ι ι' κ : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'} {logged : OracleSpec κ} {S α : Type}

/-- A logged handler into `spec'`, followed by a stateful implementation of `spec'`, as one
stateful handler whose state carries the accumulated log. -/
def flattened (so : QueryImpl spec (WriterT (QueryLog logged) (OracleComp spec')))
    (impl : QueryImpl spec' (StateT S ProbComp)) :
    QueryImpl spec (StateT (S × QueryLog logged) ProbComp) := fun t => StateT.mk fun state =>
  (fun result => (result.1.1, (result.2, state.2 ++ result.1.2))) <$> (simulateQ impl (so t).run).run state.1

theorem flattened_run (so : QueryImpl spec (WriterT (QueryLog logged) (OracleComp spec')))
    (impl : QueryImpl spec' (StateT S ProbComp)) (prog : OracleComp spec α) (s : S) (log : QueryLog logged) :
    (simulateQ (flattened so impl) prog).run (s, log) =
      (fun result => (result.1.1, (result.2, log ++ result.1.2))) <$> (simulateQ impl (simulateQ so prog).run).run s := by
  induction prog using OracleComp.inductionOn generalizing s log with
  | pure a => simp [simulateQ_pure, StateT.run_pure]
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
      StateT.run_bind, WriterT.run_bind', map_bind, flattened]
    change ((fun result => (result.1.1, (result.2, log ++ result.1.2))) <$> (simulateQ impl (so t).run).run s >>= _) = _
    rw [bind_map_left]
    apply bind_congr
    rintro ⟨⟨u, w⟩, s'⟩
    simp only [ih, simulateQ_map, StateT.run_map, Functor.map_map]
    congr 1
    funext result
    simp [List.append_assoc]

end Flatten

section Projection
variable {ι : Type} {spec : OracleSpec.{0, 0} ι} {S₁ S₂ α : Type}

/-- Adaptive execution respects a state projection when every single query does. -/
theorem evalDist_simulateQ_run_proj (h₁ : QueryImpl spec (StateT S₁ ProbComp)) (h₂ : QueryImpl spec (StateT S₂ ProbComp))
    (proj : S₂ → S₁)
    (hh : ∀ t s, ∀ [MeasurableSpace (spec.Range t × S₁)],
      𝒟[(h₁ t).run (proj s)] = 𝒟[Prod.map id proj <$> (h₂ t).run s])
    (prog : OracleComp spec α) (s : S₂) [MeasurableSpace (α × S₁)] :
    𝒟[(simulateQ h₁ prog).run (proj s)] = 𝒟[Prod.map id proj <$> (simulateQ h₂ prog).run s] := by
  induction prog using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind t k ih =>
    let : MeasurableSpace (spec.Range t × S₁) := ⊤
    let : MeasurableSpace (spec.Range t × S₂) := ⊤
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map, OracleQuery.input_query,
      StateT.run_bind, map_bind, evalDist_bind_of_discrete]
    rw [hh t s, evalDist_map_of_discrete, Measure.bind, Measure.bind,
      Measure.map_map Measurable.of_discrete Measurable.of_discrete]
    congr 2
    funext output
    exact ih output.1 output.2

end Projection

end Model.Simulation
