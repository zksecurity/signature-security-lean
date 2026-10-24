import Proofs.Runtime.BackendLazyAGMExtractionGrowth
import Proofs.Runtime.BackendLazyAGMReadBudget
import Proofs.Runtime.BackendLazyAGMReadDescription
import Proofs.Runtime.BackendLazyAGMSelect
import Proofs.Runtime.BackendLazyAGMUpdate
import Proofs.Runtime.BackendLazyAGMBody
import Proofs.Runtime.BackendLazyAGMEvaluateSize
import Proofs.Runtime.BackendLazyAGMEvaluateState
import Proofs.Runtime.BackendLazyAGMEvaluateDescription
import Proofs.Runtime.BackendLazyAGMExtractionDescription
import Proofs.Runtime.BackendLanguageIteration
import Proofs.Runtime.BackendLengthCost
import Proofs.Runtime.BackendLazyAGMGoodEvaluate
import Proofs.Runtime.BackendLazyAGMBadEvaluate
import Proofs.Runtime.BackendLazyAGMExtractionState
import Proofs.Runtime.BackendLazyAGMExtractionCost
import Proofs.Runtime.BackendLazyAGMExtractionArgs
import Proofs.Runtime.BackendLazyAGMTokensSize
import Proofs.Runtime.BackendLazyAGMGoodTokens
import Proofs.Runtime.BackendLazyAGMBadTokens
import Proofs.Runtime.BackendLazyAGMGoodExtractionBudget
import Proofs.Runtime.BackendLazyAGMBadExtractionBudget
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

open OracleComp OracleSpec PFunctor Signatures.Runtime Signatures.Runtime.BackendProgram
open Signatures.Runtime.LazyAGM Model.LazyAGM BLS.LazyAGM.Reduction

namespace SignaturesTest.BackendLazyAGMExtraction

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

section Native

variable {C : StepClass} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass C} [Q.HasCategory] [Q.HasProd] [Q.HasSum]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase (ZMod 5) (ZMod 5) (ZMod 5) Nat Nat))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b)
      ((arithmetic (ZMod 5) (ZMod 5) (ZMod 5) Nat Nat cost).execute instr))
  (sampling : MachineCompiler.SamplingImplementation Q iface rep)

-- Chronological preparation keeps surplus coefficients in the
-- executed input while evaluating only actual transcript occurrences.
example : (backendEvaluateTokens rep data cost primitive sampling.scalar
    (.op .zero .unit) (.op .zero .unit) goodCombine).denote
      (([(7, 4), (8, 1)], [2, 4, 1], ((99, 0), 0), ()), [(7, 2), (8, 3)]) =
        pure ((4 : ZMod 5), [(7, 2), (8, 3)]) := by
  rw [backendEvaluateTokens, compileRead_denote rep data cost primitive sampling.scalar
    (.op .zero .unit) (sampling.scalar_denote ())]
  rw [evaluateTokens_source cost _ (.op .zero .unit) goodCombine (fun _ _ => rfl)
    (fun answer coeff acc => goodCombine_denote (G₁ := ZMod 5) (G₂ := ZMod 5) (M := Nat)
      cost answer coeff acc)]
  simp only [traceTerms, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, List.mapIdx_cons, List.mapIdx_nil, evalTerms, simulateQ_bind,
    simulateQ_spec_query, simulateQ_pure, StateT.run_bind, StateT.run_pure]
  repeat'
    erw [privateListOracle_lookup]
    simp only [List.lookup_cons, Nat.reduceBEq, pure_bind]
  norm_num [tokenCoeff, smul_eq_mul]
  decide

-- A resumed evaluator step selects the current indexed occurrence, advances
-- its counter, and inserts only that occurrence's message into the cache.
example : (Language.compile rep data (arithmetic (ZMod 5) (ZMod 5) (ZMod 5) Nat Nat cost) primitive
    (rep.ty (cacheTy scalar)) (readEffect rep data cost primitive sampling.scalar (.op .zero .unit))
    (evalBody goodCombine)).denote
      (((1, 4), [((7, 1), 2), ((8, 2), 3)], ((99, 0), 0), ()), []) =
        (fun r : ZMod 5 => ((2, 4 + 3 * r), [(8, r)])) <$> ($ᵗ (ZMod 5) : ProbComp (ZMod 5)) := by
  rw [evalBody_source rep data cost primitive sampling.scalar (.op .zero .unit) (sampling.scalar_denote ())]
  erw [privateListOracle_lookup]
  simp [List.lookup_nil]
  rfl

-- Repeated occurrences retain their own coefficients; cache hits leave the
-- association list unchanged. Group points in the rows do not select keys.
example : (backendEvaluateGood rep data cost primitive sampling).denote
    (([((7, 4), 1), ((8, 1), 2), ((7, 3), 3)], ((99, 0), 0), ()), [(7, 2), (8, 3)]) =
      pure ((4 : ZMod 5), [(7, 2), (8, 3)]) := by
  rw [backendEvaluateGood_source]
  simp only [evalTerms, List.map_cons, List.map_nil, simulateQ_bind,
    simulateQ_spec_query, simulateQ_pure, StateT.run_bind, StateT.run_pure]
  repeat'
    erw [privateListOracle_lookup]
    simp only [List.lookup_cons, Nat.reduceBEq, pure_bind]
  norm_num [smul_eq_mul]
  decide

-- Empty inputs never query their fallback message.
example : (backendEvaluateBad rep data cost primitive sampling).denote
    (([], ((99, 0), 0), ()), []) = pure ((0 : ZMod 5 × ZMod 5), []) := by
  rw [backendEvaluateBad_source]
  simp [evalTerms]

-- A zero coefficient still causes its source-prescribed read. Misses are
-- sampled in row order; the repeated key reuses its first draw.
example : (backendEvaluateGood rep data cost primitive sampling).denote
    (([((7, 4), 0), ((8, 1), 1), ((7, 3), 2)], ((99, 0), 0), ()), []) =
      (do
        let r₇ ← ($ᵗ (ZMod 5) : ProbComp (ZMod 5))
        let r₈ ← ($ᵗ (ZMod 5) : ProbComp (ZMod 5))
        pure (r₈ + 2 * r₇, [(8, r₈), (7, r₇)])) := by
  rw [backendEvaluateGood_source]
  simp only [evalTerms, List.map_cons, List.map_nil, simulateQ_bind,
    simulateQ_spec_query, simulateQ_pure, StateT.run_bind, StateT.run_pure]
  repeat'
    erw [privateListOracle_lookup]
    simp only [pure_bind]
  norm_num [smul_eq_mul]
  congr 1

-- Both coordinates are accumulated in the bad branch.
example : (backendEvaluateBad rep data cost primitive sampling).denote
    (([((7, 4), 0), ((8, 1), 1), ((7, 3), 2)], ((99, 0), 0), ()), [(7, (2, 3)), (8, (4, 1))]) =
      pure (((3, 2) : ZMod 5 × ZMod 5), [(7, (2, 3)), (8, (4, 1))]) := by
  rw [backendEvaluateBad_source]
  simp only [evalTerms, List.map_cons, List.map_nil, simulateQ_bind,
    simulateQ_spec_query, simulateQ_pure, StateT.run_bind, StateT.run_pure]
  repeat'
    erw [privateListOracle_lookup]
    simp only [List.lookup_cons, Nat.reduceBEq, pure_bind]
  norm_num
  decide

-- Full good extraction restores chronology, ignores surplus coefficients,
-- uses the signing sum in the denominator, and preserves the final cache.
example : (backendExtractGood rep data cost primitive sampling).denote
    (((9, 2, [2, 4, 1], [3]), ([(7, 4), (8, 2)], [(7, 1)]), ()), [(9, 4), (7, 2), (8, 3)]) =
      pure ((2 : ZMod 5), [(9, 4), (7, 2), (8, 3)]) := by
  rw [backendExtractGood_source]
  simp only [goodFinish, chronological, AGM.outputView, traceTerms, List.reverse_cons,
    List.reverse_nil, List.mapIdx_cons, List.mapIdx_nil, List.nil_append, List.cons_append,
    evalTerms, simulateQ_bind, simulateQ_spec_query,
    simulateQ_pure, StateT.run_bind, StateT.run_pure]
  repeat'
    erw [privateListOracle_lookup]
    simp only [List.lookup_cons, Nat.reduceBEq, pure_bind]
  norm_num [tokenCoeff, smul_eq_mul]
  apply (div_eq_iff (by decide)).2
  decide

-- Division by zero keeps the source field semantics.
example : (backendExtractGood rep data cost primitive sampling).denote
    (((9, 2, [2, 4, 1], [3]), ([(7, 4), (8, 2)], [(7, 1)]), ()), [(9, 1), (7, 2), (8, 3)]) =
      pure ((0 : ZMod 5), [(9, 1), (7, 2), (8, 3)]) := by
  rw [backendExtractGood_source]
  simp only [goodFinish, chronological, AGM.outputView, traceTerms, List.reverse_cons,
    List.reverse_nil, List.mapIdx_cons, List.mapIdx_nil, List.nil_append, List.cons_append,
    evalTerms, simulateQ_bind, simulateQ_spec_query,
    simulateQ_pure, StateT.run_bind, StateT.run_pure]
  repeat'
    erw [privateListOracle_lookup]
    simp only [List.lookup_cons, Nat.reduceBEq, pure_bind]
  norm_num [tokenCoeff, smul_eq_mul]
  decide

-- An unseen final message is looked up after the frozen output, even with
-- no transcript rows. Only that message is inserted into the private cache.
example : (backendExtractGood rep data cost primitive sampling).denote
    (((9, 1, [], []), ([], []), ()), []) =
      (fun r : ZMod 5 => (1 / r, [(9, r)])) <$> ($ᵗ (ZMod 5) : ProbComp (ZMod 5)) := by
  rw [backendExtractGood_source]
  simp only [goodFinish, chronological, AGM.outputView, traceTerms, List.reverse_nil,
    List.mapIdx_nil, evalTerms, simulateQ_bind, simulateQ_pure, simulateQ_spec_query,
    StateT.run_bind, StateT.run_pure, pure_bind]
  erw [privateListOracle_lookup]
  simp

example : (backendExtractBad rep data cost primitive sampling).denote
    (((9, 4, [1], []), ([], []), ()), []) =
      (fun r : ZMod 5 × ZMod 5 => (-r.2 / r.1, [(9, r)])) <$>
        ($ᵗ (ZMod 5 × ZMod 5) : ProbComp (ZMod 5 × ZMod 5)) := by
  rw [backendExtractBad_source]
  simp only [badFinish, chronological, AGM.outputView, traceTerms, List.reverse_nil,
    List.mapIdx_nil, evalTerms, simulateQ_bind, simulateQ_pure, simulateQ_spec_query,
    StateT.run_bind, StateT.run_pure, pure_bind]
  erw [privateListOracle_lookup]
  simp

-- Bad extraction reads only signing rows and the target. The uncached hash
-- message 99 must not create a private-cache entry; the missing signing
-- coefficient defaults to zero without dropping that signing read.
example : (backendExtractBad rep data cost primitive sampling).denote
    (((9, 4, [1, 2, 3], [2]), ([(99, 3)], [(8, 4), (7, 1)]), ()),
      [(9, (1, 4)), (7, (2, 3)), (8, (4, 1))]) =
        pure ((1 : ZMod 5), [(9, (1, 4)), (7, (2, 3)), (8, (4, 1))]) := by
  rw [backendExtractBad_source]
  simp only [badFinish, chronological, AGM.outputView, traceTerms, List.reverse_cons,
    List.reverse_nil, List.mapIdx_cons, List.mapIdx_nil, List.nil_append, List.cons_append,
    evalTerms, simulateQ_bind, simulateQ_spec_query,
    simulateQ_pure, StateT.run_bind, StateT.run_pure]
  repeat'
    erw [privateListOracle_lookup]
    simp only [List.lookup_cons, Nat.reduceBEq, pure_bind]
  norm_num [tokenCoeff]
  apply (div_eq_iff (by decide)).2
  decide

end Native

open Lean Meta Elab Command

run_cmd liftTermElabM do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``repeat_indexed_suffix, ``repeat_indexed, ``fold_count, ``listLength_denote,
      ``LengthCompiler.body_time_bound, ``LengthCompiler.length_time_bound,
      ``LengthCompiler.length_cost_bound, ``LengthCompiler.length_description,
      ``selectRow_denote, ``evalUpdate_denote, ``evalBody_denote, ``evaluateRows_denote,
      ``goodCombine_denote, ``badCombine_denote, ``foldRows_simulate,
      ``evaluateRows_source, ``evaluateGood_source, ``evaluateBad_source,
      ``backendRead_denote, ``backendGoodRead_denote, ``backendBadRead_denote,
      ``goodReadArgs_cost, ``badReadArgs_cost, ``backendRead_bound,
      ``backendGoodRead_bound, ``backendBadRead_bound, ``backendRead_description,
      ``backendGoodRead_description, ``backendBadRead_description,
      ``compileRead_denote, ``backendEvaluate_denote, ``backendEvaluate_source,
      ``backendEvaluateGood_source, ``backendEvaluateBad_source,
      ``tokenRows_terms, ``evaluateTokens_source, ``extractGood_source, ``extractBad_source,
      ``backendExtractGood_source, ``backendExtractBad_source,
      ``goodProgram_finish, ``badProgram_finish, ``goodFinish_queries, ``badFinish_queries,
      ``backendEvaluateGood_growth, ``backendEvaluateBad_growth,
      ``backendExtractGood_growth, ``backendExtractBad_growth,
      ``iterationRun_bound_remaining, ``Bounds.iterate_remaining, ``Language.loop_bound_remaining,
      ``evaluationRow_key_size, ``evaluationSelected_size,
      ``evaluationRows_size, ``evaluationFrame_size, ``evaluationUpdateFrame_size, ``evaluationCache_size,
      ``selectRow_time_bound, ``goodUpdate_time_bound, ``badUpdate_time_bound,
      ``evalKey_cost, ``evalBody_bound, ``privateRead_messages, ``evalBody_source,
      ``backendRead_state, ``evalBody_state, ``evalBody_remaining,
      ``backendEvaluate_description, ``backendEvaluateGood_description, ``backendEvaluateBad_description,
      ``backendExtractGood_description, ``backendExtractBad_description,
      ``evaluateInit_cost, ``backendEvaluate_bound, ``goodBody_budget, ``badBody_budget,
      ``backendEvaluateGood_bound, ``backendEvaluateBad_bound,
      ``privateTerms_messages, ``privateTerms_state, ``evaluateTokens_state,
      ``defaultRow_cost, ``goodExtractResult_cost, ``badExtractResult_cost, ``evaluateTokenArgs_cost,
      ``goodHashArgs_cost, ``goodSignArgs_cost, ``badSignArgs_cost, ``goodTarget_cost, ``badTarget_cost,
      ``tokenRows_entries, ``tokenInput_size, ``tokenCache_size,
      ``evaluatePreparedTokens_bound, ``evaluateTokens_bound, ``goodTokens_budget, ``badTokens_budget,
      ``extractionWidth_base, ``evaluationWidth_le_extractionWidth, ``extractionCache_size,
      ``extraction_target_size, ``extractionFrames_size, ``extractionInputs_size,
      ``extractionArgumentFrame_size, ``extraction_default_size,
      ``goodExtraction_assembly, ``badExtraction_assembly, ``backendExtractGood_bound, ``backendExtractBad_bound] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let type ← inferType param
        if type.isAppOf ``Finite || type.isAppOf ``Fintype then
          throwError "{name}: finite-domain premise added to lazy extraction"

end SignaturesTest.BackendLazyAGMExtraction
