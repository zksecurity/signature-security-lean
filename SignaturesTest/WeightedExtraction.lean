import Proofs.Runtime.BackendWeightedExtractionDescription
import Proofs.Runtime.BackendWeightedExtractionState
import Proofs.Runtime.BackendWeightedSigningExtraction
import Proofs.Runtime.BackendWeightedHashExtraction
import Proofs.Runtime.BackendWeightedTargetExtraction
import Proofs.Runtime.BackendWeightedGoodExtractionBudget
import Proofs.Runtime.BackendWeightedBadExtractionBudget
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

open OracleComp OracleSpec PFunctor
open Signatures.Runtime Signatures.Runtime.BackendProgram Signatures.Runtime.WeightedAGM
open Model.LazyAGM.WeightedReduction

namespace SignaturesTest.WeightedExtraction

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private abbrev field := ZMod 5
private abbrev model := arithmetic field field field Nat Bool PrimitiveCosts.unit

section Native

variable {C : StepClass} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass C} [Q.HasCategory] [Q.HasProd] [Q.HasSum]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase field field field Nat Bool))
  (data : DataCode Q rep.data) (sampling : MachineCompiler.SamplingImplementation Q iface rep)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) (model.execute instr))

-- Reverse hash logs attach coefficients chronologically. A missing hash
-- coefficient is zero; the surplus signing coefficient creates no term.
-- The result and every original cache binding, including a shadow, are checked.
example : (Extract.backendGood rep data PrimitiveCosts.unit primitive sampling (.oops 1)).denote
    (((((1, 37), (1, [2], [3, 4])) : (field × Nat) × field × List field × List field),
      ([((37, (1 : Fin 2)), (4 : field)), ((37, 0), 3)], [((2, 37), (2 : field))]), ()),
      [((37, 0), (3 : field)), ((37, 1), 4), ((37, 1), 0)]) =
    pure ((3 : field), [((37, (0 : Fin 2)), (3 : field)), ((37, 1), 4), ((37, 1), 0)]) := by
  rw [Extract.backendGood_source]
  have hterms : (Index.oops 1).sourceTerms (F := field) (G₁ := field) (G₂ := field) (K := Nat) (M := Bool)
      PrimitiveCosts.unit = OOPS.LazyAGM.terms 1 := funext (Index.oops_sourceTerms PrimitiveCosts.unit 1)
  rw [hterms]
  rw [Extract.goodFinish_cached _ _ _ _ (by
    constructor
    · intro p hp
      change p ∈ [((37, (0 : Fin 2)), (3 : field)), ((37, 1), 4)] at hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> exact ⟨_, rfl⟩
    · intro p hp
      change p ∈ [((2, 37), (2 : field))] at hp
      simp only [List.mem_singleton] at hp
      subst p
      intro row hr
      change row ∈ [((37, (0 : Fin 2)), (1 : field)), ((37, 1), 2)] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact ⟨_, rfl⟩) (by
    intro row hr
    change row ∈ [((37, (0 : Fin 2)), (1 : field)), ((37, 1), 1)] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact ⟨_, rfl⟩)]
  congr 1
  change ((2 : field) / 4, _) = (3, _)
  congr 1
  exact (div_eq_iff (by decide : (4 : field) ≠ 0)).2 (by decide)

-- A completely unseen final topic reads both bases, even with a zero weight.
-- The first draw can be zero: division retains the field's source semantics.
example : (Extract.backendGood rep data PrimitiveCosts.unit primitive sampling (.oops 1)).denote
    (((((0, 99), (1, [], [])) : (field × Nat) × field × List field × List field), ([], []), ()),
      [((37, 0), (3 : field))]) =
    (do let r₀ ← ($ᵗ field : ProbComp field)
        let r₁ ← ($ᵗ field : ProbComp field)
        pure ((1 : field) / r₀, [((99, (1 : Fin 2)), r₁), ((99, 0), r₀), ((37, 0), 3)])) := by
  rw [Extract.backendGood_source, Extract.goodFinish_cachedTranscript _ _ _ _ (by
    simp [TranscriptCached, Reply.chronological])]
  rw [Index.oops_sourceTerms]
  have ht : OOPS.LazyAGM.terms 1 ((0, 99) : field × Nat) =
      [((99, (0 : Fin 2)), (1 : field)), ((99, 1), 0)] := by decide
  dsimp only [AGM.outputView]
  rw [ht]
  simp [Model.LazyAGM.evalTerms, StateT.run_bind, bind_pure_comp,
    Extract.cachedValue, BLS.LazyAGM.Reduction.traceTerms, signedTerms,
    Reply.chronological]
  rw [BLS.LazyAGM.Reduction.privateListOracle_lookup]
  change ((fun r : field => (r, [((99, (0 : Fin 2)), r), ((37, 0), 3)])) <$>
      ($ᵗ field : ProbComp field) >>= fun a =>
        (fun b => (a.1⁻¹, b.2)) <$>
          (BLS.LazyAGM.Reduction.privateListOracle (.inr (99, (1 : Fin 2)))).run a.2) = _
  rw [bind_map_left]
  congr 1

-- Proximity's constant and variable coordinates are both used in paired-mask
-- extraction. The unused hash coefficients and extra signing coefficient have
-- no effect, and the shadowed paired binding survives unchanged.
example : (Extract.backendBad rep data PrimitiveCosts.unit primitive sampling (.proximity 1)).denote
    ((((((1, ()), 37), (4, [2, 3], [3, 4])) : ((field × Unit) × Nat) × field × List field × List field),
      ([], [(((2, ()), 37), (2 : field))]), ()),
      [(((0 : Fin 2), 37), ((1, 2) : field × field)), ((1, 37), (3, 4)), ((1, 37), (0, 0))]) =
    pure ((3 : field), [(((0 : Fin 2), 37), ((1, 2) : field × field)),
      ((1, 37), (3, 4)), ((1, 37), (0, 0))]) := by
  rw [Extract.backendBad_source]
  let terms : (field × Unit) × Nat → List ((Fin 2 × Nat) × field) :=
    fun m => [((0, m.2), 1), ((1, m.2), m.1.1)]
  have hterms : (Index.proximity 1).sourceTerms (F := field) (G₁ := field) (G₂ := field) (K := Nat) (M := Bool)
      PrimitiveCosts.unit = terms := by
    funext m
    rw [Index.proximity_sourceTerms]
    rfl
  rw [hterms]
  rw [Extract.badFinish_cached _ _ _ _ (by
    constructor
    · simp [Reply.chronological]
    · intro p hp
      change p ∈ [(((2, ()), 37), (2 : field))] at hp
      simp only [List.mem_singleton] at hp
      subst p
      intro row hr
      change row ∈ [(((0 : Fin 2), 37), (1 : field)), ((1, 37), 2)] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact ⟨_, rfl⟩) (by
    intro row hr
    change row ∈ [(((0 : Fin 2), 37), (1 : field)), ((1, 37), 1)] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact ⟨_, rfl⟩)]
  congr 1
  change (-(1 : field) / 3, _) = (3, _)
  congr 1
  exact (div_eq_iff (by decide : (3 : field) ≠ 0)).2 (by decide)

end Native

open Lean Meta

run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Extract.hash_signedTerms, ``Extract.goodProgram_finish, ``Extract.badProgram_finish,
      ``Extract.evaluateCoefficients_source, ``Extract.evaluateTarget_source,
      ``Extract.good_source, ``Extract.bad_source, ``Extract.backendGood_source, ``Extract.backendBad_source,
      ``Extract.evaluateRows_description, ``Extract.good_description, ``Extract.bad_description,
      ``Extract.backendGood_description, ``Extract.backendBad_description,
      ``Extract.goodFinish_cachedTranscript, ``Extract.badFinish_cachedTranscript,
      ``Extract.goodFinish_cached, ``Extract.badFinish_cached,
      ``Extract.goodFinish_cache, ``Extract.badFinish_cache,
      ``Extract.backendGood_cache, ``Extract.backendBad_cache,
      ``Extract.goodResult_cost, ``Extract.badResult_cost,
      ``Extract.coefficientPrepareArgs_cost, ``Extract.coefficientEvaluateArgs_cost,
      ``Extract.targetPrepareArgs_cost, ``Extract.targetEvaluateArgs_cost,
      ``Extract.evaluateCoefficients_bound, ``Extract.evaluateTarget_bound,
      ``Extract.hashTerms_weakenTail_time, ``Extract.hashCoefficients_cost,
      ``Index.coefficients_cost, ``Index.coefficients_length, ``Index.coefficients_rows_size,
      ``Index.coefficients_size, ``Extract.preparationInput_size, ``Extract.preparationCache_size,
      ``Extract.hashCoefficients_length, ``Extract.hashCoefficients_rows_size, ``Extract.hashCoefficients_size,
      ``Extract.goodSigningCoefficients_bound, ``Extract.badSigningCoefficients_bound,
      ``Extract.hashExtraction_bound, ``Extract.goodTarget_bound, ``Extract.badTarget_bound,
      ``Extract.goodHashArgs_cost, ``Extract.goodSignArgs_cost, ``Extract.badSignArgs_cost,
      ``Extract.goodTargetArgs_cost, ``Extract.badTargetArgs_cost, ``Extract.defaultRow_cost,
      ``Extract.extraction_target_size, ``Extract.extractionFrames_size, ``Extract.extractionInputs_size,
      ``Extract.extractionArgumentFrame_size, ``Extract.extractionTargetFrame_size,
      ``Extract.evaluateCoefficients_cached, ``Extract.evaluateTarget_cache,
      ``Extract.goodExtraction_assembly, ``Extract.badExtraction_assembly,
      ``Extract.extractionWidth_bounds, ``Extract.defaultRow_denote,
      ``Extract.defaultRow_size, ``Extract.extractionCache_size,
      ``Extract.backendGood_bound, ``Extract.backendBad_bound] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let type ← inferType param
        if type.isAppOf ``Finite || type.isAppOf ``Fintype then
          throwError "{name}: finite topic/slot/message domain required"
        for forbidden in #[``Bounds] do
          if (type.find? (fun e => e.isConstOf forbidden)).isSome then
            throwError "{name}: supplied finished extractor budget"

-- The actual call and complete extractor endpoints derive all component budgets.
-- Their resource premises must not supply a runtime bound for compiled components.
run_meta do
  for name in #[``Extract.goodSigningCoefficients_bound, ``Extract.badSigningCoefficients_bound,
      ``Extract.hashExtraction_bound, ``Extract.goodTarget_bound, ``Extract.badTarget_bound,
      ``Extract.backendGood_bound, ``Extract.backendBad_bound] do
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let type ← inferType param
        forallTelescope type fun _ conclusion => do
          if conclusion.isAppOf ``LE.le then
            for component in #[``Expression.compile, ``Language.compile, ``Evaluate.backendGood,
                ``Evaluate.backendBad, ``Read.goodRead, ``Read.badRead,
                ``Extract.backendGood, ``Extract.backendBad] do
              if (conclusion.find? (fun e => e.isConstOf component)).isSome then
                throwError "{name}: assumed completed component runtime"

end SignaturesTest.WeightedExtraction
