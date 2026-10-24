import Proofs.Runtime.Caliper.WeightedParameters
import VCVio.OracleComp.Constructions.SampleableType.Basic

/-! Derive challenge coverage and both complete Caliper certificates from the
fixed local contracts. The same caller, source, challenge encoding, output
encoding and sampling port are used in both reductions. -/
namespace Signatures.Runtime.WeightedCaliper
open Caliper OracleComp OracleSpec CaliperBackend BoundedSource
variable {F G PK J M : Type} [Field F] [SampleableType F] [DecidableEq J]
    [AddCommGroup G] [Module F G] [AddCommGroup PK] [Module F PK]
    {queries : QueryAllowance} {terms : M → List (J × F)} {generator : G} {keyGenerator : PK}
    (P : Parameters F G PK J M queries terms generator keyGenerator)

namespace Parameters

theorem scalar_valid (scalar : F) : P.scalar.valid scalar := by
  have reached : scalar ∈ support (Subtype.val <$> P.scalarSource) := by
    rw [P.scalarLaw]
    exact mem_support_uniformSample F
  rw [support_map, Set.mem_image] at reached
  obtain ⟨represented, _, equal⟩ := reached
  exact equal ▸ represented.property

theorem challenge_valid (scalar : F) :
    P.layout.goodSetup.challenge.valid ((generator, scalar • generator), (keyGenerator, scalar • keyGenerator)) := by
  have point := (P.good.response false).preserves (scalar, (generator, generator))
    ⟨P.scalar_valid scalar, P.generatorValid, P.generatorValid⟩
  rw [P.goodResponse] at point
  exact ⟨⟨P.generatorValid, point⟩, P.keyGeneratorValid,
    P.keyScale.preserves (scalar, keyGenerator) ⟨P.scalar_valid scalar, P.keyGeneratorValid⟩⟩

theorem pair_correct : Interactive.Refines P.layout.port .unit
    P.layout.bad.service.evaluation.cache.lookup.unit.representation
    P.layout.bad.service.evaluation.cache.value.representation (fun _ => P.pairSource) P.pairSampler :=
  PairSampling.refines (hw := P.layout.scheme.rows.accumulation.cache.wordFits)
    (fits := P.layout.scheme.rows.accumulation.cache.pairValueFits) P.samplerCorrect P.samplerCorrect

theorem pair_uniform : Subtype.val <$> P.pairSource = ($ᵗ (F × F) : ProbComp (F × F)) :=
  PairSampling.uniform P.scalar P.scalar P.layout.scheme.rows.accumulation.cache.pairValueFits
    P.scalarSource P.scalarSource P.scalarLaw P.scalarLaw

theorem pair_time : Interactive.TimeBound P.layout.port .unit
    P.layout.bad.service.evaluation.cache.lookup.unit.representation P.pairSampler P.pairTime :=
  PairSampling.time_bound (hw := P.layout.scheme.rows.accumulation.cache.wordFits)
    (fits := P.layout.scheme.rows.accumulation.cache.pairValueFits) P.samplerCorrect P.samplerCorrect P.samplerTime P.samplerTime

theorem pair_words : (P.pairSampler.lower P.layout.port).descriptionWords ≤ P.pairWords :=
  PairSampling.code_bound P.scalar P.scalar P.layout.scheme.rows.accumulation.cache.wordFits
    P.layout.scheme.rows.accumulation.cache.pairValueFits P.layout.port P.sampler P.sampler P.samplerWords P.samplerWords

theorem pair_names : WordIO.NamesBound (P.pairSampler.lower P.layout.port) P.pairSlots :=
  PairSampling.names P.scalar P.scalar P.layout.scheme.rows.accumulation.cache.wordFits
    P.layout.scheme.rows.accumulation.cache.pairValueFits P.layout.port P.sampler P.sampler P.samplerNames P.samplerNames

theorem scalar_reserve : P.samplerSlots + 5 < 2 ^ P.wordBits := by
  have bound := P.samplerReserve
  unfold PairSampling.slots at bound
  omega

theorem pair_fits : (P.pairSampler.lower P.layout.port).DescriptionFits :=
  PairSampling.descriptionFits P.scalar P.scalar P.layout.scheme.rows.accumulation.cache.wordFits
    P.layout.scheme.rows.accumulation.cache.pairValueFits P.layout.port P.sampler P.sampler
      P.samplerFits P.samplerFits P.samplerNames (by have := P.scalar_reserve; omega)
theorem hash_reservation : queries.total ≤ P.layout.good.service.hashCapacityPred + 1 := by
  change queries.total ≤ P.layout.scheme.hashes - 1 + 1
  simpa only [Nat.sub_add_cancel P.layout.scheme.hashPositive] using P.hashRoom

theorem sign_reservation : queries.total ≤ P.layout.good.service.signCapacityPred + 1 := by
  change queries.total ≤ P.layout.scheme.signs - 1 + 1
  simpa only [Nat.sub_add_cancel P.layout.scheme.signPositive] using P.signRoom
end Parameters

variable (A : AlgebraicAdversary P)

theorem good_within : dlogWithin P.layout.port P.layout.goodSetup.challenge P.scalar generator keyGenerator
    P.goodWords P.goodMemory P.goodTime (Model.LazyAGM.WeightedReduction.goodReductionList terms A.proofView) := by
  have goodTerms : ∀ message, P.good.generate message = (terms message).map (Prod.map (Equiv.refl J) id) := by
    intro message
    simpa using congrFun P.goodTerms message
  exact WeightedFull.good_dlogWithin (base := base F J) (key := indexTy) (val := scalarTy)
    P.layout.good P.layout.goodSetup P.good (primitives F J) comparison (comparison_correct F J)
    A.caller queries.total P.scalarSource P.goodCoefficient P.goodCombine rfl P.scalarLaw
    P.goodResponse P.goodExtract P.goodSum A.invariant P.cacheRoom P.hash_reservation P.sign_reservation
    (Equiv.refl J) terms goodTerms A.correspondence A.proofView A.source_eq
    P.goodBounds (A.bounds P) P.sampler P.samplerCorrect P.samplerTime P.samplerWords P.samplerNames
    P.samplerFits P.scalar_reserve P.goodAddresses generator keyGenerator P.challenge_valid

theorem bad_within : dlogWithin P.layout.port P.layout.goodSetup.challenge P.scalar generator keyGenerator
    P.badWords P.badMemory P.badTime (Model.LazyAGM.WeightedReduction.badReductionList terms A.proofView) := by
  have badTerms : ∀ message, P.bad.generate message = (terms message).map (Prod.map (Equiv.refl J) id) := by
    intro message
    simpa using congrFun P.badTerms message
  exact WeightedFull.bad_dlogWithin (base := base F J) (key := indexTy) (scalar := scalarTy)
    P.layout.bad P.layout.badSetup P.bad (primitives F J) comparison (comparison_correct F J)
    (WeightedFull.SharedCaller.bad (base := base F J) (key := indexTy) (scalar := scalarTy) P.layout A.caller) queries.total P.pairSource P.badCoefficient P.badCombine rfl P.pair_uniform
    P.badResponse P.badExtract (WeightedFull.SharedCaller.badInvariant (base := base F J) (key := indexTy) (scalar := scalarTy) P.layout A.caller queries.total A.invariant)
    P.cacheRoom P.hash_reservation P.sign_reservation (Equiv.refl J) terms badTerms
    (WeightedFull.SharedCaller.badCorrespondence (base := base F J) (key := indexTy) (scalar := scalarTy) P.layout A.caller queries.total A.invariant (Equiv.refl J) A.correspondence)
    A.proofView A.source_eq P.resampling P.scalarSource P.scalarLaw
    P.badBounds (WeightedFull.SharedCaller.badBounds (base := base F J) (key := indexTy) (scalar := scalarTy) P.layout A.caller (A.bounds P)) P.pairSampler P.sampler
    P.pair_correct P.samplerCorrect P.pair_time P.samplerTime P.pair_words P.samplerWords P.pair_names P.samplerNames
    P.pair_fits P.samplerFits P.samplerReserve (by have := P.scalar_reserve; omega)
    P.badAddresses generator keyGenerator P.challenge_valid

theorem reductions_within :
    P.within P.goodTime (Model.LazyAGM.WeightedReduction.goodReductionList terms A.proofView) ∧
    P.within P.badTime (Model.LazyAGM.WeightedReduction.badReductionList terms A.proofView) :=
  ⟨(good_within P A).mono (Nat.le_max_left _ _) (Nat.le_max_left _ _) le_rfl,
    (bad_within P A).mono (Nat.le_max_right _ _) (Nat.le_max_right _ _) le_rfl⟩
end Signatures.Runtime.WeightedCaliper
