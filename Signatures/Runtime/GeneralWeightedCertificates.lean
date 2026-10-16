import Signatures.Runtime.GeneralWeightedParameters

/-! The two weighted reductions belong to the fixed backend's concrete DLog
class. Whole-solver certificates are derived from component contracts and a
general attacker's own resources, then used to bound its two reduction advantages.
No source-game probability theorem or completed-solver budget is an assumption. -/

open BilinearGroup

open OracleComp OracleSpec PFunctor AlgebraicGroupModel
open Signatures.Runtime Signatures.Runtime.BackendProgram
open Signatures.Runtime.WeightedAGM Signatures.Runtime.WeightedAGM.NativeSolver

namespace Signatures.Runtime.WeightedAGM.General

universe v w x

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [Q.HasProd] [Q.HasSum] [Q.HasOption] [Q.IsDistributive] [OptionCode (Q := Q)]
  {F G₁ G₂ Gₜ K M : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [AddCommGroup Gₜ] [Module F Gₜ] [BilinearPairing F G₁ G₂ Gₜ]


variable {index : Index}
  (P : Parameters (Q := Q) (F := F) (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ) (K := K) (M := M) index)
  (A : AlgebraicAdversary P)

theorem reductions_within :
    dlogWithin P.rep P.backend P.descriptionSizes P.factor P.description
      P.generator P.keyGenerator P.inputWidth P.solverCode P.goodTime
      (Model.LazyAGM.WeightedReduction.goodReductionList (index.sourceTerms P.cost) A.source) ∧
    dlogWithin P.rep P.backend P.descriptionSizes P.factor P.description
      P.generator P.keyGenerator P.inputWidth P.solverCode P.badTime
      (Model.LazyAGM.WeightedReduction.badReductionList (index.sourceTerms P.cost) A.source) := by
  have hchallenge : ∀ x : F,
      Q.size (P.rep.env inputTypes) (P.generator, x • P.generator, P.keyGenerator, x • P.keyGenerator, ()) ≤
        P.inputWidth := by
    intro x
    have h := challenge_size P.rep P.sizes P.width P.width P.width
      P.values.point₁ P.values.point₂ P.values.unit P.generator P.keyGenerator x
    have hh := P.headerWidth
    have hi := P.inputCapacity
    omega
  have hcode : P.factor * programDescription index.bound
      (P.descriptionSizes.localSize A.caller.initCode + 2 * P.descriptionSizes.localSize A.caller.headCode +
        P.descriptionSizes.localSize A.caller.updateCode)
      (P.sampling.scalar.descriptionSize P.descriptionSizes) (P.sampler.code.descriptionSize P.descriptionSizes)
      P.queries.total P.allowance P.instructionSize P.handlerPortSize P.solverPortSize ≤ P.solverCode := by
    apply Nat.mul_le_mul_left
    have h := A.storedCode
    dsimp only [programDescription]
    omega
  have goodCertificate := goodProgram_within P.rep index P.bd P.ports P.sampler P.boundary P.data P.cost P.primitive P.sampling
    P.control P.queryCost P.sizes P.lists P.lengths P.laws P.dataLaws P.primitiveBound P.mono P.routing P.dispatch
    A.caller P.execution A.runs P.recovery A.program A.realizes P.backend P.descriptionSizes P.factor P.description
    P.allowance P.descriptionLaws P.descriptionData P.descriptionDispatch
    P.inputWidth P.width P.outputWidth P.routeWidth P.queries.total P.queries.total P.keyWidth
    P.comparisonTime P.scalarTime P.opTime P.handlerAdapterTime P.solverAdapterTime P.dynamicTime
    P.handlerTickTime P.callerTickTime P.extractionTickTime P.headerWidth le_rfl P.queryCapacity
    P.values P.ops P.handlerCaps P.solverCaps P.dynamicSamples P.storeCapacity P.goodHandlerComparison
    P.extractionComparison P.requestWidth P.stateWidth P.headWidth
    P.sampleTime P.callerTick P.goodHandlerTick P.extractionTick A.source A.corresponds
    P.instructionSize P.handlerPortSize P.solverPortSize P.instructionDescriptions P.handlerDescriptions P.solverDescriptions
  have badCertificate := badProgram_within P.rep index P.bd P.ports P.sampler P.boundary P.data P.cost P.primitive P.sampling
    P.control P.queryCost P.sizes P.lists P.lengths P.laws P.dataLaws P.primitiveBound P.mono P.routing P.dispatch
    A.caller P.execution A.runs P.recovery A.program A.realizes P.backend P.descriptionSizes P.factor P.description
    P.allowance P.descriptionLaws P.descriptionData P.descriptionDispatch
    P.inputWidth P.width P.outputWidth P.routeWidth P.queries.total P.queries.total P.keyWidth
    P.comparisonTime P.scalarTime P.opTime P.handlerAdapterTime P.solverAdapterTime P.dynamicTime
    P.handlerTickTime P.callerTickTime P.extractionTickTime P.headerWidth le_rfl P.queryCapacity
    P.values P.ops P.handlerCaps P.solverCaps P.dynamicSamples P.storeCapacity P.badHandlerComparison
    P.extractionComparison P.requestWidth P.stateWidth P.headWidth
    P.sampleTime P.callerTick P.badHandlerTick P.extractionTick A.source A.corresponds
    P.instructionSize P.handlerPortSize P.solverPortSize P.instructionDescriptions P.handlerDescriptions P.solverDescriptions
  exact ⟨⟨hchallenge, Within.mono P.backend P.descriptionSizes P.factor P.description
    goodCertificate hcode le_rfl⟩, ⟨hchallenge,
    Within.mono P.backend P.descriptionSizes P.factor P.description badCertificate hcode le_rfl⟩⟩

theorem reduction_advantages :
    Model.dlog11Advantage P.generator P.keyGenerator
      (Model.LazyAGM.WeightedReduction.goodReductionList (index.sourceTerms P.cost) A.source) ≤
        P.dlogBound P.goodTime ∧
    Model.dlog11Advantage P.generator P.keyGenerator
      (Model.LazyAGM.WeightedReduction.badReductionList (index.sourceTerms P.cost) A.source) ≤
        P.dlogBound P.badTime := by
  obtain ⟨goodFits, badFits⟩ := reductions_within P A
  exact ⟨Model.le_advantageBound _ _ _ goodFits, Model.le_advantageBound _ _ _ badFits⟩

theorem reduction_advantages_of_hardness (goodEpsilon badEpsilon : ENNReal)
    (goodHardness : Model.HardWithin (Model.dlog11Advantage (F := F) P.generator P.keyGenerator)
      (dlogWithin P.rep P.backend P.descriptionSizes P.factor P.description
        P.generator P.keyGenerator P.inputWidth P.solverCode) P.goodTime goodEpsilon)
    (badHardness : Model.HardWithin (Model.dlog11Advantage (F := F) P.generator P.keyGenerator)
      (dlogWithin P.rep P.backend P.descriptionSizes P.factor P.description
        P.generator P.keyGenerator P.inputWidth P.solverCode) P.badTime badEpsilon) :
    Model.dlog11Advantage P.generator P.keyGenerator
      (Model.LazyAGM.WeightedReduction.goodReductionList (index.sourceTerms P.cost) A.source) ≤ goodEpsilon ∧
    Model.dlog11Advantage P.generator P.keyGenerator
      (Model.LazyAGM.WeightedReduction.badReductionList (index.sourceTerms P.cost) A.source) ≤ badEpsilon := by
  obtain ⟨goodFits, badFits⟩ := reductions_within P A
  exact ⟨goodHardness _ goodFits, badHardness _ badFits⟩

end Signatures.Runtime.WeightedAGM.General
