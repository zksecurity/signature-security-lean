import Signatures.BLS.GeneralAGMParameters

/-! BLS AGM security for general realized attackers at explicit resource/query
allowances. The supporting parameters fix the curve, backend, primitive prices,
and encodings. The bound uses maximum DLog advantage in that same backend at
the derived solver budgets. Numerical hardness assumptions can bound those
terms separately; no completed solver's efficiency is assumed. -/

open OracleComp OracleSpec PFunctor
open Signatures.Runtime Signatures.Runtime.BackendProgram
open Signatures.Runtime.LazyAGM.NativeSolver

namespace BLS.GeneralAGM

universe v w x

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [Q.HasProd] [Q.HasSum] [Q.HasOption] [Q.IsDistributive] [OptionCode (Q := Q)]
  {F G₁ G₂ Gₜ M : Type} [Field F] [SampleableType F] [Fintype F]
  [SampleableType G₁] [Fintype G₁]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq Gₜ] [DecidableEq M]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [AddCommGroup Gₜ] [Module F Gₜ] [AlgebraicGroupModel.BilinearPairing F G₁ G₂ Gₜ]

/-- At the declared curve, resource limits, and query allowances, any realized
algebraic adversary has success bounded by the two DLog terms and `1 / |F|`. -/
theorem security (P : Parameters (Q := Q) (F := F) (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ) (M := M))
    (A : AlgebraicAdversary P) :
    𝒟[BLS.LazyAGM.game (Gₜ := Gₜ) P.generator P.keyGenerator A.source] {true} ≤ P.securityBound := by
  have hchallenge : ∀ x : F,
      Q.size (P.rep.env inputTypes) (P.generator, x • P.generator, P.keyGenerator, x • P.keyGenerator, ()) ≤
        P.inputWidth := by
    intro x
    have h := challenge_size P.rep P.sizes P.width P.width P.width
      P.values.point₁ P.values.point₂ P.values.unit P.generator P.keyGenerator x
    have hh := P.headerWidth
    have hi := P.inputCapacity
    omega
  have hcode : P.factor * programDescription
      (P.descriptionSizes.localSize A.caller.initCode + 2 * P.descriptionSizes.localSize A.caller.headCode +
        P.descriptionSizes.localSize A.caller.updateCode)
      (P.sampling.scalar.descriptionSize P.descriptionSizes) (P.sampler.code.descriptionSize P.descriptionSizes)
      P.queries.total P.allowance P.instructionSize P.handlerPortSize P.solverPortSize ≤ P.solverCode := by
    apply Nat.mul_le_mul_left
    have h := A.storedCode
    dsimp only [programDescription]
    omega
  exact security_of_resources P.rep P.bd P.ports P.sampler P.boundary P.data P.cost P.primitive P.sampling
    P.control P.queryCost P.sizes P.lists P.lengths P.laws P.dataLaws P.primitiveBound P.mono P.routing P.dispatch
    A.caller P.execution A.runs P.recovery P.backend P.descriptionSizes P.factor P.description
    P.allowance P.descriptionLaws P.descriptionData P.descriptionDispatch
    P.inputWidth P.width P.outputWidth P.routeWidth P.queries.total P.queries.total P.messageWidth
    P.comparisonTime P.scalarTime P.opTime P.handlerAdapterTime P.solverAdapterTime P.dynamicTime
    P.callerTickTime P.extractionTickTime P.headerWidth le_rfl P.values P.ops P.handlerCaps P.solverCaps
    P.dynamicSamples P.storeCapacity P.handlerComparison P.extractionComparison P.requestWidth P.stateWidth P.headWidth
    P.sampleTime P.callerTick P.extractionTick P.queryCapacity A.program A.realizes A.source A.corresponds
    P.instructionSize P.handlerPortSize P.solverPortSize P.instructionDescriptions P.handlerDescriptions P.solverDescriptions
    P.generator P.keyGenerator P.generates P.pairingInjective hchallenge
    P.solverCode P.goodTime P.badTime (P.dlogBound P.goodTime) (P.dlogBound P.badTime) hcode le_rfl le_rfl
    (Model.hardWithin_advantageBound _ _ _) (Model.hardWithin_advantageBound _ _ _)

end BLS.GeneralAGM

namespace BLS.GeneralAGM.Family

universe v w x

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [Q.HasProd] [Q.HasSum] [Q.HasOption] [Q.IsDistributive] [OptionCode (Q := Q)]
  {F G₁ G₂ Gₜ M : Nat → Type}
  [∀ n, Field (F n)] [∀ n, SampleableType (F n)] [∀ n, Fintype (F n)]
  [∀ n, SampleableType (G₁ n)] [∀ n, Fintype (G₁ n)]
  [∀ n, DecidableEq (F n)] [∀ n, DecidableEq (G₁ n)] [∀ n, DecidableEq (G₂ n)]
  [∀ n, DecidableEq (Gₜ n)] [∀ n, DecidableEq (M n)]
  [∀ n, AddCommGroup (G₁ n)] [∀ n, Module (F n) (G₁ n)]
  [∀ n, AddCommGroup (G₂ n)] [∀ n, Module (F n) (G₂ n)]
  [∀ n, AddCommGroup (Gₜ n)] [∀ n, Module (F n) (Gₜ n)]
  [∀ n, AlgebraicGroupModel.BilinearPairing (F n) (G₁ n) (G₂ n) (Gₜ n)]

/-- Concrete security at any selected security parameter. This pointwise
statement imposes no asymptotic claim on arbitrary parameter families. -/
theorem security
    (parameters : ∀ n, Parameters (Q := Q) (F := F n) (G₁ := G₁ n) (G₂ := G₂ n) (Gₜ := Gₜ n) (M := M n))
    (securityParameter : Nat) (A : AlgebraicAdversary (parameters securityParameter)) :
    𝒟[BLS.LazyAGM.game (Gₜ := Gₜ securityParameter)
      (parameters securityParameter).generator (parameters securityParameter).keyGenerator A.source] {true} ≤
      (parameters securityParameter).securityBound :=
  BLS.GeneralAGM.security (parameters securityParameter) A

end BLS.GeneralAGM.Family
