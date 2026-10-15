import Signatures.Schnorr.GeneralAGMParameters

/-! The complete native reduction meets the derived resource bounds. Only
local operation/encoding contracts and the attacker's own resources are assumed. -/

open OracleComp OracleSpec PFunctor
open Signatures.Runtime Signatures.Runtime.BackendProgram
open Signatures.Runtime.SchnorrAGM.Native
open Signatures.Runtime.SchnorrAGM.Native.Interface

namespace Schnorr.GeneralAGM

universe v w x

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [Q.HasProd] [Q.HasSum] [Q.HasOption] [Q.IsDistributive] [OptionCode (Q := Q)]
  {F G M : Type} [Field F] [SampleableType F] [Fintype F]
  [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] [DecidableEq M]
  [DecidableEq (SourceRequest F G M)]

omit [Fintype F] in
theorem reduction_within (P : Parameters (Q := Q) (F := F) (G := G) (M := M))
    (A : AlgebraicAdversary P) :
    Solver.dlogWithin P.rep P.backend P.descriptionSizes P.factor P.description
      P.generator P.inputWidth P.solverCode P.solverTime (SchnorrAGM.dlogReduction A.source) := by
  have hchallenge : ∀ x : F,
      Q.size (P.rep.env Solver.inputTypes) (P.generator, x • P.generator, ()) ≤ P.inputWidth := by
    intro x
    have h := Solver.challenge_size P.rep P.sizes P.width P.width
      P.primitives.point P.primitives.unit P.generator x
    have hh := P.headerWidth
    have hi := P.inputCapacity
    omega
  have hcode : P.factor * Solver.programDescription
      (P.descriptionSizes.localSize A.caller.initCode + 2 * P.descriptionSizes.localSize A.caller.headCode +
        P.descriptionSizes.localSize A.caller.updateCode)
      (P.sampler.descriptionSize P.descriptionSizes) P.randomPortSize P.handlerPortSize P.solverPortSize
      P.queries.total P.allowance P.instructionSize ≤ P.solverCode := by
    apply Nat.mul_le_mul_left
    have h := A.storedCode
    dsimp only [Solver.programDescription]
    omega
  have certificate := Solver.program_within P.rep P.bd P.boundary P.data P.cost P.primitive
    P.ports P.randomPorts P.sampler A.caller P.sizes P.lists P.lengths P.payloads
    P.laws P.dataLaws P.primitiveBound P.mono P.control P.queryCost P.routing P.dispatch
    P.recovery P.execution A.runs P.backend P.descriptionSizes P.factor P.description
    P.allowance P.descriptionLaws P.descriptionData P.descriptionDispatch
    P.inputWidth P.width P.outputWidth P.routeWidth P.queries.total (P.queries.total + 2) P.queries.total
    P.width P.width P.width P.arityCap P.portWidth P.queries.total P.tickTime P.adapterTime P.divisionTime P.times
    P.headerWidth le_rfl le_rfl le_rfl P.routeCapacity P.handlerCaps P.solverCaps P.primitives
    P.requestWidth P.requestWidth P.requestWidth P.requestWidth P.randomArity P.stateWidth P.headWidth
    P.tick P.oneTime P.messageComparison P.pointComparison P.subtractionTime P.fieldDivisionTime
    P.sampleLaw P.queryCapacity A.source A.realizes
    P.instructionSize P.randomPortSize P.handlerPortSize P.solverPortSize
    P.instructionDescriptions P.randomRequestDescription P.randomResponseDescription P.handlerDescriptions P.solverDescriptions
  exact ⟨hchallenge, Within.mono P.backend P.descriptionSizes P.factor P.description certificate hcode le_rfl⟩

theorem security (P : Parameters (Q := Q) (F := F) (G := G) (M := M))
    (A : AlgebraicAdversary P) :
    𝒟[AGM.game P.generator A.source] {true} ≤ P.dlogBound P.solverTime +
      (P.queries.hash + 1 : ENNReal) * (Fintype.card F : ENNReal)⁻¹ +
      (P.queries.sign : ENNReal) * (P.queries.sign + P.queries.hash) * (Fintype.card F : ENNReal)⁻¹ := by
  have fits := reduction_within P A
  have hdlog := Model.le_advantageBound
    (fun solver => 𝒟[DiffieHellman.dlogExperiment P.generator solver] {true}) _ _ fits
  exact (SchnorrAGM.security P.generator P.generates.1 A.source P.queries.sign P.queries.hash
    A.signingQueries A.hashQueries).trans (add_le_add (add_le_add hdlog le_rfl) le_rfl)

end Schnorr.GeneralAGM
