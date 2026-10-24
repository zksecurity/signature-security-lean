import Signatures.Schnorr.GeneralNonzeroROMParameters
import Proofs.Model.ForkingLoss

/-! The nonzero-nonce ROM reduction meets the model's derived budgets for every
implemented unrestricted attacker. Both the original quadratic bound and its
direct square-root consequence follow without assuming reduction efficiency. -/

open OracleComp OracleSpec PFunctor
open Signatures.Runtime Signatures.Runtime.BackendProgram
open Signatures.Runtime.Schnorr ListROM RawTape

namespace Schnorr.NonzeroNonce.GeneralROM

universe v w x

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [Q.HasProd] [Q.HasSum] [Q.HasOption] [Q.IsDistributive] [OptionCode (Q := Q)]
  {F G M : Type} [Field F] [SampleableType F] [SampleableType Fˣ] [SampleableType G]
  [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] [DecidableEq M]

theorem reduction_within (P : Parameters (Q := Q) (F := F) (G := G) (M := M))
    (A : UnrestrictedAdversary P) :
    ListROM.NativeSolver.dlogWithin P.rep P.backend P.descriptionSizes P.factor P.description
      P.generator P.inputWidth P.solverCode P.solverTime
      (NonzeroListROM.NativeSolver.reduction (G₂ := G) (K := M) A.source.main P.queries.hash) := by
  have hchallenge : ∀ x : F,
      Q.size (P.rep.env ListROM.NativeSolver.inputTypes) (P.generator, x • P.generator, ()) ≤ P.inputWidth := by
    intro x
    exact (ListROM.NativeSolver.challenge_size P.rep P.sizes P.groupWidth P.tapeWidth
      P.groupSize P.first.hu P.generator x).trans P.inputCapacity
  have hd := NonzeroListROM.NativeSolver.DescriptionInputs.solver_withCaller
    (NonzeroListROM.NativeSolver.descriptionInputs P.rep P.cost P.primitive P.sampler P.nonzeroSampler P.descriptionSizes P.bd P.boundary
      P.ports P.uniform P.privatePorts A.caller)
    P.callerCodeLimit P.allowance P.queries.total P.queries.hash A.storedCode
  have hcode : P.factor * (NonzeroListROM.NativeSolver.descriptionInputs P.rep P.cost P.primitive P.sampler P.nonzeroSampler P.descriptionSizes
      P.bd P.boundary P.ports P.uniform P.privatePorts A.caller).solver P.allowance P.queries.total P.queries.hash ≤
      P.solverCode := Nat.mul_le_mul_left P.factor hd
  have certificate := NonzeroListROM.NativeSolver.program_within P.rep P.sizes P.lists P.bd P.boundary P.ports P.data
    P.cost P.primitive P.uniform P.privatePorts P.sampler P.nonzeroSampler P.sampleLaw P.nonzeroLaw P.laws P.dataLaws P.primitiveBound
    P.mono P.control P.queryCost P.routing P.dispatch A.caller P.recovery P.execution A.runs
    P.backend P.descriptionSizes P.factor P.description P.allowance P.descriptionLaws P.descriptionData P.descriptionDispatch
    P.inputWidth P.width P.tapeWidth P.queries.total P.queries.total P.queries.total P.queries.hash P.first P.second
    P.scaleTime P.addTime P.messageTime P.pointTime P.incrementTime P.comparisonTime P.scalarComparisonTime P.subtractTime
    P.extractionScalarTime P.fieldSubTime P.divTime P.selectorOps P.extractionOps P.indexSize P.scalarComparison
    P.indexSubtraction P.rejectionCost P.acceptanceCost P.inputFits P.queryCapacity A.source.main A.realizes
  exact ⟨hchallenge, Within.mono P.backend P.descriptionSizes P.factor P.description certificate hcode le_rfl⟩

variable [Fintype F]

theorem security_quadratic (P : Parameters (Q := Q) (F := F) (G := G) (M := M))
    (A : UnrestrictedAdversary P) :
    let eps := 𝒟[NonzeroNonce.game P.generator A.source] {true} -
      (P.queries.sign : ENNReal) * (P.queries.sign + P.queries.hash) * ((Fintype.card F - 1 : Nat) : ENNReal)⁻¹
    eps * (eps / (P.queries.hash + 1 : ENNReal) - (Fintype.card F : ENNReal)⁻¹) ≤ P.dlogBound P.solverTime := by
  have fits := reduction_within P A
  have hdlog := Model.le_advantageBound
    (fun solver => 𝒟[DiffieHellman.dlogExperiment P.generator solver] {true}) _ _ fits
  change 𝒟[DiffieHellman.dlogExperiment P.generator
    (NonzeroListROM.NativeSolver.reduction (G₂ := G) (K := M) A.source.main P.queries.hash)] {true} ≤ P.dlogBound P.solverTime at hdlog
  rw [NonzeroListROM.NativeSolver.reduction_experiment (G₂ := G) (K := M) P.generator A.source P.queries.hash] at hdlog
  exact (NonzeroNonce.LazyROM.security P.generator P.generates A.source P.queries.sign P.queries.hash
    (fun pk => ⟨A.signingQueries pk, A.hashQueries pk⟩)).trans hdlog

theorem security (P : Parameters (Q := Q) (F := F) (G := G) (M := M))
    (A : UnrestrictedAdversary P) :
    𝒟[NonzeroNonce.game P.generator A.source] {true} ≤
      (P.queries.sign : ENNReal) * (P.queries.sign + P.queries.hash) * ((Fintype.card F - 1 : Nat) : ENNReal)⁻¹ +
      (P.queries.hash + 1 : ENNReal) * (Fintype.card F : ENNReal)⁻¹ +
      ((P.queries.hash + 1 : ENNReal) * P.dlogBound P.solverTime) ^ (1 / 2 : ℝ) := by
  apply Model.forking_inverse P.queries.hash
  · exact MeasureTheory.measure_ne_top _ _
  · exact ENNReal.inv_ne_top.mpr (by positivity)
  · exact security_quadratic P A

end Schnorr.NonzeroNonce.GeneralROM
