import Signatures.Schnorr.GeneralSecurityModel
import Signatures.Schnorr.Proofs.GeneralAGM

/-! Proofs for the public Schnorr AGM statement. The displayed game is exactly
the source game, and the constructed solver belongs to the displayed resource
class by the complete native runtime and stored-code proofs. -/

open OracleComp OracleSpec PFunctor
open Signatures.Runtime Signatures.Runtime.BackendProgram
open Signatures.Runtime.SchnorrAGM.Native

namespace Schnorr

universe v w x

variable (curve : Model.CyclicCurve) [model : AGMSecurityModel.{v, w, x} curve]

theorem AlgebraicAdversary.query_allowances (securityParameter : Nat) (queries : QueryAllowance)
    (adversary : AlgebraicAdversary curve securityParameter queries) :
    (∀ pk, IsQueryBoundP (adversary.source.main (AGM.initial (curve.generator securityParameter) pk))
      (fun q => GeneralAGM.randomRequest q = true) queries.random) ∧
    (∀ pk, IsQueryBoundP (adversary.source.main (AGM.initial (curve.generator securityParameter) pk))
      (fun q => AGM.Reduction.hashRequest q = true) queries.hash) ∧
    (∀ pk, IsQueryBoundP (adversary.source.main (AGM.initial (curve.generator securityParameter) pk))
      (fun q => AGM.Reduction.signRequest q = true) queries.sign) := by
  simpa only [AGMSecurityModel.queries_eq, AGMSecurityModel.generator_eq] using
    And.intro adversary.randomQueries (And.intro adversary.hashQueries adversary.signingQueries)

theorem agmEufCmaGame_eq (securityParameter : Nat) {queries : QueryAllowance}
    (adversary : AlgebraicAdversary curve securityParameter queries) :
    agmEufCmaGame curve securityParameter adversary = AGM.game (curve.generator securityParameter) adversary.source := by
  simp only [agmEufCmaGame, AGM.game, AGM.experiment]
  congr! 8
  funext motive groups singleton fallback
  cases groups with
  | nil => rfl
  | cons R rest => cases rest <;> rfl

theorem Proofs.agm_security
    (curve : Model.CyclicCurve) [model : AGMSecurityModel curve]
    (securityParameter : Nat) (queries : QueryAllowance)
    (adversary : AlgebraicAdversary curve securityParameter queries) :
    𝒟[agmEufCmaGame curve securityParameter adversary] {true} ≤
      dlogSuccessBound curve securityParameter queries (agmReductionTime curve securityParameter queries) +
      (queries.hash + 1 : ENNReal) * (curve.order securityParameter : ENNReal)⁻¹ +
      (queries.sign : ENNReal) * (queries.sign + queries.hash) * (curve.order securityParameter : ENNReal)⁻¹ := by
  let resources := model.parameters securityParameter queries
  have probabilityBound := SchnorrAGM.security resources.generator resources.generates.1 adversary.source
    resources.queries.sign resources.queries.hash adversary.signingQueries adversary.hashQueries
  have fits := GeneralAGM.reduction_within resources adversary
  have hdlog : 𝒟[DiffieHellman.dlogExperiment resources.generator (SchnorrAGM.dlogReduction adversary.source)] {true} ≤
      dlogSuccessBound curve securityParameter queries resources.solverTime :=
    le_iSup_of_le _ (le_iSup_of_le fits le_rfl)
  simpa only [resources, agmEufCmaGame_eq, AGMSecurityModel.generator_eq, AGMSecurityModel.queries_eq,
    Model.CyclicCurve.order, agmReductionTime] using
    probabilityBound.trans (add_le_add (add_le_add hdlog le_rfl) le_rfl)

theorem dlogSuccessBound_mono (securityParameter : Nat) (queries : QueryAllowance) :
    Monotone (dlogSuccessBound curve securityParameter queries) := by
  intro time largerTime ht
  let resources := model.parameters securityParameter queries
  refine iSup_le fun solver => iSup_le fun fits => ?_
  have largerFits : Solver.dlogWithin
      resources.rep resources.backend resources.descriptionSizes resources.factor resources.description
      resources.generator resources.inputWidth resources.solverCode largerTime solver :=
    ⟨fits.1, Within.mono resources.backend resources.descriptionSizes resources.factor resources.description fits.2 le_rfl ht⟩
  exact le_iSup_of_le solver (le_iSup_of_le largerFits le_rfl)

end Schnorr
