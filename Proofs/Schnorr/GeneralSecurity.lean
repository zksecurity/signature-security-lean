import Signatures.Schnorr.GeneralSecurityModel
import Proofs.Schnorr.CaliperAGM
import Proofs.Schnorr.Game

/-! Public Schnorr AGM proofs. The displayed game equals the shared-AGM
source game. The actual Caliper reduction meets its derived code, time and
total-memory limits. -/
namespace Schnorr
open OracleComp OracleSpec
variable (curve : Model.CyclicCurve) [model : AGMSecurityModel curve]

theorem AlgebraicAdversary.query_allowances (securityParameter : Nat) (queries : QueryAllowance)
    (adversary : AlgebraicAdversary curve securityParameter queries) :
    (∀ pk, IsQueryBoundP (adversary.source.main (AGM.initial (curve.generator securityParameter) pk))
      (fun q => CaliperAGM.randomRequest q = true) queries.random) ∧
    (∀ pk, IsQueryBoundP (adversary.source.main (AGM.initial (curve.generator securityParameter) pk))
      (fun q => AGM.Reduction.hashRequest q = true) queries.hash) ∧
    (∀ pk, IsQueryBoundP (adversary.source.main (AGM.initial (curve.generator securityParameter) pk))
      (fun q => AGM.Reduction.signRequest q = true) queries.sign) :=
  ⟨adversary.randomQueries, adversary.hashQueries, adversary.signingQueries⟩

theorem agmEufCmaGame_eq (securityParameter : Nat) {queries : QueryAllowance}
    (adversary : AlgebraicAdversary curve securityParameter queries) :
    agmEufCmaGame curve securityParameter adversary = AGM.game (curve.generator securityParameter) adversary.source :=
  Game.agm_eq_source curve securityParameter adversary.source

theorem Proofs.agm_security
    (curve : Model.CyclicCurve) [model : AGMSecurityModel curve]
    (securityParameter : Nat) (queries : QueryAllowance)
    (adversary : AlgebraicAdversary curve securityParameter queries) :
    𝒟[agmEufCmaGame curve securityParameter adversary] {true} ≤
      𝒟[DiffieHellman.dlogExperiment (curve.generator securityParameter) (agmReduction curve adversary)] {true} +
      (queries.hash + 1 : ENNReal) * (curve.order securityParameter : ENNReal)⁻¹ +
      (queries.sign : ENNReal) * (queries.sign + queries.hash) * (curve.order securityParameter : ENNReal)⁻¹ := by
  simpa only [agmEufCmaGame_eq, agmReduction, Model.CyclicCurve.order] using
    Signatures.Runtime.SchnorrAGM.security (curve.generator securityParameter) (curve.generates securityParameter).1
      adversary.source queries.sign queries.hash adversary.signingQueries adversary.hashQueries

theorem Proofs.agm_reduction_within
    (curve : Model.CyclicCurve) [model : AGMSecurityModel curve]
    (securityParameter : Nat) (queries : QueryAllowance)
    (adversary : AlgebraicAdversary curve securityParameter queries) :
    DLogSolverWithin curve securityParameter queries (agmReductionTime curve securityParameter queries)
      (agmReduction curve adversary) :=
  CaliperAGM.reduction_within (model.parameters securityParameter queries) adversary

end Schnorr
