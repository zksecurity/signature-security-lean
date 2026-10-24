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
      dlogSuccessBound curve securityParameter queries (agmReductionTime curve securityParameter queries) +
      (queries.hash + 1 : ENNReal) * (curve.order securityParameter : ENNReal)⁻¹ +
      (queries.sign : ENNReal) * (queries.sign + queries.hash) * (curve.order securityParameter : ENNReal)⁻¹ := by
  simpa only [agmEufCmaGame_eq, dlogSuccessBound, CaliperAGM.Parameters.dlogBound,
    Signatures.Runtime.CaliperBackend.cyclicDLogSuccessBound, Model.advantageBound,
    Model.CyclicCurve.order, agmReductionTime] using
    CaliperAGM.security (model.parameters securityParameter queries) adversary (curve.generates securityParameter).1

theorem dlogSuccessBound_mono (securityParameter : Nat) (queries : QueryAllowance) :
    Monotone (dlogSuccessBound curve securityParameter queries) :=
  fun _ _ elapsed => Signatures.Runtime.CaliperBackend.cyclicDLogSuccessBound_mono
    (model.parameters securityParameter queries).layout.service.random.port
    (model.parameters securityParameter queries).layout.service.scheme.config
    (model.parameters securityParameter queries).layout.service.scheme.scalar
    (curve.generator securityParameter) le_rfl le_rfl elapsed

end Schnorr
