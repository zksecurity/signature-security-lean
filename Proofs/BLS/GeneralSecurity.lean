import Signatures.BLS.GeneralSecurityModel
import Proofs.BLS.CaliperAGM
import Proofs.BLS.CaliperCoCDH
import Proofs.BLS.CoCDH.ArbitraryMessages
import Proofs.BLS.ROM
import Proofs.BLS.EufCma
import Proofs.BLS.Game

/-! Proofs for the public BLS AGM/DLog and unrestricted co-CDH statements.
First connect the displayed games and allowances to the original source games.
Then bound each by its named reductions' success, and separately place those
reductions in the Caliper budget from their constructed certificates. -/

open OracleComp OracleSpec PFunctor
open Signatures.Runtime Signatures.Runtime.BackendProgram

namespace BLS

section AGM

variable (curve : Model.PairingCurve) [model : AGMSecurityModel curve]

/-- Each allowance in the public statement bounds that kind of query in the
actual source adversary, at every verification key. -/
theorem AlgebraicAdversary.query_allowances (securityParameter : Nat) (queries : QueryAllowance)
    (adversary : AlgebraicAdversary curve securityParameter queries) :
    (∀ pk, IsQueryBoundP (adversary.source.main (Model.LazyAGM.Interactive.initialInput (curve.generator securityParameter) pk))
      (fun i => queryKind i.value.data = 0) queries.random) ∧
    (∀ pk, IsQueryBoundP (adversary.source.main (Model.LazyAGM.Interactive.initialInput (curve.generator securityParameter) pk))
      (fun i => queryKind i.value.data = 1) queries.hash) ∧
    (∀ pk, IsQueryBoundP (adversary.source.main (Model.LazyAGM.Interactive.initialInput (curve.generator securityParameter) pk))
      (fun i => queryKind i.value.data = 2) queries.sign) := by
  exact ⟨adversary.randomQueries, adversary.hashQueries, adversary.signingQueries⟩

/-- Expanding the public game gives the same native shared-attacker experiment. -/
theorem agmEufCmaGame_eq (securityParameter : Nat) {queries : QueryAllowance}
    (adversary : AlgebraicAdversary curve securityParameter queries) :
    agmEufCmaGame curve securityParameter adversary =
      Model.DirectAGM.game (Gₜ := curve.TargetGroup securityParameter)
        LazyAGM.terms (fun _ _ => True)
        (curve.generator securityParameter) (curve.keyGenerator securityParameter) adversary.source := by
  exact Game.agm_eq_source curve securityParameter adversary.source

/-- Every algebraic attacker obeys this EUF-CMA bound. The good reduction extracts
from a nonzero denominator. The bad one uses independent affine masks for the
zero-denominator case; the remaining loss is `1/|F|`. -/
theorem Proofs.agm_security
    (curve : Model.PairingCurve) [model : AGMSecurityModel curve]
    (securityParameter : Nat)
    (queries : QueryAllowance)
    (adversary : AlgebraicAdversary curve securityParameter queries) :
    𝒟[agmEufCmaGame curve securityParameter adversary] {true} ≤
      𝒟[AlgebraicGroupModel.dlog11Exp (curve.generator securityParameter) (curve.keyGenerator securityParameter)
        (agmGoodReduction curve adversary)] {true} +
      𝒟[AlgebraicGroupModel.dlog11Exp (curve.generator securityParameter) (curve.keyGenerator securityParameter)
        (agmBadReduction curve adversary)] {true} +
      1 / (curve.order securityParameter : ENNReal) := by
  have probabilityBound := LazyAGM.Reduction.security_arbitrary_messages_list
    (curve.generator securityParameter) (curve.keyGenerator securityParameter)
    adversary.proofView (curve.generates securityParameter) (curve.pairingInjective securityParameter)
  have sourceBound := Model.DirectAGM.game_le (Gₜ := curve.TargetGroup securityParameter) LazyAGM.terms (fun _ _ => True)
    (curve.generator securityParameter) (curve.keyGenerator securityParameter) adversary.source
  simpa only [agmEufCmaGame_eq, Model.PairingCurve.order, agmGoodReduction, agmBadReduction,
    Model.dlog11Advantage] using sourceBound.trans probabilityBound

/-- The good reduction is Caliper code within the common budget, the larger of
the two proved complete reduction runtimes. -/
theorem Proofs.agm_good_reduction_within
    (curve : Model.PairingCurve) [model : AGMSecurityModel curve]
    (securityParameter : Nat) (queries : QueryAllowance)
    (adversary : AlgebraicAdversary curve securityParameter queries) :
    DLog11SolverWithin curve securityParameter queries (agmReductionTime curve securityParameter queries)
      (agmGoodReduction curve adversary) :=
  CaliperBackend.dlogWithin.mono
    (CaliperAGM.reductions_within (model.parameters securityParameter queries) adversary).1 le_rfl le_rfl (Nat.le_max_left _ _)

/-- The bad reduction is Caliper code within the same common budget. -/
theorem Proofs.agm_bad_reduction_within
    (curve : Model.PairingCurve) [model : AGMSecurityModel curve]
    (securityParameter : Nat) (queries : QueryAllowance)
    (adversary : AlgebraicAdversary curve securityParameter queries) :
    DLog11SolverWithin curve securityParameter queries (agmReductionTime curve securityParameter queries)
      (agmBadReduction curve adversary) :=
  CaliperBackend.dlogWithin.mono
    (CaliperAGM.reductions_within (model.parameters securityParameter queries) adversary).2 le_rfl le_rfl (Nat.le_max_right _ _)

end AGM

section CoCDH

variable (curve : Model.PairingCurve) [model : CoCDHSecurityModel curve]

/-- The three allowances bound the actual source computation at every public key. -/
theorem UnrestrictedAdversary.query_allowances (securityParameter : Nat) (queries : QueryAllowance)
    (adversary : UnrestrictedAdversary curve securityParameter queries) :
    (∀ pk, IsQueryBoundP (adversary.source pk) (fun i => queryKind i = 0) queries.random) ∧
    (∀ pk, IsQueryBoundP (adversary.source pk) (fun i => queryKind i = 1) queries.hash) ∧
    (∀ pk, IsQueryBoundP (adversary.source pk) (fun i => Sum.isRight i = true) queries.sign) := by
  exact ⟨adversary.randomQueries, adversary.hashQueries, adversary.signingQueries⟩

/-- The same distribution as the established lazy ROM game, whose hash oracle keeps
exponents: a perfect simulation because `g₁` generates. -/
theorem cocdhEufCmaGame_eq (securityParameter : Nat) {queries : QueryAllowance}
    (adversary : UnrestrictedAdversary curve securityParameter queries) :
    𝒟[cocdhEufCmaGame curve securityParameter adversary] =
      𝒟[CoCDH.Tight.blsEufLazyPK (F := curve.Scalar securityParameter) (Gₜ := curve.TargetGroup securityParameter)
        (curve.generator securityParameter) (curve.keyGenerator securityParameter) adversary.source] := by
  rw [cocdhEufCmaGame, Game.eufCma_eq_rom, ROM.game_eq_source]

/-- The original probability inequality, independent of the solver's resource
membership. Both the concrete and family theorems use this same reduction. -/
theorem Proofs.cocdh_probability (securityParameter : Nat) (queries : QueryAllowance)
    (adversary : UnrestrictedAdversary curve securityParameter queries) :
    𝒟[cocdhEufCmaGame curve securityParameter adversary] {true} ≤
      Model.coronFactor queries.sign * Model.coCDHAdvantage (F := curve.Scalar securityParameter)
        (curve.generator securityParameter) (curve.keyGenerator securityParameter)
        (CoCDH.coronReductionLazyPK (F := curve.Scalar securityParameter) queries.sign (ROM.cacheForgeryPK adversary.source)) := by
  have pairingInjective : Function.Injective (fun point : curve.SignatureGroup securityParameter =>
      BilinearGroup.pairing (F := curve.Scalar securityParameter) (Gₜ := curve.TargetGroup securityParameter)
        point (curve.keyGenerator securityParameter)) := by
    intro left right equal
    obtain ⟨a, rfl⟩ := (curve.generates securityParameter).surjective left
    obtain ⟨b, rfl⟩ := (curve.generates securityParameter).surjective right
    have scalars := (curve.pairingInjective securityParameter)
      (by simpa only [BilinearGroup.pairing_smul_left] using equal)
    exact congrArg (fun scalar : curve.Scalar securityParameter => scalar • curve.generator securityParameter) scalars
  rw [cocdhEufCmaGame_eq]
  exact CoCDH.Proofs.security_arbitrary_messages
    (curve.generator securityParameter) (curve.keyGenerator securityParameter) queries.sign adversary.source
    (curve.generates securityParameter) pairingInjective
    (fun r => adversary.signingQueries (r • curve.keyGenerator securityParameter))

/-- Every unrestricted attacker obeys this EUF-CMA bound. For `s` signing queries,
`coronFactor s = ((s+1)⁻¹ * (s/(s+1))^s)⁻¹`, approximately `e*s` for large `s`
and exactly `1` when `s = 0`. -/
theorem Proofs.cocdh_security
    (curve : Model.PairingCurve) [model : CoCDHSecurityModel curve]
    (securityParameter : Nat)
    (queries : QueryAllowance)
    (adversary : UnrestrictedAdversary curve securityParameter queries) :
    𝒟[cocdhEufCmaGame curve securityParameter adversary] {true} ≤
      Model.coronFactor queries.sign *
        𝒟[CoCDH.coCDHExp (curve.generator securityParameter) (curve.keyGenerator securityParameter)
          (cocdhReduction curve adversary)] {true} :=
  Proofs.cocdh_probability curve securityParameter queries adversary

/-- Coron's reduction is Caliper code within its proved complete budget, which
charges the caller, lazy oracle simulation, setup and extraction. -/
theorem Proofs.cocdh_reduction_within
    (curve : Model.PairingCurve) [model : CoCDHSecurityModel curve]
    (securityParameter : Nat) (queries : QueryAllowance)
    (adversary : UnrestrictedAdversary curve securityParameter queries) :
    CoCDHSolverWithin curve securityParameter queries (cocdhReductionTime curve securityParameter queries)
      (cocdhReduction curve adversary) :=
  CaliperCoCDH.reduction_within (model.parameters securityParameter queries) adversary
    (curve.generates securityParameter).surjective

end CoCDH

end BLS
