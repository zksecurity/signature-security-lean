import Signatures.BLS.GeneralSecurityModel
import Signatures.BLS.Proofs.CaliperAGM
import Signatures.BLS.Proofs.CaliperCoCDH
import Signatures.BLS.CoCDH.Proofs.ArbitraryMessages
import Signatures.BLS.Proofs.ROM
import Signatures.BLS.Proofs.EufCma
import Signatures.BLS.Proofs.Game

/-! Proofs for the public BLS AGM/DLog and unrestricted co-CDH statements.
First connect the displayed games and allowances to the original source games.
Then combine their probability reductions with constructed native resource
certificates and membership in the explicit hardness suprema. -/

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

/-- Every algebraic attacker within the declared resources and query allowances obeys
this EUF-CMA bound. `goodTime` and `badTime` are the complete derived reduction times.
The good branch extracts from a nonzero denominator. The bad branch uses independent
affine masks to handle the zero-denominator case; the proof's remaining loss is `1/|F|`. -/
theorem Proofs.agm_security
    (curve : Model.PairingCurve) [model : AGMSecurityModel curve]
    (securityParameter : Nat)
    (queries : QueryAllowance)
    (adversary : AlgebraicAdversary curve securityParameter queries) :
    let resources := model.parameters securityParameter queries
    𝒟[agmEufCmaGame curve securityParameter adversary] {true} ≤
      dlogSuccessBound curve securityParameter queries resources.goodTime +
      dlogSuccessBound curve securityParameter queries resources.badTime +
      1 / (curve.order securityParameter : ENNReal) := by
  let resources := model.parameters securityParameter queries
  -- Probability: the two explicit lazy reductions account for every successful forgery,
  -- apart from the original inverse-field-size loss. This step has no efficiency premise.
  have probabilityBound := LazyAGM.Reduction.security_arbitrary_messages_list
    (curve.generator securityParameter) (curve.keyGenerator securityParameter)
    adversary.proofView (curve.generates securityParameter) (curve.pairingInjective securityParameter)
  -- Efficiency: construct both Caliper programs and prove their code/time/total-memory bounds.
  obtain ⟨goodFits, badFits⟩ := CaliperAGM.reductions_within resources adversary
  -- Each constructed solver is therefore a member of the supremum above.
  have goodBound : Model.dlog11Advantage (curve.generator securityParameter)
      (curve.keyGenerator securityParameter) (LazyAGM.Reduction.goodReductionList adversary.proofView) ≤
      dlogSuccessBound curve securityParameter queries resources.goodTime :=
    le_iSup_of_le _ (le_iSup_of_le goodFits le_rfl)
  have badBound : Model.dlog11Advantage (curve.generator securityParameter)
      (curve.keyGenerator securityParameter) (LazyAGM.Reduction.badReductionList adversary.proofView) ≤
      dlogSuccessBound curve securityParameter queries resources.badTime :=
    le_iSup_of_le _ (le_iSup_of_le badFits le_rfl)
  have sourceBound := Model.DirectAGM.game_le (Gₜ := curve.TargetGroup securityParameter) LazyAGM.terms (fun _ _ => True)
    (curve.generator securityParameter) (curve.keyGenerator securityParameter) adversary.source
  simpa only [agmEufCmaGame_eq, Model.PairingCurve.order] using
    sourceBound.trans (probabilityBound.trans (add_le_add (add_le_add goodBound badBound) le_rfl))

/-- Increasing only the time allowance enlarges the same Caliper solver class.
Its layouts, stored-code and total-memory bounds stay fixed. -/
theorem dlogSuccessBound_mono (securityParameter : Nat) (queries : QueryAllowance) :
    Monotone (dlogSuccessBound curve securityParameter queries) := by
  intro time largerTime ht
  let resources := model.parameters securityParameter queries
  exact CaliperBackend.dlogSuccessBound_mono resources.layout.port
    resources.layout.setup.challenge resources.layout.scheme.cache.value
    (curve.generator securityParameter) (curve.keyGenerator securityParameter) le_rfl le_rfl ht

/-- Both DLog solvers fit the maximum of their derived runtimes, yielding one
hardness quantity with a factor of two. The separate-budget theorem is sharper. -/
theorem Proofs.agm_security_common_budget
    (curve : Model.PairingCurve) [model : AGMSecurityModel curve]
    (securityParameter : Nat) (queries : QueryAllowance)
    (adversary : AlgebraicAdversary curve securityParameter queries) :
    𝒟[agmEufCmaGame curve securityParameter adversary] {true} ≤
      2 * dlogSuccessBound curve securityParameter queries
        (agmReductionTime curve securityParameter queries) +
      1 / (curve.order securityParameter : ENNReal) := by
  let resources := model.parameters securityParameter queries
  have goodBound := dlogSuccessBound_mono curve securityParameter queries
    (Nat.le_max_left resources.goodTime resources.badTime)
  have badBound := dlogSuccessBound_mono curve securityParameter queries
    (Nat.le_max_right resources.goodTime resources.badTime)
  have bound := (Proofs.agm_security curve securityParameter queries adversary).trans
    (add_le_add (add_le_add goodBound badBound) le_rfl)
  simpa only [two_mul, agmReductionTime, resources] using bound

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

/-- Every unrestricted attacker within the declared resources and query allowances
obeys this EUF-CMA bound. `solverTime` charges the complete Caliper Coron reduction,
including the caller, lazy oracle simulation, setup and extraction. For `s` signing
queries, `coronFactor s = ((s+1)⁻¹ * (s/(s+1))^s)⁻¹`, approximately `e*s`
for large `s` and exactly `1` when `s = 0`. -/
theorem Proofs.cocdh_security
    (curve : Model.PairingCurve) [model : CoCDHSecurityModel curve]
    (securityParameter : Nat) (queries : QueryAllowance)
    (adversary : UnrestrictedAdversary curve securityParameter queries) :
    let resources := model.parameters securityParameter queries
    𝒟[cocdhEufCmaGame curve securityParameter adversary] {true} ≤
      Model.coronFactor queries.sign *
        coCDHSuccessBound curve securityParameter queries resources.solverTime := by
  let resources := model.parameters securityParameter queries
  -- Construct the complete Caliper code/time/total-memory witness, including challenge coverage.
  have fits := CaliperCoCDH.reduction_within resources adversary (curve.generates securityParameter).surjective
  have solverBound : Model.coCDHAdvantage (F := curve.Scalar securityParameter)
      (curve.generator securityParameter) (curve.keyGenerator securityParameter)
      (CoCDH.coronReductionLazyPK (F := curve.Scalar securityParameter) queries.sign
        (BLS.ROM.cacheForgeryPK adversary.source)) ≤
      coCDHSuccessBound curve securityParameter queries resources.solverTime :=
    le_iSup_of_le _ (le_iSup_of_le fits le_rfl)
  exact (Proofs.cocdh_probability curve securityParameter queries adversary).trans
    (mul_le_mul_right solverBound (Model.coronFactor queries.sign))

end CoCDH

end BLS
