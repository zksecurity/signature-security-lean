import Signatures.SynchronizedPS.Game
import Signatures.SynchronizedPS.CaliperAGMParameters

/-! Inspectable games and Caliper DLog bounds for synchronized PS. The mathematical curve and
period type stay explicit. Fixed local implementations, encodings and caller allowances determine
the four complete reduction time, code and memory bounds. The game stays independent of these
implementation contracts. -/

open OracleComp OracleSpec
open Signatures.Runtime

namespace SynchronizedPS

abbrev QueryAllowance := WeightedCaliper.QueryAllowance

/-- Caliper layouts, local implementations and caller allowances for a period type with
decidable equality, fixed before choosing the attacker. The four reductions and their bounds are
constructed from these components; no completed-solver contract or hardness assumption is a
field. -/
class AGMSecurityModel (curve : Model.PairingCurve) where
  Period : Nat → Type
  [periodEquality : ∀ n, DecidableEq (Period n)]
  parameters : ∀ n q, CaliperAGM.Parameters
    (curve.Scalar n) (curve.SignatureGroup n) (curve.KeyGroup n) (Period n)
    q (curve.generator n) (curve.keyGenerator n)

attribute [instance_reducible, instance] AGMSecurityModel.periodEquality

variable (curve : Model.PairingCurve) [model : AGMSecurityModel curve]

/-- A realized algebraic attacker within the model's execution, stored-code, memory and signing
limits. It attacks the single honest signer, reporting no co-signer keys; its source retains the
game's interface. -/
abbrev AlgebraicAdversary (securityParameter : Nat) (queries : QueryAllowance) :=
  SyncWrapCaliper.AlgebraicAdversary (model.parameters securityParameter queries)

/-- Maximum of the four complete runtime bounds proved for the constructed solvers. -/
def agmReductionTime (securityParameter : Nat) (queries : QueryAllowance) : Nat :=
  let resources := model.parameters securityParameter queries
  max (max resources.goodTime₁ resources.badTime₁) (max resources.goodTime₂ resources.badTime₂)

/-- The algebraic EUF-CMA experiment of `Game.lean` at the attacker's source. -/
noncomputable def agmEufCmaGame (securityParameter : Nat) {queries : QueryAllowance}
    (adversary : AlgebraicAdversary curve securityParameter queries) : ProbComp Bool :=
  Game.agm curve securityParameter adversary.source

/-- Supremum of `(1,1)`-DLog success for Caliper solvers receiving `(g₁, x • g₁, g₂, x • g₂)`
within the derived code and memory bounds and the given time. Every sampled challenge is
representable, as proved from the scalar sampler and the key scaling. -/
noncomputable def dlogSuccessBound (securityParameter : Nat) (queries : QueryAllowance) (time : Nat) : ENNReal :=
  let resources := model.parameters securityParameter queries
  ⨆ solver, ⨆ (_ : CaliperBackend.dlogWithin resources.outer.port resources.shape.challenge resources.outer.good.extraction.scalar
      (curve.generator securityParameter) (curve.keyGenerator securityParameter)
      resources.solverCode resources.solverMemory time solver),
    𝒟[AlgebraicGroupModel.dlog11Exp (curve.generator securityParameter) (curve.keyGenerator securityParameter) solver] {true}

end SynchronizedPS
