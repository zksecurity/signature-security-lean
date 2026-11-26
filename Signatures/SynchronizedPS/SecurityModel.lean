import Signatures.SynchronizedPS.Game
import Signatures.SynchronizedPS.CaliperAGMParameters

/-! Inspectable games, the four Caliper DLog reductions and their budget for synchronized PS. The
mathematical curve and period type stay explicit. Fixed local implementations, encodings and caller allowances determine
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
limits; its source retains the game's interface. -/
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

/-- The scheme₁ (`x•H(t)`, second key known) good-branch `(1,1)`-DLog solver built from the
attacker: it draws the known key, runs the wrapped attacker once inside the keyed weighted good
program and solves from the forgery's algebraic explanation. The four solvers are constructed in
`Proofs/Runtime/Caliper/SyncWrapSecurity.lean`. -/
noncomputable def goodReduction₁ {securityParameter : Nat} {queries : QueryAllowance}
    (adversary : AlgebraicAdversary curve securityParameter queries) :
    AlgebraicGroupModel.DLog11Adversary (curve.Scalar securityParameter) (curve.SignatureGroup securityParameter)
      (curve.KeyGroup securityParameter) :=
  adversary.caliperGood₁

/-- The scheme₁ bad-branch solver: as `goodReduction₁`, but it first resamples the key. -/
noncomputable def badReduction₁ {securityParameter : Nat} {queries : QueryAllowance}
    (adversary : AlgebraicAdversary curve securityParameter queries) :
    AlgebraicGroupModel.DLog11Adversary (curve.Scalar securityParameter) (curve.SignatureGroup securityParameter)
      (curve.KeyGroup securityParameter) :=
  adversary.caliperBad₁

/-- The scheme₂ (`y•(m•H(t))`, first key known) good-branch solver. -/
noncomputable def goodReduction₂ {securityParameter : Nat} {queries : QueryAllowance}
    (adversary : AlgebraicAdversary curve securityParameter queries) :
    AlgebraicGroupModel.DLog11Adversary (curve.Scalar securityParameter) (curve.SignatureGroup securityParameter)
      (curve.KeyGroup securityParameter) :=
  adversary.caliperGood₂

/-- The scheme₂ bad-branch solver. -/
noncomputable def badReduction₂ {securityParameter : Nat} {queries : QueryAllowance}
    (adversary : AlgebraicAdversary curve securityParameter queries) :
    AlgebraicGroupModel.DLog11Adversary (curve.Scalar securityParameter) (curve.SignatureGroup securityParameter)
      (curve.KeyGroup securityParameter) :=
  adversary.caliperBad₂

/-- A `(1,1)`-DLog solver given `(g₁, x • g₁, g₂, x • g₂)` that runs as Caliper code on the fixed
port and layouts within the derived code and memory limits and the given time. Every sampled
challenge must be representable. -/
def DLogSolverWithin (securityParameter : Nat) (queries : QueryAllowance) (time : Nat)
    (solver : AlgebraicGroupModel.DLog11Adversary (curve.Scalar securityParameter)
      (curve.SignatureGroup securityParameter) (curve.KeyGroup securityParameter)) : Prop :=
  (model.parameters securityParameter queries).within time solver

end SynchronizedPS
