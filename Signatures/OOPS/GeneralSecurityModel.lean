import Signatures.OOPS.Game
import Signatures.OOPS.CaliperAGMParameters

/-! Inspectable games, DLog reductions and their Caliper budget for OOPS. The mathematical
curve and degree stay explicit. Fixed local implementations, encodings and
caller allowances determine both complete reduction time, code and memory bounds.
The game stays independent of these implementation contracts. -/

open OracleComp OracleSpec PFunctor
open Signatures.Runtime

namespace OOPS

abbrev QueryAllowance := WeightedCaliper.QueryAllowance

/-- Caliper layouts, local implementations and caller allowances, fixed before
choosing the attacker. Complete reduction code and bounds are constructed from
these components; no completed-solver contract or hardness assumption is a field. -/
class AGMSecurityModel (curve : Model.PairingCurve) where
  Topic : Nat → Type
  [topicEquality : ∀ n, DecidableEq (Topic n)]
  parameters : ∀ n degree q, CaliperAGM.Parameters
    (curve.Scalar n) (curve.SignatureGroup n) (curve.KeyGroup n) (Topic n)
    degree q (curve.generator n) (curve.keyGenerator n)

attribute [instance_reducible, instance] AGMSecurityModel.topicEquality

variable (curve : Model.PairingCurve) [model : AGMSecurityModel curve]

/-- An arbitrary realized algebraic attacker within the model's own execution,
stored-code, memory and per-kind query limits. Local code is general Caliper
code; conventional-machine coverage remains a separate adequacy claim. The source retains the original scalar/topic game interface. -/
abbrev AlgebraicAdversary (securityParameter degree : Nat) (queries : QueryAllowance) :=
  WeightedCaliper.AlgebraicAdversary (model.parameters securityParameter degree queries)

/-- Maximum of the two complete runtime bounds proved for the constructed solvers. -/
def agmReductionTime (securityParameter degree : Nat) (queries : QueryAllowance) : Nat :=
  let resources := model.parameters securityParameter degree queries
  max resources.goodTime resources.badTime

/-- The actual lazy EUF-CMA experiment, with shared hash/signing/verification
bases. The winning predicate limits distinct signed scalar messages on the target topic to degree.
The secret is uniform over the whole field, including zero. -/
noncomputable def agmEufCmaGame (securityParameter degree : Nat) {queries : QueryAllowance}
    (adversary : AlgebraicAdversary curve securityParameter degree queries) : ProbComp Bool :=
  Game.agm curve securityParameter degree adversary.source

/-- The first `(1,1)`-DLog solver built from the attacker: it uses the challenge
`x • g₁` as the signing key, answers hashes with known multiples of `g₁`, and
solves for `x` from the forgery's algebraic explanation. Its Caliper
implementation is in `Proofs/Runtime/Caliper/WeightedGood.lean`. -/
noncomputable def agmGoodReduction {securityParameter degree : Nat} {queries : QueryAllowance}
    (adversary : AlgebraicAdversary curve securityParameter degree queries) :
    AlgebraicGroupModel.DLog11Adversary (curve.Scalar securityParameter)
      (curve.SignatureGroup securityParameter) (curve.KeyGroup securityParameter) :=
  Model.LazyAGM.WeightedReduction.goodReductionList (LazyAGM.terms degree) adversary.proofView

/-- The second solver, for forgeries the first cannot use: it samples the signing
key itself, embeds the challenge in every hash answer, and solves for `x` from
the forgery's explanation. Its Caliper implementation is in
`Proofs/Runtime/Caliper/WeightedBad.lean`. -/
noncomputable def agmBadReduction {securityParameter degree : Nat} {queries : QueryAllowance}
    (adversary : AlgebraicAdversary curve securityParameter degree queries) :
    AlgebraicGroupModel.DLog11Adversary (curve.Scalar securityParameter)
      (curve.SignatureGroup securityParameter) (curve.KeyGroup securityParameter) :=
  Model.LazyAGM.WeightedReduction.badReductionList (LazyAGM.terms degree) adversary.proofView

/-- A `(1,1)`-DLog solver given `(g₁, x • g₁, g₂, x • g₂)` that runs as Caliper
code on the fixed port and layouts within the derived code and total-memory
limits and the displayed time limit. Memory includes the stored program, input
and every intermediate state, and every sampled challenge must be representable. -/
def DLog11SolverWithin (securityParameter degree : Nat) (queries : QueryAllowance) (time : Nat)
    (solver : AlgebraicGroupModel.DLog11Adversary (curve.Scalar securityParameter)
      (curve.SignatureGroup securityParameter) (curve.KeyGroup securityParameter)) : Prop :=
  (model.parameters securityParameter degree queries).within time solver

end OOPS
