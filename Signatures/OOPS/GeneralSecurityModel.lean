import Signatures.OOPS.Game
import Signatures.OOPS.CaliperAGMParameters

/-! Inspectable games and Caliper DLog bounds for OOPS. The mathematical
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

/-- Supremum of `(1,1)`-DLog success for Caliper solvers receiving
`(g₁, x • g₁, g₂, x • g₂)`. The fixed code and total-memory bounds are derived
from local routines and caller limits; `time` is explicit. Every sampled challenge
is representable, as proved from the scalar sampler and local implementations.
Memory includes the stored program, input and every intermediate state.
See `Runtime/Caliper/WeightedSecurity.lean` for the two constructed certificates. -/
noncomputable def dlogSuccessBound (securityParameter degree : Nat) (queries : QueryAllowance)
    (time : Nat) : ENNReal :=
  let resources := model.parameters securityParameter degree queries
  ⨆ solver, ⨆ (_ : CaliperBackend.dlogWithin
      resources.layout.port resources.layout.goodSetup.challenge resources.scalar
      (curve.generator securityParameter) (curve.keyGenerator securityParameter)
      resources.solverCode resources.solverMemory time solver),
    𝒟[AlgebraicGroupModel.dlog11Exp (curve.generator securityParameter)
      (curve.keyGenerator securityParameter) solver] {true}

end OOPS
