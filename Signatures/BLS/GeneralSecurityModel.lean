import Signatures.BLS.Game
import Signatures.Model.PairingCurve
import Signatures.BLS.CaliperAGMParameters
import Signatures.BLS.CaliperCoCDHParameters

/-! Inspectable definitions for the two public BLS statements.

`AGMSecurityModel` and `AlgebraicAdversary` describe the AGM-to-DLog route.
`CoCDHSecurityModel` and `UnrestrictedAdversary` describe ordinary ROM security
to co-CDH. Both use actual Caliper word programs and the common query-allowance type. Their
component contracts, output types, reductions and hardness classes differ.

The games are in `Game.lean`; each success measure below is an explicit supremum
over solvers in the fixed resource model. Both bounds include code, runtime
and total memory. These are concrete resource models. Polynomial families and
a conventional-machine instantiation need further hypotheses when making those stronger claims.
The public statements are in `Statement.lean`; their proofs and exact game
correspondences are in `Proofs/GeneralSecurity.lean`. -/

open OracleComp OracleSpec PFunctor
open Signatures.Runtime Signatures.Runtime.BackendProgram

namespace BLS

/-- Caliper implementations and attacker allowances, fixed before choosing the attacker.
`parameters` supplies bounded layouts, individual primitive implementations,
a sampler, and numeric limits for local attacker code. The detailed fields are
in `CaliperAGMParameters.lean`. Algebraic output is required only on this route.
Complete reduction code, time and memory bounds are proved from those components. -/
class AGMSecurityModel (curve : Model.PairingCurve) where
  Message : Nat → Type
  [messageEquality : ∀ n, DecidableEq (Message n)]
  parameters : ∀ n q, CaliperAGM.Parameters
    (curve.Scalar n) (curve.SignatureGroup n) (curve.KeyGroup n) (Message n)
    q (curve.generator n) (curve.keyGenerator n)

attribute [instance_reducible, instance] AGMSecurityModel.messageEquality

/-- Caliper implementations and ordinary attacker allowances for co-CDH.
The detailed fields in `CaliperCoCDHParameters.lean` require a plain message and
signature output, without algebraic coefficients. The complete Coron program
and its resource certificate are constructed from those components. -/
class CoCDHSecurityModel (curve : Model.PairingCurve) where
  Message : Nat → Type
  [messageEquality : ∀ n, DecidableEq (Message n)]
  parameters : ∀ n q, CaliperCoCDH.Parameters
    (curve.Scalar n) (curve.SignatureGroup n) (curve.KeyGroup n) (Message n)
    q (curve.generator n) (curve.keyGenerator n)

attribute [instance_reducible, instance] CoCDHSecurityModel.messageEquality

section AGM

variable (curve : Model.PairingCurve) [model : AGMSecurityModel curve]

/-- An algebraic attacker realized by local Caliper code within the fixed allowances.
Its certificate proves initialization and continuation bounds, the three query
allowances, and exact agreement with the coefficient view of the shared AGM
`source`. Producing that view is charged to its implementation. Local computation
is general Caliper code. This class does not assert coverage of every conventional
polynomial-time attacker; that requires a separate machine-adequacy theorem. -/
abbrev AlgebraicAdversary (securityParameter : Nat) (queries : QueryAllowance) :=
  CaliperAGM.AlgebraicAdversary (model.parameters securityParameter queries)

/-- A common time allowance for the two constructed DLog solvers: the maximum
of their proved complete runtimes. This is computed from the fixed primitive
contracts and attacker limits, not supplied as an efficiency assumption. -/
def agmReductionTime (securityParameter : Nat) (queries : QueryAllowance) : Nat :=
  let resources := model.parameters securityParameter queries
  max resources.goodTime resources.badTime

/-- The actual EUF-CMA experiment. Hash and signing calls share one initially empty,
lazy random oracle: `hash(m) = H(m)` and `sign(m) = secret • H(m)`.
The certified AGM runner records signed messages and returns the candidate group point.
The secret is sampled uniformly from the whole scalar field, including zero. -/
noncomputable def agmEufCmaGame (securityParameter : Nat) {queries : QueryAllowance}
    (adversary : AlgebraicAdversary curve securityParameter queries) : ProbComp Bool :=
  Game.agm curve securityParameter adversary.source

/-- Supremum of success probabilities for `(1,1)`-DLog: sample `x` uniformly,
give a solver `(g₁, x • g₁, g₂, x • g₂)`, and test whether it returns `x`.

`dlogWithin` requires actual Caliper code, exact solver semantics on every
represented input, stored code at most `resources.solverCode`, total memory at
most `resources.solverMemory`, and time at most `time`. The memory bound covers
code, initial data and every visited state. Every sampled DLog challenge must
be representable. See `Runtime/Caliper/DLog.lean` and `Runtime/Caliper/Within.lean`.
No optimal solver is assumed to exist.

The budgets are computed in `CaliperAGMParameters.lean`; their proofs are
`CaliperAGM.reductions_within`. They charge setup, local attacker execution,
lazy oracle simulation and extraction. A hardness assumption is needed to make
this supremum small. -/
noncomputable def dlogSuccessBound (securityParameter : Nat) (queries : QueryAllowance)
    (time : Nat) : ENNReal :=
  let resources := model.parameters securityParameter queries
  ⨆ solver, ⨆ (_ : Signatures.Runtime.CaliperBackend.dlogWithin
      resources.layout.port resources.layout.setup.challenge resources.layout.scheme.cache.value
      (curve.generator securityParameter) (curve.keyGenerator securityParameter)
      resources.solverCode resources.solverMemory time solver),
    𝒟[AlgebraicGroupModel.dlog11Exp (curve.generator securityParameter)
      (curve.keyGenerator securityParameter) solver] {true}

end AGM

section CoCDH

variable (curve : Model.PairingCurve) [model : CoCDHSecurityModel curve]

/-- Any implemented attacker within the declared execution, code and query limits.
Its local computation is Caliper code and its output is an arbitrary
message/signature pair; no algebraic representation is supplied or inspected.
Coverage of every conventional efficient attacker is a separate adequacy claim. -/
abbrev UnrestrictedAdversary (securityParameter : Nat) (queries : QueryAllowance) :=
  CaliperCoCDH.Adversary (model.parameters securityParameter queries)

/-- The constructed Coron solver's proved complete runtime, including attacker
execution, lazy oracle simulation, setup and extraction. The detailed formula
is `CaliperCoCDH.Parameters.solverTime`; no completed-solver budget is assumed. -/
def cocdhReductionTime (securityParameter : Nat) (queries : QueryAllowance) : Nat :=
  (model.parameters securityParameter queries).solverTime

/-- The ordinary BLS EUF-CMA experiment: the shared game at `Game.signature`, with
hashing, signing and final verification through one initially empty lazy random
oracle, for the attacker's source program. -/
noncomputable def cocdhEufCmaGame (securityParameter : Nat) {queries : QueryAllowance}
    (adversary : UnrestrictedAdversary curve securityParameter queries) : ProbComp Bool :=
  Game.eufCma curve securityParameter adversary.source

/-- Supremum of co-CDH success: sample a scalar `x` and group point `h`, give a
solver `(g₁, g₂, x • g₁, x • g₂, h)`, and test whether it returns `x • h`.

`coCDHWithin` requires actual Caliper code, exact solver semantics and fixed
code, time and total-memory bounds. Memory includes stored code, initial data
and every visited state. Every sampled challenge must fit the fixed layout.
See `Runtime/Caliper/CoCDH.lean` and `Within.lean` for the resource class and
`CaliperCoCDHParameters.lean` for the derived budgets. The reduction's membership
is proved in `CaliperCoCDH.reduction_within` from its full constructed program.
A numerical hardness assumption is needed to bound this supremum. -/
noncomputable def coCDHSuccessBound (securityParameter : Nat) (queries : QueryAllowance)
    (time : Nat) : ENNReal :=
  let resources := model.parameters securityParameter queries
  ⨆ solver, ⨆ (_ : Signatures.Runtime.CaliperBackend.coCDHWithin (F := curve.Scalar securityParameter)
      resources.service.port resources.challenge resources.service.point
      (curve.generator securityParameter) (curve.keyGenerator securityParameter)
      resources.solverCode resources.solverMemory time solver),
    𝒟[CoCDH.coCDHExp (F := curve.Scalar securityParameter)
      (curve.generator securityParameter) (curve.keyGenerator securityParameter) solver] {true}

end CoCDH

end BLS
