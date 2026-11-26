import Signatures.BLS.Game
import Signatures.Model.PairingCurve
import Signatures.BLS.CaliperAGMParameters
import Signatures.BLS.CaliperCoCDHParameters

/-! Inspectable definitions for the two public BLS statements.

`AGMSecurityModel` and `AlgebraicAdversary` describe the AGM-to-DLog route.
`CoCDHSecurityModel` and `UnrestrictedAdversary` describe ordinary ROM security
to co-CDH. Both use actual Caliper word programs and the common query-allowance type. Their
component contracts, output types, reductions and hardness classes differ.

The games are in `Game.lean`. Each route names the solvers its proof builds from
the attacker, and a budget predicate (code, runtime and total memory) that they
are proved to satisfy. These are concrete resource models. Polynomial families and
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

/-- The DLog solver for forgeries whose algebraic explanation gives a nonzero
denominator: it runs the attacker on the challenge key, answers hashes and
signatures from a lazy table of known exponents, and solves for the key from
the explanation. Built in `Spec/LazyAGMList.lean`. -/
noncomputable def agmGoodReduction {securityParameter : Nat} {queries : QueryAllowance}
    (adversary : AlgebraicAdversary curve securityParameter queries) :
    AlgebraicGroupModel.DLog11Adversary (curve.Scalar securityParameter)
      (curve.SignatureGroup securityParameter) (curve.KeyGroup securityParameter) :=
  LazyAGM.Reduction.goodReductionList adversary.proofView

/-- The DLog solver for the zero-denominator case: it hides the key behind
independent affine masks and solves from the forgery's explanation.
Built in `Spec/LazyAGMList.lean`. -/
noncomputable def agmBadReduction {securityParameter : Nat} {queries : QueryAllowance}
    (adversary : AlgebraicAdversary curve securityParameter queries) :
    AlgebraicGroupModel.DLog11Adversary (curve.Scalar securityParameter)
      (curve.SignatureGroup securityParameter) (curve.KeyGroup securityParameter) :=
  LazyAGM.Reduction.badReductionList adversary.proofView

/-- A `(1,1)`-DLog solver given `(g₁, x • g₁, g₂, x • g₂)` that runs as Caliper
code on the fixed port and layouts within the derived stored-code and
total-memory limits and the displayed time limit. Memory covers code, initial
data and every visited state, and every sampled challenge must be represented.
See `Runtime/Caliper/DLog.lean` and the budgets in `CaliperAGMParameters.lean`. -/
def DLog11SolverWithin (securityParameter : Nat) (queries : QueryAllowance) (time : Nat)
    (solver : AlgebraicGroupModel.DLog11Adversary (curve.Scalar securityParameter)
      (curve.SignatureGroup securityParameter) (curve.KeyGroup securityParameter)) : Prop :=
  let resources := model.parameters securityParameter queries
  Signatures.Runtime.CaliperBackend.dlogWithin
    resources.layout.port resources.layout.setup.challenge resources.layout.scheme.cache.value
    (curve.generator securityParameter) (curve.keyGenerator securityParameter)
    resources.solverCode resources.solverMemory time solver

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

/-- Coron's co-CDH solver built from the attacker: it answers hashes with
`h + ρ • g₁` on a random subset of messages and `ρ • g₁` elsewhere, signs the
latter, and turns a forgery on the former into `x • h`. Built in
`CoCDH/Spec/Coron.lean`. -/
noncomputable def cocdhReduction {securityParameter : Nat} {queries : QueryAllowance}
    (adversary : UnrestrictedAdversary curve securityParameter queries) :
    CoCDH.CoCDHAdversary (curve.Scalar securityParameter)
      (curve.SignatureGroup securityParameter) (curve.KeyGroup securityParameter) :=
  CoCDH.coronReductionLazyPK queries.sign (ROM.cacheForgeryPK adversary.source)

/-- A co-CDH solver given `(g₁, g₂, x • g₁, x • g₂, h)` that runs as Caliper code
on the fixed port and layouts within the derived stored-code and total-memory
limits and the displayed time limit. Memory covers code, initial data and every
visited state, and every sampled challenge must fit the layout. See
`Runtime/Caliper/CoCDH.lean` and the budgets in `CaliperCoCDHParameters.lean`. -/
def CoCDHSolverWithin (securityParameter : Nat) (queries : QueryAllowance) (time : Nat)
    (solver : CoCDH.CoCDHAdversary (curve.Scalar securityParameter)
      (curve.SignatureGroup securityParameter) (curve.KeyGroup securityParameter)) : Prop :=
  let resources := model.parameters securityParameter queries
  Signatures.Runtime.CaliperBackend.coCDHWithin (F := curve.Scalar securityParameter)
    resources.service.port resources.challenge resources.service.point
    (curve.generator securityParameter) (curve.keyGenerator securityParameter)
    resources.solverCode resources.solverMemory time solver

end CoCDH

end BLS
