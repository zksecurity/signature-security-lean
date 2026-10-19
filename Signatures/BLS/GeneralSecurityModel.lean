import Signatures.BLS.Game
import Signatures.Model.PairingCurve
import Signatures.BLS.CaliperAGMParameters
import Signatures.BLS.GeneralCoCDHParameters

/-! Inspectable definitions for the two public BLS statements.

`AGMSecurityModel` and `AlgebraicAdversary` describe the AGM-to-DLog route.
`CoCDHSecurityModel` and `UnrestrictedAdversary` describe ordinary ROM security
to co-CDH. Both use the common query-allowance type. The AGM route uses actual
Caliper word programs; the co-CDH route still uses `ExecutionModel`. Their
component contracts, output types, reductions and hardness classes differ.

The games are in `Game.lean`; each success measure below is an explicit supremum
over solvers in the fixed resource model. The AGM bounds include code, runtime
and total memory. These are concrete resource models. Polynomial families and
a conventional-machine instantiation need further hypotheses when making those stronger claims.
The public statements are in `Statement.lean`; their proofs and exact game
correspondences are in `Proofs/GeneralSecurity.lean`. -/

open OracleComp OracleSpec PFunctor
open Signatures.Runtime Signatures.Runtime.BackendProgram

namespace BLS

universe v w x

/-- Abstract local computation and message types for the co-CDH route.
The message type only needs decidable equality; it need not be finite. The
quantitative backend measures encoded sizes and costs of local computation. -/
class ExecutionModel (curve : Model.PairingCurve) where
  steps : StepClass.{0, v}
  [products : steps.HasProd]
  [sums : steps.HasSum]
  [options : steps.HasOption]
  quantitative : QuantitativeStepClass.{0, v, w} steps
  [category : quantitative.HasCategory]
  [quantitativeProducts : quantitative.HasProd]
  [quantitativeSums : quantitative.HasSum]
  [quantitativeOptions : quantitative.HasOption]
  [distributive : quantitative.IsDistributive]
  [optionCode : OptionCode (Q := quantitative)]
  Message : Nat → Type
  [messageEquality : ∀ n, DecidableEq (Message n)]

attribute [instance_reducible, instance] ExecutionModel.products ExecutionModel.sums ExecutionModel.options
  ExecutionModel.category ExecutionModel.quantitativeProducts ExecutionModel.quantitativeSums
  ExecutionModel.quantitativeOptions ExecutionModel.distributive ExecutionModel.optionCode
  ExecutionModel.messageEquality

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

/-- Unrestricted execution contracts and attacker limits for the co-CDH route.
The detailed fields in `GeneralCoCDHParameters.lean` require a plain message and
signature output, without algebraic coefficients. The native Coron reduction's
complete resource certificate is derived from these component contracts. -/
class CoCDHSecurityModel (curve : Model.PairingCurve) extends ExecutionModel.{v, w} curve where
  parameters : ∀ n, QueryAllowance → GeneralCoCDH.Parameters.{v, w, x}
    (Q := quantitative) (F := curve.Scalar n) (G₁ := curve.SignatureGroup n)
    (G₂ := curve.KeyGroup n) (Gₜ := curve.TargetGroup n) (M := Message n)
  queries_eq : ∀ n q, (parameters n q).queries = q
  generator_eq : ∀ n q, (parameters n q).generator = curve.generator n
  keyGenerator_eq : ∀ n q, (parameters n q).keyGenerator = curve.keyGenerator n

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

variable (curve : Model.PairingCurve) [model : CoCDHSecurityModel.{v, w, x} curve]

/-- Any implemented attacker within the declared execution, code and query limits.
Its local computation is general backend code and its output is an arbitrary
message/signature pair; no algebraic representation is supplied or inspected. -/
abbrev UnrestrictedAdversary (securityParameter : Nat) (queries : QueryAllowance) :=
  GeneralCoCDH.Adversary (model.parameters securityParameter queries)

/-- The constructed Coron solver's proved complete runtime, including attacker
execution, lazy oracle simulation, setup and extraction. The detailed formula
is `GeneralCoCDH.Parameters.solverTime`; no completed-solver budget is assumed. -/
def cocdhReductionTime (securityParameter : Nat) (queries : QueryAllowance) : Nat :=
  (model.parameters securityParameter queries).solverTime

/-- The ordinary BLS EUF-CMA experiment. The real oracle samples a fresh scalar
only when a message is first encountered, hashes it to `scalar • generator`, and
signs it with the secret key. Hashing, signing and final verification share that
cache. `cacheForgeryPK` appends the verifier's hash lookup before the final test.
The secret is uniform over the whole scalar field, including zero. -/
noncomputable def cocdhEufCmaGame (securityParameter : Nat) {queries : QueryAllowance}
    (adversary : UnrestrictedAdversary curve securityParameter queries) : ProbComp Bool :=
  Game.rom curve securityParameter adversary.source

/-- Supremum of co-CDH success: sample a scalar `x` and group point `h`, give a
solver `(g₁, g₂, x • g₁, x • g₂, h)`, and test whether it returns `x • h`.

`coCDHWithin` requires an executable in this model's fixed backend, exact solver
semantics, and derived code/input/time bounds. Every sampled challenge must fit
`inputWidth`. See `Runtime/BackendCoronSolverWithin.lean` for the predicate and
`GeneralCoCDHParameters.lean` for the derived `solverCode` and `solverTime`.
A numerical hardness assumption is needed to bound this supremum. -/
noncomputable def coCDHSuccessBound (securityParameter : Nat) (queries : QueryAllowance)
    (time : Nat) : ENNReal :=
  let resources := model.parameters securityParameter queries
  ⨆ solver, ⨆ (_ : Signatures.Runtime.Coron.NativeSolver.coCDHWithin
      resources.rep resources.backend resources.descriptionSizes resources.factor resources.description
      resources.generator resources.keyGenerator resources.inputWidth resources.solverCode time solver),
    𝒟[CoCDH.coCDHExp resources.generator resources.keyGenerator solver] {true}

end CoCDH

end BLS
