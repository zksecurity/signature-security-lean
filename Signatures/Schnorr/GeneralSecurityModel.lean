import Signatures.Schnorr.Game
import Signatures.Model.CyclicCurve
import Proofs.Schnorr.CaliperAGMSource

/-! Inspectable game and Caliper resource model for the public Schnorr AGM
statement. Implemented primitives, layouts, sampler and caller allowances are
fixed before choosing the attacker. The game remains independent of this model.
The separate abstract backend lives in `GeneralExecutionModel.lean`. -/
namespace Schnorr
open OracleComp OracleSpec

/-- Fixed Caliper components, with no completed-reduction certificate.
The fields are in `CaliperAGMParameters.lean`; actual initialization, caller
control, lazy service and extraction are constructed and proved separately. -/
class AGMSecurityModel (curve : Model.CyclicCurve) where
  Message : Nat → Type
  [messageEquality : ∀ n, DecidableEq (Message n)]
  parameters : ∀ n q, CaliperAGM.Parameters (curve.Scalar n) (curve.Group n) (Message n) q (curve.generator n)

attribute [instance_reducible, instance] AGMSecurityModel.messageEquality

variable (curve : Model.CyclicCurve) [model : AGMSecurityModel curve]

/-- An algebraic source attacker with actual local Caliper code and its own
query/resource bounds and source correspondence. Internal code is general
Caliper code; requests and output carry the shared AGM's algebraic explanations.
`CaliperAGM.AlgebraicAdversary.ofLocalCaller` derives the source and its
correspondence from local query, algebraicity and resource contracts.
Coverage of conventional machines is a separate adequacy theorem. -/
abbrev AlgebraicAdversary (securityParameter : Nat) (queries : QueryAllowance) :=
  CaliperAGM.AlgebraicAdversary (model.parameters securityParameter queries)

/-- Derived complete runtime, including initialization, local caller execution,
lazy queries, extraction and cutoff. No finished-solver time is assumed. -/
def agmReductionTime (securityParameter : Nat) (queries : QueryAllowance) : Nat :=
  (model.parameters securityParameter queries).solverTime

/-- Full-field-nonce Schnorr EUF-CMA. Key generation, hashing, signing,
verification and freshness are displayed independently in `Game.lean`. -/
noncomputable def agmEufCmaGame (securityParameter : Nat) {queries : QueryAllowance}
    (adversary : AlgebraicAdversary curve securityParameter queries) : ProbComp Bool :=
  Game.agm curve securityParameter adversary.source

/-- Supremum of success for ordinary DLog: sample uniform x, supply `(g,x • g)`
and check the returned scalar. Solvers use the fixed Caliper port and layouts,
with the derived code and total-memory limits and the displayed runtime limit.
Memory includes stored code, initial data and all visited buffers. Every
sampled challenge must be represented. No optimal solver need exist.

The budgets are in `CaliperAGM.Parameters`; `CaliperAGM.reduction_within`
constructs the actual reduction witness. A hardness assumption makes this
quantity small. Polynomial families are handled in separate statements. -/
noncomputable def dlogSuccessBound (securityParameter : Nat) (queries : QueryAllowance)
    (time : Nat) : ENNReal :=
  let resources := model.parameters securityParameter queries
  ⨆ solver, ⨆ (_ : Signatures.Runtime.CaliperBackend.cyclicDLogWithin
      resources.layout.service.random.port resources.layout.service.scheme.config resources.layout.service.scheme.scalar
      (curve.generator securityParameter) resources.solverCode resources.solverMemory time solver),
    𝒟[DiffieHellman.dlogExperiment (curve.generator securityParameter) solver] {true}

end Schnorr
