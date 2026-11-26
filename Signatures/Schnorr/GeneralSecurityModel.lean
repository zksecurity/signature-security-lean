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

/-- The single-pass DLog solver built from the attacker: it runs the attacker,
answers its queries, and solves for the key from the forgery's algebraic
explanation. Its construction is in `Proofs/Runtime/SchnorrAGMExecution.lean`. -/
noncomputable def agmReduction {securityParameter : Nat} {queries : QueryAllowance}
    (adversary : AlgebraicAdversary curve securityParameter queries) :
    DiffieHellman.DLogAdversary (curve.Scalar securityParameter) (curve.Group securityParameter) :=
  Signatures.Runtime.SchnorrAGM.dlogReduction adversary.source

/-- A DLog solver given `(g, x • g)` that runs as Caliper code on the fixed port
and layouts within the derived code and total-memory limits and the displayed
time limit. Memory includes stored code, initial data and all visited buffers,
and every sampled challenge must be represented. -/
def DLogSolverWithin (securityParameter : Nat) (queries : QueryAllowance) (time : Nat)
    (solver : DiffieHellman.DLogAdversary (curve.Scalar securityParameter) (curve.Group securityParameter)) :
    Prop :=
  (model.parameters securityParameter queries).within time solver

end Schnorr
