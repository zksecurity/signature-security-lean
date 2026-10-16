import Signatures.OOPS.Game
import Signatures.Runtime.WeightedSecurityModel
import Signatures.OOPS.GeneralAGMParameters

/-! Inspectable games, execution contracts and DLog bounds for OOPS.
The degree is explicit and fixed throughout each game. The adversary has general
backend code with algebraic outputs; its execution/code/query limits are its own.
Derived solver time and code include the degree/dimension-dependent work.
Proofs are in `Proofs/GeneralSecurity.lean`; declarations are in `Statement.lean`. -/

open OracleComp OracleSpec PFunctor
open Signatures.Runtime Signatures.Runtime.BackendProgram
open Signatures.Runtime.WeightedAGM

namespace OOPS

universe v w x

abbrev QueryAllowance := General.QueryAllowance

/-- Primitive and representation contracts, fixed before the attacker is chosen.
The mathematical curve and degree remain explicit inputs. This model supplies
neither a completed-reduction budget nor a hardness assumption. -/
class AGMSecurityModel (curve : Model.PairingCurve) extends ExecutionModel.{v, w} curve where
  parameters : ∀ n degree, QueryAllowance → GeneralAGM.Parameters.{v, w, x}
    (Q := quantitative) (F := curve.Scalar n) (G₁ := curve.SignatureGroup n)
    (G₂ := curve.KeyGroup n) (Gₜ := curve.TargetGroup n) (K := Label n) (M := Label n) degree
  queries_eq : ∀ n d q, (parameters n d q).queries = q
  generator_eq : ∀ n d q, (parameters n d q).generator = curve.generator n
  keyGenerator_eq : ∀ n d q, (parameters n d q).keyGenerator = curve.keyGenerator n

variable (curve : Model.PairingCurve) [model : AGMSecurityModel.{v, w, x} curve]

/-- An arbitrary realized algebraic attacker within the model's own execution,
stored-code and per-kind query limits. Local code need not use our arithmetic
language. The source retains the original scalar/topic game interface. -/
abbrev AlgebraicAdversary (securityParameter degree : Nat) (queries : QueryAllowance) :=
  GeneralAGM.AlgebraicAdversary (model.parameters securityParameter degree queries)

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

/-- Supremum of `(1,1)`-DLog success over implementations in the same fixed
backend. A solver receives `(g₁, x • g₁, g₂, x • g₂)` and must recover uniform x.
The input and stored-code limits are derived in the shared weighted resource
interface; `time` is explicit. A hardness assumption is needed to make this small.
See `Runtime/BackendWeightedDLog.lean` and `Runtime/GeneralWeightedParameters.lean`. -/
noncomputable def dlogSuccessBound (securityParameter degree : Nat) (queries : QueryAllowance)
    (time : Nat) : ENNReal :=
  let resources := model.parameters securityParameter degree queries
  ⨆ solver, ⨆ (_ : NativeSolver.dlogWithin
      resources.rep resources.backend resources.descriptionSizes resources.factor resources.description
      resources.generator resources.keyGenerator resources.inputWidth resources.solverCode time solver),
    𝒟[AlgebraicGroupModel.dlog11Exp resources.generator resources.keyGenerator solver] {true}

end OOPS
