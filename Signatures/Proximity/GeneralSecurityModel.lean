import Signatures.Runtime.WeightedSecurityModel
import Signatures.Proximity.GeneralAGMParameters

/-! Inspectable games, execution contracts and DLog bounds for Proximity.
The dimension is explicit and fixed throughout each game. The adversary has general
backend code with algebraic outputs; its execution/code/query limits are its own.
Derived solver time and code include the degree/dimension-dependent work.
Proofs are in `Proofs/GeneralSecurity.lean`; declarations are in `Statement.lean`. -/

open OracleComp OracleSpec PFunctor
open Signatures.Runtime Signatures.Runtime.BackendProgram
open Signatures.Runtime.WeightedAGM

namespace Proximity

universe v w x

abbrev QueryAllowance := General.QueryAllowance

/-- Primitive and representation contracts, fixed before the attacker is chosen.
The mathematical curve and dimension remain explicit inputs. This model supplies
neither a completed-reduction budget nor a hardness assumption. -/
class AGMSecurityModel (curve : Model.PairingCurve) extends ExecutionModel.{v, w} curve where
  parameters : ∀ n dimension, QueryAllowance → GeneralAGM.Parameters.{v, w, x}
    (Q := quantitative) (F := curve.Scalar n) (G₁ := curve.SignatureGroup n)
    (G₂ := curve.KeyGroup n) (Gₜ := curve.TargetGroup n) (K := Label n) (M := Label n) dimension
  queries_eq : ∀ n d q, (parameters n d q).queries = q
  generator_eq : ∀ n d q, (parameters n d q).generator = curve.generator n
  keyGenerator_eq : ∀ n d q, (parameters n d q).keyGenerator = curve.keyGenerator n

variable (curve : Model.PairingCurve) [model : AGMSecurityModel.{v, w, x} curve]

/-- An arbitrary realized algebraic attacker within the model's own execution,
stored-code and per-kind query limits. Local code need not use our arithmetic
language. The source retains the original vector/slot game interface. -/
abbrev AlgebraicAdversary (securityParameter dimension : Nat) (queries : QueryAllowance) :=
  GeneralAGM.AlgebraicAdversary (model.parameters securityParameter dimension queries)

/-- Maximum of the two complete runtime bounds proved for the constructed solvers. -/
def agmReductionTime (securityParameter dimension : Nat) (queries : QueryAllowance) : Nat :=
  let resources := model.parameters securityParameter dimension queries
  max resources.goodTime resources.badTime

/-- The actual lazy EUF-CMA experiment, with shared hash/signing/verification
bases. Fresh collisions remain wins when the signature verifies; they are not rejected.
The secret is uniform over the whole field, including zero. -/
noncomputable def agmEufCmaGame (securityParameter dimension : Nat) {queries : QueryAllowance}
    (adversary : AlgebraicAdversary curve securityParameter dimension queries) : ProbComp Bool := by
  classical
  let F := curve.Scalar securityParameter
  let G₁ := curve.SignatureGroup securityParameter
  let Gₜ := curve.TargetGroup securityParameter
  let Slot := model.Label securityParameter
  let g₁ := curve.generator securityParameter
  let g₂ := curve.keyGenerator securityParameter
  exact (simulateQ Model.LazyAGM.lazyImpl (do
    let secret ← (liftM ($ᵗ F) : OracleComp (Model.LazyAGM.baseSpec (Option (Fin dimension) × Slot) G₁) F)
    let result ← Model.LazyAGM.interactiveRun (LazyAGM.terms) secret adversary.source g₁ (secret • g₂)
    match result.data, result.groups .signature with
    | some (forgery, signedMessages), [signature] =>
        let target ← Model.LazyAGM.evalTerms (LazyAGM.terms forgery.mstar)
        return decide (
          AlgebraicGroupModel.pairing (F := F) (Gₜ := Gₜ) signature g₂ =
            AlgebraicGroupModel.pairing (F := F) (Gₜ := Gₜ) target (secret • g₂) ∧
          forgery.mstar ∉ signedMessages)
    | _, _ => return false)).run' ∅

/-- Actual fresh-collision probability in the same source interaction. Every
signed vector, including repetitions and other slots, contributes with its
returned signing coefficient. Missing coefficients are zero. This event does
not require a valid signature and is not assumed negligible. -/
noncomputable def freshCollisionGame (securityParameter dimension : Nat) {queries : QueryAllowance}
    (adversary : AlgebraicAdversary curve securityParameter dimension queries) : ProbComp Bool := by
  classical
  let F := curve.Scalar securityParameter
  let G₁ := curve.SignatureGroup securityParameter
  let Slot := model.Label securityParameter
  let g₂ := curve.keyGenerator securityParameter
  exact (simulateQ Model.LazyAGM.lazyImpl (do
    let secret ← (liftM ($ᵗ F) : OracleComp (Model.LazyAGM.baseSpec (Option (Fin dimension) × Slot) G₁) F)
    let (out, transcript) ← Model.LazyAGM.run LazyAGM.terms secret adversary.source (secret • g₂)
    let signed := transcript.2.map Prod.fst
    return decide (out.mstar ∉ signed ∧
      out.mstar.1 = fun k => (signed.mapIdx fun n m =>
        Model.LazyAGM.tokenCoeff out.ξ n * m.1 k).sum))).run' ∅

/-- Supremum of `(1,1)`-DLog success over implementations in the same fixed
backend. A solver receives `(g₁, x • g₁, g₂, x • g₂)` and must recover uniform x.
The input and stored-code limits are derived in the shared weighted resource
interface; `time` is explicit. A hardness assumption is needed to make this small.
See `Runtime/BackendWeightedDLog.lean` and `Runtime/GeneralWeightedParameters.lean`. -/
noncomputable def dlogSuccessBound (securityParameter dimension : Nat) (queries : QueryAllowance)
    (time : Nat) : ENNReal :=
  let resources := model.parameters securityParameter dimension queries
  ⨆ solver, ⨆ (_ : NativeSolver.dlogWithin
      resources.rep resources.backend resources.descriptionSizes resources.factor resources.description
      resources.generator resources.keyGenerator resources.inputWidth resources.solverCode time solver),
    𝒟[AlgebraicGroupModel.dlog11Exp resources.generator resources.keyGenerator solver] {true}

end Proximity
