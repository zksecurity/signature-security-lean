import Signatures.Model.PairingCurve
import Signatures.BLS.GeneralAGMParameters
import Signatures.BLS.GeneralCoCDHParameters

/-! Inspectable definitions for the two public BLS statements.

`AGMSecurityModel` and `AlgebraicAdversary` describe the AGM-to-DLog route.
`CoCDHSecurityModel` and `UnrestrictedAdversary` describe ordinary ROM security
to co-CDH. Both use `ExecutionModel` and the common query-allowance type; their
component contracts, output types, native reductions and hardness classes differ.

Each game is written out below, and each success measure is an explicit supremum
over solvers in the fixed backend at the derived code/input/time bounds. This is
a concrete resource model. Polynomial families and a conventional-machine
instantiation need further hypotheses when making those stronger claims.
The public statements are in `Statement.lean`; their proofs and exact game
correspondences are in `Proofs/GeneralSecurity.lean`. -/

open OracleComp OracleSpec PFunctor
open Signatures.Runtime Signatures.Runtime.BackendProgram

namespace BLS

universe v w x

/-- Local computation and message types, shared by both BLS routes.
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

/-- AGM execution contracts and attacker limits, fixed before choosing the attacker.
`parameters` supplies encodings, a fixed executable backend, individual primitive
cost/size laws, and attacker work/state/output/code limits. The detailed fields
are in `GeneralAGMParameters.lean`. Algebraic output is required only on this route.
No completed-reduction budget or DLog hardness is assumed. -/
class AGMSecurityModel (curve : Model.PairingCurve) extends ExecutionModel.{v, w} curve where
  parameters : ∀ n, QueryAllowance → GeneralAGM.Parameters.{v, w, x}
    (Q := quantitative) (F := curve.Scalar n) (G₁ := curve.SignatureGroup n)
    (G₂ := curve.KeyGroup n) (Gₜ := curve.TargetGroup n) (M := Message n)
  queries_eq : ∀ n q, (parameters n q).queries = q
  generator_eq : ∀ n q, (parameters n q).generator = curve.generator n
  keyGenerator_eq : ∀ n q, (parameters n q).keyGenerator = curve.keyGenerator n

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

variable (curve : Model.PairingCurve) [model : AGMSecurityModel.{v, w, x} curve]

/-- Any algebraic attacker with an implementation in the fixed backend.
Its certificate supplies its own execution and stored-code bounds, the three query
allowances, and exact agreement with `source` at every public key. Algebraicity means
its group outputs come with representations in the group elements it received.
Its local computation is general backend code, not restricted to our arithmetic language. -/
abbrev AlgebraicAdversary (securityParameter : Nat) (queries : QueryAllowance) :=
  GeneralAGM.AlgebraicAdversary (model.parameters securityParameter queries)

/-- The actual EUF-CMA experiment. Hash and signing calls share one initially empty,
lazy random oracle: `hash(m) = H(m)` and `sign(m) = secret • H(m)`.
The certified AGM runner records signed messages and returns the candidate group point.
The secret is sampled uniformly from the whole scalar field, including zero. -/
noncomputable def agmEufCmaGame (securityParameter : Nat) {queries : QueryAllowance}
    (adversary : AlgebraicAdversary curve securityParameter queries) : ProbComp Bool := by
  classical
  let F := curve.Scalar securityParameter
  let G₁ := curve.SignatureGroup securityParameter
  let Gₜ := curve.TargetGroup securityParameter
  let M := model.Message securityParameter
  let g₁ := curve.generator securityParameter
  let g₂ := curve.keyGenerator securityParameter
  exact (simulateQ Model.LazyAGM.lazyImpl (do
    let secret ← (liftM ($ᵗ F) : OracleComp (Model.LazyAGM.baseSpec M G₁) F)
    let result ← Model.LazyAGM.interactiveRun LazyAGM.terms secret adversary.source g₁ (secret • g₂)
    match result.data, result.groups .signature with
    | some (forgery, signedMessages), [signature] =>
        let hash : G₁ ← liftM ((Model.LazyAGM.baseSpec M G₁).query (.inr forgery.mstar))
        return decide (
          AlgebraicGroupModel.pairing (F := F) (Gₜ := Gₜ) signature g₂ =
            AlgebraicGroupModel.pairing (F := F) (Gₜ := Gₜ) hash (secret • g₂) ∧
          forgery.mstar ∉ signedMessages)
    | _, _ => return false)).run' ∅

/-- Supremum of success probabilities for `(1,1)`-DLog: sample `x` uniformly,
give a solver `(g₁, x • g₁, g₂, x • g₂)`, and test whether it returns `x`.

`dlogWithin` requires one executable in the model's fixed backend, with exact solver
semantics at every input, stored code/data at most `resources.solverCode`, and time
at most `time` on every supported run within `resources.inputWidth`. All DLog
challenges must fit that input bound. See `Runtime/BackendLazyAGMDLog.lean` and
`Runtime/BackendWithin.lean` for those predicates. No optimal solver is assumed to exist.

`solverCode`, `goodTime`, and `badTime` are computed in `GeneralAGMParameters.lean`;
they charge setup, attacker execution, oracle simulation, extraction, and composition.
Their resource proofs are `GeneralAGM.reductions_within`. They are not user-supplied
finished-reduction budgets. This supremum still needs a hardness assumption to be small. -/
noncomputable def dlogSuccessBound (securityParameter : Nat) (queries : QueryAllowance)
    (time : Nat) : ENNReal :=
  let resources := model.parameters securityParameter queries
  ⨆ solver, ⨆ (_ : Signatures.Runtime.LazyAGM.NativeSolver.dlogWithin
      resources.rep resources.backend resources.descriptionSizes resources.factor resources.description
      resources.generator resources.keyGenerator resources.inputWidth resources.solverCode time solver),
    𝒟[AlgebraicGroupModel.dlog11Exp resources.generator resources.keyGenerator solver] {true}

end AGM

section CoCDH

variable (curve : Model.PairingCurve) [model : CoCDHSecurityModel.{v, w, x} curve]

/-- Any implemented attacker within the declared execution, code and query limits.
Its local computation is general backend code and its output is an arbitrary
message/signature pair; no algebraic representation is supplied or inspected. -/
abbrev UnrestrictedAdversary (securityParameter : Nat) (queries : QueryAllowance) :=
  GeneralCoCDH.Adversary (model.parameters securityParameter queries)

/-- The ordinary BLS EUF-CMA experiment. The real oracle samples a fresh scalar
only when a message is first encountered, hashes it to `scalar • generator`, and
signs it with the secret key. Hashing, signing and final verification share that
cache. `cacheForgeryPK` appends the verifier's hash lookup before the final test.
The secret is uniform over the whole scalar field, including zero. -/
noncomputable def cocdhEufCmaGame (securityParameter : Nat) {queries : QueryAllowance}
    (adversary : UnrestrictedAdversary curve securityParameter queries) : ProbComp Bool := by
  classical
  let F := curve.Scalar securityParameter
  let Gₜ := curve.TargetGroup securityParameter
  let g₁ := curve.generator securityParameter
  let g₂ := curve.keyGenerator securityParameter
  exact do
    let secret ← ($ᵗ F : ProbComp F)
    let ((message, signature), state) ←
      (simulateQ (CoCDH.Tight.realOracle (F := F) g₁ (secret • g₁))
        (CoCDH.Tight.cacheForgeryPK adversary.source (secret • g₂))).run ((fun _ => none), ∅)
    return decide (AlgebraicGroupModel.pairing (F := F) (Gₜ := Gₜ) signature g₂ =
      AlgebraicGroupModel.pairing (F := F) (Gₜ := Gₜ)
        (((state.1 message).getD 0) • g₁) (secret • g₂)) && decide (message ∉ state.2)

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
