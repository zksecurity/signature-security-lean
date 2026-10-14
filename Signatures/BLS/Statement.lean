import Signatures.Model.PairingCurve
import Signatures.BLS.GeneralAGMStatement
import Signatures.BLS.ArithmeticStatement

/-! BLS security: the game, execution assumptions, DLog success measure, and proof
are given below. The headline inequality is

    Pr[fresh valid BLS forgery] ≤ DLogSuccess(T_good) + DLogSuccess(T_bad) + 1/|F|.

Both DLog terms range over the same fixed backend, at the reduction's derived time,
stored-code, and input bounds. A numerical security claim additionally bounds those
DLog success probabilities. This is a concrete theorem at each security parameter.
The older arithmetic-source endpoints remain in `ArithmeticStatement.lean`. -/

open OracleComp OracleSpec PFunctor
open Signatures.Runtime Signatures.Runtime.BackendProgram

namespace BLS

universe v w x

/-- Maximum private-randomness, hash, and signing calls: `random`, `hash`, `sign`. -/
abbrev QueryAllowance := GeneralAGM.QueryAllowance

/-- The execution assumptions and attacker resource class, fixed before choosing an attacker.

* `steps` / `quantitative`: permitted local computation, encoded sizes, and measured costs.
* `parameters n q`: implemented sampling, arithmetic, equality and data operations with their
  individual cost/size laws; attacker work/state/output limits (`execution`) and stored
  code/advice limit (`callerCodeLimit`); concrete encodings and the common executable backend.
* `Message n`: any message type with decidable equality; it need not be finite.
* The final equalities tie the configured curve and query limits to the theorem's inputs.

The detailed fields are in `GeneralAGMParameters.lean`. In particular, this class fixes
resource limits as well as a machine: the theorem covers every attacker meeting those limits.
It assumes neither small DLog success nor a runtime bound for a completed reduction.
The reduction budgets are derived from these component contracts. Polynomial bounds on
parameter families and a conventional-machine instantiation are additional obligations
if one wants an asymptotic or conventional-PPT claim. -/
class SecurityModel (curve : Model.PairingCurve) where
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
  parameters : ∀ n, QueryAllowance → GeneralAGM.Parameters.{v, w, x}
    (Q := quantitative) (F := curve.Scalar n) (G₁ := curve.SignatureGroup n)
    (G₂ := curve.KeyGroup n) (Gₜ := curve.TargetGroup n) (M := Message n)
  queries_eq : ∀ n q, (parameters n q).queries = q
  generator_eq : ∀ n q, (parameters n q).generator = curve.generator n
  keyGenerator_eq : ∀ n q, (parameters n q).keyGenerator = curve.keyGenerator n

attribute [instance_reducible, instance] SecurityModel.products SecurityModel.sums SecurityModel.options
  SecurityModel.category SecurityModel.quantitativeProducts SecurityModel.quantitativeSums
  SecurityModel.quantitativeOptions SecurityModel.distributive SecurityModel.optionCode
  SecurityModel.messageEquality

variable (curve : Model.PairingCurve) [model : SecurityModel.{v, w, x} curve]

/-- Any algebraic attacker with an implementation in the fixed backend.
Its certificate supplies its own execution and stored-code bounds, the three query
allowances, and exact agreement with `source` at every public key. Algebraicity means
its group outputs come with representations in the group elements it received.
Its local computation is general backend code, not restricted to our arithmetic language. -/
abbrev AlgebraicAdversary (securityParameter : Nat) (queries : QueryAllowance) :=
  GeneralAGM.AlgebraicAdversary (model.parameters securityParameter queries)

/-- Each allowance in the public statement bounds that kind of query in the
actual source adversary, at every verification key. -/
theorem AlgebraicAdversary.query_allowances (securityParameter : Nat) (queries : QueryAllowance)
    (adversary : AlgebraicAdversary curve securityParameter queries) :
    (∀ pk, IsQueryBoundP (adversary.source.main pk) (fun i => GeneralAGM.queryKind i = 0) queries.random) ∧
    (∀ pk, IsQueryBoundP (adversary.source.main pk) (fun i => GeneralAGM.queryKind i = 1) queries.hash) ∧
    (∀ pk, IsQueryBoundP (adversary.source.main pk) (fun i => GeneralAGM.queryKind i = 2) queries.sign) := by
  simpa only [SecurityModel.queries_eq] using
    And.intro adversary.randomQueries (And.intro adversary.hashQueries adversary.signingQueries)

/-- The actual EUF-CMA experiment. Hash and signing calls share one initially empty,
lazy random oracle: `hash(m) = H(m)` and `sign(m) = secret • H(m)`.
The certified AGM runner records signed messages and returns the candidate group point.
The secret is sampled uniformly from the whole scalar field, including zero. -/
noncomputable def eufCmaGame (securityParameter : Nat) {queries : QueryAllowance}
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

/-- Expanding the public game preserves the exact original game, not just its probability. -/
theorem eufCmaGame_eq (securityParameter : Nat) {queries : QueryAllowance}
    (adversary : AlgebraicAdversary curve securityParameter queries) :
    eufCmaGame curve securityParameter adversary =
      LazyAGM.game (Gₜ := curve.TargetGroup securityParameter)
        (curve.generator securityParameter) (curve.keyGenerator securityParameter) adversary.source := by
  classical
  simp [eufCmaGame, LazyAGM.game, Model.LazyAGM.game, Model.LazyAGM.experiment,
    LazyAGM.terms, Model.LazyAGM.evalTerms]
  apply bind_congr
  intro keyAndCache
  apply bind_congr
  intro resultAndCache
  congr 2
  split <;> split <;> simp_all
  grind only

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

/-- Every algebraic attacker within the declared resources and query allowances obeys
this EUF-CMA bound. `goodTime` and `badTime` are the complete derived reduction times.
The good branch extracts from a nonzero denominator. The bad branch uses independent
affine masks to handle the zero-denominator case; the proof's remaining loss is `1/|F|`. -/
theorem security
    (curve : Model.PairingCurve) [model : SecurityModel curve]
    (securityParameter : Nat)
    (queries : QueryAllowance)
    (adversary : AlgebraicAdversary curve securityParameter queries) :
    let resources := model.parameters securityParameter queries
    𝒟[eufCmaGame curve securityParameter adversary] {true} ≤
      dlogSuccessBound curve securityParameter queries resources.goodTime +
      dlogSuccessBound curve securityParameter queries resources.badTime +
      1 / (curve.order securityParameter : ENNReal) := by
  let resources := model.parameters securityParameter queries
  -- Probability: the two explicit lazy reductions account for every successful forgery,
  -- apart from the original inverse-field-size loss. This step has no efficiency premise.
  have probabilityBound := LazyAGM.Reduction.security_arbitrary_messages_list
    resources.generator resources.keyGenerator adversary.source resources.generates resources.pairingInjective
  -- Efficiency: construct both native executable witnesses and prove their full budgets.
  obtain ⟨goodFits, badFits⟩ := GeneralAGM.reductions_within resources adversary
  -- Each constructed solver is therefore a member of the supremum above.
  have goodBound : Model.dlog11Advantage resources.generator resources.keyGenerator
      (LazyAGM.Reduction.goodReductionList adversary.source) ≤
      dlogSuccessBound curve securityParameter queries resources.goodTime :=
    le_iSup_of_le _ (le_iSup_of_le goodFits le_rfl)
  have badBound : Model.dlog11Advantage resources.generator resources.keyGenerator
      (LazyAGM.Reduction.badReductionList adversary.source) ≤
      dlogSuccessBound curve securityParameter queries resources.badTime :=
    le_iSup_of_le _ (le_iSup_of_le badFits le_rfl)
  simpa only [resources, eufCmaGame_eq, SecurityModel.generator_eq, SecurityModel.keyGenerator_eq,
    Model.PairingCurve.order] using
    probabilityBound.trans (add_le_add (add_le_add goodBound badBound) le_rfl)

end BLS
