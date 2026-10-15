import Signatures.Runtime.BackendWeightedExtractionAssembly
import Signatures.Runtime.BackendWeightedExtractionFrames
import Signatures.Runtime.BackendWeightedGoodEvaluate
import Signatures.Runtime.BackendWeightedBadEvaluate

/-! Complete native signing-transcript calls for both extraction branches.
Chronological coefficient expansion and effectful evaluation are composed from
actual primitive contracts. Argument construction, retained context and the
entire cache are charged; no finished preparation/evaluation budget is assumed. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.WeightedAGM.Extract

open BackendProgram Evaluate

def goodCoefficientEvaluationWidth (index : Index) (width tokenCap cacheCap : Nat) : Nat :=
  evaluationWidth (7 * width) (tokenCap * (index.bound + 1)) (cacheCap + tokenCap * (index.bound + 1))

def goodCoefficientEvaluationTime (index : Index) (overhead : Nat → Nat)
    (width tokenCap cacheCap natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime tickTime : Nat) : Nat :=
  let rows := tokenCap * (index.bound + 1)
  let capacity := cacheCap + rows
  let W := goodCoefficientEvaluationWidth index width tokenCap cacheCap
  let fee := overhead (32 * CacheCompiler.frameWidth (W) capacity)
  rows * (rows * (natEqTime + natSubTime + 257 * fee) +
    capacity * (topicTime + 2 * indexTime + natEqTime + 391 * fee) + 2 * natAddTime +
    1 * addTime + 1 * mulTime + 1 * scalarTime + 1 * zeroTime + 516 * fee + tickTime) +
    1 * zeroTime + tickTime + 128 * fee

def goodSigningCoefficientsTime (index : Index) (overhead : Nat → Nat)
    (width tokenCap coeffCap cacheCap natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime tickTime
      genIndexTime finZeroTime oneTime : Nat) : Nat :=
  index.coefficientTime overhead width tokenCap coeffCap genIndexTime finZeroTime oneTime mulTime natEqTime natSubTime natAddTime zeroTime +
    goodCoefficientEvaluationTime index overhead width tokenCap cacheCap natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime tickTime +
    64 * overhead (1024 * preparationFrameWidth width tokenCap coeffCap (tokenCap * (index.bound + 1)) cacheCap)

def badCoefficientEvaluationWidth (index : Index) (width tokenCap cacheCap : Nat) : Nat :=
  evaluationWidth (3 * (7 * width)) (tokenCap * (index.bound + 1)) (cacheCap + tokenCap * (index.bound + 1))

def badCoefficientEvaluationTime (index : Index) (overhead : Nat → Nat)
    (width tokenCap cacheCap natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime tickTime : Nat) : Nat :=
  let rows := tokenCap * (index.bound + 1)
  let capacity := cacheCap + rows
  let W := badCoefficientEvaluationWidth index width tokenCap cacheCap
  let fee := overhead (32 * CacheCompiler.frameWidth (3 * W) capacity)
  rows * (rows * (natEqTime + natSubTime + 257 * fee) +
    capacity * (topicTime + 2 * indexTime + natEqTime + 391 * fee) + 2 * natAddTime +
    2 * addTime + 2 * mulTime + 2 * scalarTime + 2 * zeroTime + 600 * fee + tickTime) +
    2 * zeroTime + tickTime + 128 * fee

def badSigningCoefficientsTime (index : Index) (overhead : Nat → Nat)
    (width tokenCap coeffCap cacheCap natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime tickTime
      genIndexTime finZeroTime oneTime : Nat) : Nat :=
  index.coefficientTime overhead width tokenCap coeffCap genIndexTime finZeroTime oneTime mulTime natEqTime natSubTime natAddTime zeroTime +
    badCoefficientEvaluationTime index overhead width tokenCap cacheCap natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime tickTime +
    64 * overhead (1024 * preparationFrameWidth width tokenCap coeffCap (tokenCap * (index.bound + 1)) cacheCap)

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ K M : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq K] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  (mono : Monotone overhead) (control : ControlCosts)
  (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (routing : RoutingCostLaws control overhead)


include laws dataLaws primitiveBound sizes lists mono routing

attribute [local irreducible] Language.compile Expression.compile Expression.arguments

theorem goodSigningCoefficients_bound (sampling : MachineCompiler.SamplingImplementation Q iface rep) (index : Index)
    (tr : List (index.messageTy.Value (cryptoBase F G₁ G₂ K M) × G₁)) (coeff : List F)
    (default : index.ty.Value (cryptoBase F G₁ G₂ K M) × F)
    (cache : List (index.ty.Value (cryptoBase F G₁ G₂ K M) × F))
    (width tokenCap coeffCap cacheCap natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime tickTime
      genIndexTime finZeroTime oneTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hn : ∀ k ≤ tokenCap * (index.bound + 1) + index.bound + 1, Q.size rep.data.nat k ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (ht : ∀ p ∈ tr, Q.size (rep.ty (AGM.tokenTy index.messageTy)) p ≤ width)
    (hj : ∀ j : Fin (index.bound + 1), Q.size (rep.ty (boundedNat index.bound)) j ≤ width)
    (hd : Q.size (rep.ty (Terms.termTy index.ty)) default ≤ 7 * width)
    (hnt : tr.length ≤ tokenCap) (hnc : coeff.length ≤ coeffCap)
    (hc : cache.length ≤ cacheCap) (hk : ∀ p ∈ cache, Q.size (rep.ty index.ty) p.1 ≤ 7 * width)
    (hne : ∀ j k, j ≤ tokenCap * (index.bound + 1) + index.bound → k ≤ tokenCap * (index.bound + 1) + index.bound →
      (primitiveBound .natEq).time (j, k) ≤ natEqTime)
    (hns : ∀ k ≤ tokenCap * (index.bound + 1), (primitiveBound .natSub).time (k, 1) ≤ natSubTime)
    (hna : ∀ k ≤ tokenCap * (index.bound + 1), (primitiveBound .natAdd).time (k, 1) ≤ natAddTime)
    (he : ∀ x y : K, Q.size (rep.ty key) x ≤ goodCoefficientEvaluationWidth index width tokenCap cacheCap →
      Q.size (rep.ty key) y ≤ goodCoefficientEvaluationWidth index width tokenCap cacheCap → (primitiveBound .keyEq).time (x, y) ≤ topicTime)
    (hi : ∀ j : Fin (index.bound + 1), (primitiveBound (.finVal index.bound)).time j ≤ indexTime)
    (hdraw : ∀ z ∈ support (sampling.scalar.run control queryCost ()), z.steps ≤ scalarTime)
    (hz : (primitiveBound .zero).time () ≤ zeroTime)
    (ha : ∀ x y : F, (primitiveBound .add).time (x, y) ≤ addTime)
    (hmul : ∀ x y : F, (primitiveBound .mul).time (x, y) ≤ mulTime)
    (htick : ∀ n ≤ tokenCap * (index.bound + 1), ∀ encoded ≤ 7 * goodCoefficientEvaluationWidth index width tokenCap cacheCap,
      control.loop n encoded ≤ tickTime)
    (hgen : ∀ k ≤ index.bound + 1, (primitiveBound (.finOfNat index.bound)).time k ≤ genIndexTime)
    (hfin : (primitiveBound (.finZero index.bound)).time () ≤ finZeroTime)
    (hone : (primitiveBound .one).time () ≤ oneTime)
    (out : Run (F × List (index.ty.Value (cryptoBase F G₁ G₂ K M) × F)))
    (hout : out ∈ support ((Language.compile rep data (arithmetic F G₁ G₂ K M cost) primitive
      (rep.ty (Reply.cacheTy index.ty scalar)) (readEffect rep (Read.goodRead rep data cost primitive sampling index))
      (evaluateCoefficients index.terms (.op .zero .unit) goodCombine)).run control queryCost ((tr, coeff, default, ()), cache))) :
    (Q.size (rep.ty scalar) out.value.1 ≤ goodCoefficientEvaluationWidth index width tokenCap cacheCap ∧
      Q.size (rep.ty (Reply.cacheTy index.ty scalar)) out.value.2 ≤ goodCoefficientEvaluationWidth index width tokenCap cacheCap) ∧
      out.steps ≤ goodSigningCoefficientsTime index overhead width tokenCap coeffCap cacheCap natEqTime natSubTime natAddTime
        topicTime indexTime scalarTime zeroTime addTime mulTime tickTime genIndexTime finZeroTime oneTime := by
  let rows := (Coefficients.signedTerms index.terms).denote (arithmetic F G₁ G₂ K M cost) (tr, coeff, ())
  let W := preparationFrameWidth width tokenCap coeffCap (tokenCap * (index.bound + 1)) cacheCap
  have hw := preparationFrameWidth_ge width tokenCap coeffCap (tokenCap * (index.bound + 1)) cacheCap
  have h7 : width ≤ 7 * width := by omega
  have htcap : tokenCap ≤ tokenCap * (index.bound + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hprep := index.coefficients_cost rep data cost primitive laws dataLaws primitiveBound sizes lists mono
    tr coeff width tokenCap coeffCap genIndexTime finZeroTime oneTime mulTime natEqTime natSubTime natAddTime zeroTime
    hh hu hb (fun n hn' => hn n (by omega)) hf ht hj hnt hnc hgen hfin hone hmul
    (fun n hn' => hne n 0 (by omega) (by omega)) (fun n hn' => hns n (by omega))
    (fun n hn' => hna n (by omega)) hz
  have hrows := index.coefficients_rows_size rep cost sizes tr coeff width hh hf ht hj
  have hrowCap : rows.length ≤ tokenCap * (index.bound + 1) := by
    dsimp only [rows]
    rw [index.coefficients_length cost]
    exact Nat.mul_le_mul_right _ hnt
  have hrowsSize : Q.size (rep.ty (.list (Terms.termTy index.ty))) rows ≤ W :=
    (index.coefficients_size rep cost sizes lists tr coeff width tokenCap hh hf ht hj hnt).trans
      (Nat.mul_le_mul_right width (by omega))
  have hvalues : ∀ f : F, Q.size (rep.ty scalar) f ≤ 3 * width := by
    intro f
    exact (hf f).trans (by omega)
  have hcache := preparationCache_size rep sizes lists (indexTy := index.ty) (value := scalar) cache width tokenCap coeffCap
    (tokenCap * (index.bound + 1)) cacheCap hh hk hvalues hc
  apply evaluateCoefficients_bound rep data cost primitive laws dataLaws primitiveBound sizes mono control queryCost routing
    (Read.goodRead rep data cost primitive sampling index) index.terms (.op .zero .unit) goodCombine tr coeff default cache
    (fun p => Q.size (rep.ty scalar) p.1 ≤ goodCoefficientEvaluationWidth index width tokenCap cacheCap ∧
      Q.size (rep.ty (Reply.cacheTy index.ty scalar)) p.2 ≤ goodCoefficientEvaluationWidth index width tokenCap cacheCap)
    W (index.coefficientTime overhead width tokenCap coeffCap genIndexTime finZeroTime oneTime mulTime natEqTime natSubTime natAddTime zeroTime)
    (goodCoefficientEvaluationTime index overhead width tokenCap cacheCap natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime tickTime)
    (hh.trans hw) (hu.trans hw)
    (preparationInput_size rep sizes lists (indexTy := index.ty) (messageTy := index.messageTy) tr coeff default width tokenCap coeffCap
      (tokenCap * (index.bound + 1)) cacheCap hh hu hf ht hd hnt hnc)
    hcache hrowsSize hprep ?_ out hout
  intro z hz'
  have h := Evaluate.backendGood_bound rep data cost primitive laws dataLaws primitiveBound sizes lists mono
    control queryCost routing sampling index rows default cache (7 * width) (tokenCap * (index.bound + 1)) cacheCap
    natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime tickTime
    (hh.trans h7) (hu.trans h7) (fun b => (hb b).trans h7) (fun n hn' => (hn n hn').trans h7)
    (fun f => (hf f).trans h7) hrows hd hrowCap hc hk hne hns hna he hi hdraw hz ha hmul htick z
    (by simpa only [Evaluate.backendGood, backendEvaluate] using hz')
  simpa only [goodCoefficientEvaluationWidth, goodCoefficientEvaluationTime, one_mul] using h

theorem badSigningCoefficients_bound (sampling : MachineCompiler.SamplingImplementation Q iface rep) (index : Index)
    (tr : List (index.messageTy.Value (cryptoBase F G₁ G₂ K M) × G₁)) (coeff : List F)
    (default : index.ty.Value (cryptoBase F G₁ G₂ K M) × F)
    (cache : List (index.ty.Value (cryptoBase F G₁ G₂ K M) × (F × F)))
    (width tokenCap coeffCap cacheCap natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime tickTime
      genIndexTime finZeroTime oneTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hn : ∀ k ≤ tokenCap * (index.bound + 1) + index.bound + 1, Q.size rep.data.nat k ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (ht : ∀ p ∈ tr, Q.size (rep.ty (AGM.tokenTy index.messageTy)) p ≤ width)
    (hj : ∀ j : Fin (index.bound + 1), Q.size (rep.ty (boundedNat index.bound)) j ≤ width)
    (hd : Q.size (rep.ty (Terms.termTy index.ty)) default ≤ 7 * width)
    (hnt : tr.length ≤ tokenCap) (hnc : coeff.length ≤ coeffCap)
    (hc : cache.length ≤ cacheCap) (hk : ∀ p ∈ cache, Q.size (rep.ty index.ty) p.1 ≤ 7 * width)
    (hne : ∀ j k, j ≤ tokenCap * (index.bound + 1) + index.bound → k ≤ tokenCap * (index.bound + 1) + index.bound →
      (primitiveBound .natEq).time (j, k) ≤ natEqTime)
    (hns : ∀ k ≤ tokenCap * (index.bound + 1), (primitiveBound .natSub).time (k, 1) ≤ natSubTime)
    (hna : ∀ k ≤ tokenCap * (index.bound + 1), (primitiveBound .natAdd).time (k, 1) ≤ natAddTime)
    (he : ∀ x y : K, Q.size (rep.ty key) x ≤ 3 * badCoefficientEvaluationWidth index width tokenCap cacheCap →
      Q.size (rep.ty key) y ≤ 3 * badCoefficientEvaluationWidth index width tokenCap cacheCap → (primitiveBound .keyEq).time (x, y) ≤ topicTime)
    (hi : ∀ j : Fin (index.bound + 1), (primitiveBound (.finVal index.bound)).time j ≤ indexTime)
    (hdraw : ∀ z ∈ support (sampling.scalar.run control queryCost ()), z.steps ≤ scalarTime)
    (hz : (primitiveBound .zero).time () ≤ zeroTime)
    (ha : ∀ x y : F, (primitiveBound .add).time (x, y) ≤ addTime)
    (hmul : ∀ x y : F, (primitiveBound .mul).time (x, y) ≤ mulTime)
    (htick : ∀ n ≤ tokenCap * (index.bound + 1), ∀ encoded ≤ 7 * badCoefficientEvaluationWidth index width tokenCap cacheCap,
      control.loop n encoded ≤ tickTime)
    (hgen : ∀ k ≤ index.bound + 1, (primitiveBound (.finOfNat index.bound)).time k ≤ genIndexTime)
    (hfin : (primitiveBound (.finZero index.bound)).time () ≤ finZeroTime)
    (hone : (primitiveBound .one).time () ≤ oneTime)
    (out : Run ((F × F) × List (index.ty.Value (cryptoBase F G₁ G₂ K M) × (F × F))))
    (hout : out ∈ support ((Language.compile rep data (arithmetic F G₁ G₂ K M cost) primitive
      (rep.ty (Reply.cacheTy index.ty (.pair scalar scalar))) (readEffect rep (Read.badRead rep data cost primitive sampling index))
      (evaluateCoefficients index.terms (.pair (.op .zero .unit) (.op .zero .unit)) badCombine)).run control queryCost ((tr, coeff, default, ()), cache))) :
    (Q.size (rep.ty (.pair scalar scalar)) out.value.1 ≤ badCoefficientEvaluationWidth index width tokenCap cacheCap ∧
      Q.size (rep.ty (Reply.cacheTy index.ty (.pair scalar scalar))) out.value.2 ≤ badCoefficientEvaluationWidth index width tokenCap cacheCap) ∧
      out.steps ≤ badSigningCoefficientsTime index overhead width tokenCap coeffCap cacheCap natEqTime natSubTime natAddTime
        topicTime indexTime scalarTime zeroTime addTime mulTime tickTime genIndexTime finZeroTime oneTime := by
  let rows := (Coefficients.signedTerms index.terms).denote (arithmetic F G₁ G₂ K M cost) (tr, coeff, ())
  let W := preparationFrameWidth width tokenCap coeffCap (tokenCap * (index.bound + 1)) cacheCap
  have hw := preparationFrameWidth_ge width tokenCap coeffCap (tokenCap * (index.bound + 1)) cacheCap
  have h7 : width ≤ 7 * width := by omega
  have htcap : tokenCap ≤ tokenCap * (index.bound + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hprep := index.coefficients_cost rep data cost primitive laws dataLaws primitiveBound sizes lists mono
    tr coeff width tokenCap coeffCap genIndexTime finZeroTime oneTime mulTime natEqTime natSubTime natAddTime zeroTime
    hh hu hb (fun n hn' => hn n (by omega)) hf ht hj hnt hnc hgen hfin hone hmul
    (fun n hn' => hne n 0 (by omega) (by omega)) (fun n hn' => hns n (by omega))
    (fun n hn' => hna n (by omega)) hz
  have hrows := index.coefficients_rows_size rep cost sizes tr coeff width hh hf ht hj
  have hrowCap : rows.length ≤ tokenCap * (index.bound + 1) := by
    dsimp only [rows]
    rw [index.coefficients_length cost]
    exact Nat.mul_le_mul_right _ hnt
  have hrowsSize : Q.size (rep.ty (.list (Terms.termTy index.ty))) rows ≤ W :=
    (index.coefficients_size rep cost sizes lists tr coeff width tokenCap hh hf ht hj hnt).trans
      (Nat.mul_le_mul_right width (by omega))
  have hvalues : ∀ f : (F × F), Q.size (rep.ty (.pair scalar scalar)) f ≤ 3 * width := by
    intro f
    have h := sizes.prod_le (rep.ty scalar) (rep.ty scalar) f
    have h1 := hf f.1
    have h2 := hf f.2
    exact h.trans (by omega)
  have hcache := preparationCache_size rep sizes lists (indexTy := index.ty) (value := .pair scalar scalar) cache width tokenCap coeffCap
    (tokenCap * (index.bound + 1)) cacheCap hh hk hvalues hc
  apply evaluateCoefficients_bound rep data cost primitive laws dataLaws primitiveBound sizes mono control queryCost routing
    (Read.badRead rep data cost primitive sampling index) index.terms (.pair (.op .zero .unit) (.op .zero .unit)) badCombine tr coeff default cache
    (fun p => Q.size (rep.ty (.pair scalar scalar)) p.1 ≤ badCoefficientEvaluationWidth index width tokenCap cacheCap ∧
      Q.size (rep.ty (Reply.cacheTy index.ty (.pair scalar scalar))) p.2 ≤ badCoefficientEvaluationWidth index width tokenCap cacheCap)
    W (index.coefficientTime overhead width tokenCap coeffCap genIndexTime finZeroTime oneTime mulTime natEqTime natSubTime natAddTime zeroTime)
    (badCoefficientEvaluationTime index overhead width tokenCap cacheCap natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime tickTime)
    (hh.trans hw) (hu.trans hw)
    (preparationInput_size rep sizes lists (indexTy := index.ty) (messageTy := index.messageTy) tr coeff default width tokenCap coeffCap
      (tokenCap * (index.bound + 1)) cacheCap hh hu hf ht hd hnt hnc)
    hcache hrowsSize hprep ?_ out hout
  intro z hz'
  have h := Evaluate.backendBad_bound rep data cost primitive laws dataLaws primitiveBound sizes lists mono
    control queryCost routing sampling index rows default cache (7 * width) (tokenCap * (index.bound + 1)) cacheCap
    natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime tickTime
    (hh.trans h7) (hu.trans h7) (fun b => (hb b).trans h7) (fun n hn' => (hn n hn').trans h7)
    (fun f => (hf f).trans h7) hrows hd hrowCap hc hk hne hns hna he hi hdraw hz ha hmul htick z
    (by simpa only [Evaluate.backendBad, backendEvaluate] using hz')
  simpa only [badCoefficientEvaluationWidth, badCoefficientEvaluationTime, one_mul] using h

end Signatures.Runtime.WeightedAGM.Extract
