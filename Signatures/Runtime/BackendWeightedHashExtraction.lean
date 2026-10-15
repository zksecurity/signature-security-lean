import Signatures.Runtime.BackendWeightedExtractionAssembly
import Signatures.Runtime.BackendWeightedExtractionFrames
import Signatures.Runtime.BackendWeightedHashCoefficients
import Signatures.Runtime.BackendWeightedGoodEvaluate

/-! Complete native hash-transcript extraction call. The singleton generator,
chronological coefficients, private-cache scans and retained argument/cache frames
are all charged from actual primitive contracts, even for zero coefficients. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.WeightedAGM.Extract

open BackendProgram Evaluate

def hashEvaluationWidth (width tokenCap cacheCap : Nat) : Nat :=
  evaluationWidth (7 * width) tokenCap (cacheCap + tokenCap)

def hashEvaluationTime (overhead : Nat → Nat)
    (width tokenCap cacheCap natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime tickTime : Nat) : Nat :=
  let rows := tokenCap
  let capacity := cacheCap + rows
  let W := hashEvaluationWidth width tokenCap cacheCap
  let fee := overhead (32 * CacheCompiler.frameWidth W capacity)
  rows * (rows * (natEqTime + natSubTime + 257 * fee) +
    capacity * (topicTime + 2 * indexTime + natEqTime + 391 * fee) + 2 * natAddTime +
    1 * addTime + 1 * mulTime + 1 * scalarTime + 1 * zeroTime + 516 * fee + tickTime) +
    1 * zeroTime + tickTime + 128 * fee

def hashExtractionTime (overhead : Nat → Nat)
    (width tokenCap coeffCap cacheCap natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime tickTime
      oneTime : Nat) : Nat :=
  hashCoefficientTime overhead width tokenCap coeffCap oneTime mulTime natEqTime natSubTime natAddTime zeroTime +
    hashEvaluationTime overhead width tokenCap cacheCap natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime tickTime +
    64 * overhead (1024 * preparationFrameWidth width tokenCap coeffCap tokenCap cacheCap)

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


omit [SampleableType F] in
theorem hashCoefficients_length {indexTy : Ty CryptoAtom}
    (tr : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × G₁)) (coeff : List F) :
    ((Coefficients.signedTerms (hashTerms (indexTy := indexTy))).denote
      (arithmetic F G₁ G₂ K M cost) (tr, coeff, ())).length = tr.length := by
  rw [Coefficients.signedTerms_denote]
  change (Model.LazyAGM.WeightedReduction.signedTerms (fun i => [(i, (1 : F))]) coeff tr.reverse).length = _
  rw [hash_signedTerms]
  simp only [BLS.LazyAGM.Reduction.traceTerms, List.length_mapIdx, List.length_reverse]

include sizes in
omit [Q.HasCategory] QP QS [SampleableType F] in
theorem hashCoefficients_rows_size {indexTy : Ty CryptoAtom}
    (tr : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × G₁)) (coeff : List F) (width : Nat)
    (hh : header ≤ width) (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (ht : ∀ p ∈ tr, Q.size (rep.ty (AGM.tokenTy indexTy)) p ≤ width) :
    ∀ row ∈ (Coefficients.signedTerms (hashTerms (indexTy := indexTy))).denote
      (arithmetic F G₁ G₂ K M cost) (tr, coeff, ()), Q.size (rep.ty (Terms.termTy indexTy)) row ≤ 3 * width := by
  intro row hr
  rw [Coefficients.signedTerms_denote] at hr
  change row ∈ Model.LazyAGM.WeightedReduction.signedTerms (fun i => [(i, (1 : F))]) coeff tr.reverse at hr
  rw [hash_signedTerms] at hr
  obtain ⟨n, hn, rfl⟩ := List.mem_mapIdx.mp hr
  have htoken := ht _ (List.mem_reverse.mp (List.getElem_mem hn))
  have hkey := (sizes.fst_le (rep.ty indexTy) (rep.ty point₁) tr.reverse[n]).trans htoken
  have hs := hf (Model.LazyAGM.tokenCoeff coeff n)
  have hp := sizes.prod_le (rep.ty indexTy) (rep.ty scalar) (tr.reverse[n].1, Model.LazyAGM.tokenCoeff coeff n)
  exact hp.trans (by dsimp only at *; omega)

include sizes lists in
omit [Q.HasCategory] QP QS [SampleableType F] in
theorem hashCoefficients_size {indexTy : Ty CryptoAtom}
    (tr : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × G₁)) (coeff : List F) (width tokenCap : Nat)
    (hh : header ≤ width) (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (ht : ∀ p ∈ tr, Q.size (rep.ty (AGM.tokenTy indexTy)) p ≤ width) (hlen : tr.length ≤ tokenCap) :
    Q.size (rep.ty (.list (Terms.termTy indexTy)))
      ((Coefficients.signedTerms (hashTerms (indexTy := indexTy))).denote
        (arithmetic F G₁ G₂ K M cost) (tr, coeff, ())) ≤ (4 * tokenCap + 1) * width := by
  have hrows := hashCoefficients_rows_size rep cost sizes tr coeff width hh hf ht
  have hlength : ((Coefficients.signedTerms (hashTerms (indexTy := indexTy))).denote
      (arithmetic F G₁ G₂ K M cost) (tr, coeff, ())).length ≤ tokenCap := by
    rw [hashCoefficients_length cost]
    exact hlen
  have h := lists.size_le_cap (rep.ty (Terms.termTy indexTy)) _ (3 * width) tokenCap hrows hlength
  have hm := Nat.mul_le_mul_left tokenCap hh
  exact h.trans (by nlinarith)

include laws dataLaws primitiveBound sizes lists mono routing

attribute [local irreducible] Language.compile Expression.compile Expression.arguments

theorem hashExtraction_bound (sampling : MachineCompiler.SamplingImplementation Q iface rep) (index : Index)
    (tr : List (index.ty.Value (cryptoBase F G₁ G₂ K M) × G₁)) (coeff : List F)
    (default : index.ty.Value (cryptoBase F G₁ G₂ K M) × F)
    (cache : List (index.ty.Value (cryptoBase F G₁ G₂ K M) × F))
    (width tokenCap coeffCap cacheCap natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime tickTime
      oneTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hn : ∀ k ≤ tokenCap + index.bound + 1, Q.size rep.data.nat k ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (ht : ∀ p ∈ tr, Q.size (rep.ty (AGM.tokenTy index.ty)) p ≤ width)
    (hd : Q.size (rep.ty (Terms.termTy index.ty)) default ≤ 7 * width)
    (hnt : tr.length ≤ tokenCap) (hnc : coeff.length ≤ coeffCap)
    (hc : cache.length ≤ cacheCap) (hk : ∀ p ∈ cache, Q.size (rep.ty index.ty) p.1 ≤ 7 * width)
    (hne : ∀ j k, j ≤ tokenCap + index.bound → k ≤ tokenCap + index.bound →
      (primitiveBound .natEq).time (j, k) ≤ natEqTime)
    (hns : ∀ k ≤ tokenCap, (primitiveBound .natSub).time (k, 1) ≤ natSubTime)
    (hna : ∀ k ≤ tokenCap, (primitiveBound .natAdd).time (k, 1) ≤ natAddTime)
    (he : ∀ x y : K, Q.size (rep.ty key) x ≤ hashEvaluationWidth width tokenCap cacheCap →
      Q.size (rep.ty key) y ≤ hashEvaluationWidth width tokenCap cacheCap → (primitiveBound .keyEq).time (x, y) ≤ topicTime)
    (hi : ∀ j : Fin (index.bound + 1), (primitiveBound (.finVal index.bound)).time j ≤ indexTime)
    (hdraw : ∀ z ∈ support (sampling.scalar.run control queryCost ()), z.steps ≤ scalarTime)
    (hz : (primitiveBound .zero).time () ≤ zeroTime)
    (ha : ∀ x y : F, (primitiveBound .add).time (x, y) ≤ addTime)
    (hmul : ∀ x y : F, (primitiveBound .mul).time (x, y) ≤ mulTime)
    (htick : ∀ n ≤ tokenCap, ∀ encoded ≤ 7 * hashEvaluationWidth width tokenCap cacheCap,
      control.loop n encoded ≤ tickTime)
    (hone : (primitiveBound .one).time () ≤ oneTime)
    (out : Run (F × List (index.ty.Value (cryptoBase F G₁ G₂ K M) × F)))
    (hout : out ∈ support ((Language.compile rep data (arithmetic F G₁ G₂ K M cost) primitive
      (rep.ty (Reply.cacheTy index.ty scalar)) (readEffect rep (Read.goodRead rep data cost primitive sampling index))
      (evaluateCoefficients (hashTerms (indexTy := index.ty)) (.op .zero .unit) goodCombine)).run control queryCost ((tr, coeff, default, ()), cache))) :
    (Q.size (rep.ty scalar) out.value.1 ≤ hashEvaluationWidth width tokenCap cacheCap ∧
      Q.size (rep.ty (Reply.cacheTy index.ty scalar)) out.value.2 ≤ hashEvaluationWidth width tokenCap cacheCap) ∧
      out.steps ≤ hashExtractionTime overhead width tokenCap coeffCap cacheCap natEqTime natSubTime natAddTime
        topicTime indexTime scalarTime zeroTime addTime mulTime tickTime oneTime := by
  let rows := (Coefficients.signedTerms (hashTerms (indexTy := index.ty))).denote (arithmetic F G₁ G₂ K M cost) (tr, coeff, ())
  let W := preparationFrameWidth width tokenCap coeffCap tokenCap cacheCap
  have hw := preparationFrameWidth_ge width tokenCap coeffCap tokenCap cacheCap
  have h7 : width ≤ 7 * width := by omega
  have hprep := hashCoefficients_cost rep data cost primitive laws dataLaws primitiveBound sizes lists mono
    tr coeff width tokenCap coeffCap oneTime mulTime natEqTime natSubTime natAddTime zeroTime
    hh hu hb (fun n hn' => hn n (by omega)) hf ht hnt hnc hone hmul
    (fun n hn' => hne n 0 (by omega) (by omega)) hns hna hz
  have hrows := hashCoefficients_rows_size rep cost sizes tr coeff width hh hf ht
  have hrowCap : rows.length ≤ tokenCap := by
    dsimp only [rows]
    rw [hashCoefficients_length cost]
    exact hnt
  have hrowsSize : Q.size (rep.ty (.list (Terms.termTy index.ty))) rows ≤ W :=
    (hashCoefficients_size rep cost sizes lists tr coeff width tokenCap hh hf ht hnt).trans
      (Nat.mul_le_mul_right width (by omega))
  have hvalues : ∀ f : F, Q.size (rep.ty scalar) f ≤ 3 * width := by
    intro f
    exact (hf f).trans (by omega)
  have hcache := preparationCache_size rep sizes lists (indexTy := index.ty) (value := scalar) cache width tokenCap coeffCap
    tokenCap cacheCap hh hk hvalues hc
  apply evaluateCoefficients_bound rep data cost primitive laws dataLaws primitiveBound sizes mono control queryCost routing
    (Read.goodRead rep data cost primitive sampling index) (hashTerms (indexTy := index.ty)) (.op .zero .unit) goodCombine tr coeff default cache
    (fun p => Q.size (rep.ty scalar) p.1 ≤ hashEvaluationWidth width tokenCap cacheCap ∧
      Q.size (rep.ty (Reply.cacheTy index.ty scalar)) p.2 ≤ hashEvaluationWidth width tokenCap cacheCap)
    W (hashCoefficientTime overhead width tokenCap coeffCap oneTime mulTime natEqTime natSubTime natAddTime zeroTime)
    (hashEvaluationTime overhead width tokenCap cacheCap natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime tickTime)
    (hh.trans hw) (hu.trans hw)
    (preparationInput_size rep sizes lists (indexTy := index.ty) (messageTy := index.ty) tr coeff default width tokenCap coeffCap
      tokenCap cacheCap hh hu hf ht hd hnt hnc)
    hcache hrowsSize hprep ?_ out hout
  intro z hz'
  have h := Evaluate.backendGood_bound rep data cost primitive laws dataLaws primitiveBound sizes lists mono
    control queryCost routing sampling index rows default cache (7 * width) tokenCap cacheCap
    natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime tickTime
    (hh.trans h7) (hu.trans h7) (fun b => (hb b).trans h7) (fun n hn' => (hn n hn').trans h7)
    (fun f => (hf f).trans h7) (fun r hr => (hrows r hr).trans (by omega)) hd hrowCap hc hk hne hns hna he hi hdraw hz ha hmul htick z
    (by simpa only [Evaluate.backendGood, backendEvaluate] using hz')
  simpa only [hashEvaluationWidth, hashEvaluationTime, one_mul] using h

end Signatures.Runtime.WeightedAGM.Extract
