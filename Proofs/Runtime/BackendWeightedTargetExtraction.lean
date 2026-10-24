import Proofs.Runtime.BackendWeightedExtractionAssembly
import Proofs.Runtime.BackendWeightedExtractionFrames
import Proofs.Runtime.BackendWeightedSignValueBudget

/-! Complete native final-target calls for weighted extraction. Term generation
runs in its own input frame; all generated rows are evaluated, including rows of
weight zero. Runtime bounds include the retained default and private cache. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.WeightedAGM.Extract

open BackendProgram Evaluate

def goodTargetTime (index : Index) (overhead : Nat → Nat)
    (width cacheCap natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime tickTime
      genIndexTime finZeroTime oneTime : Nat) : Nat :=
  index.termsTime overhead width genIndexTime mulTime finZeroTime oneTime +
    Reply.goodSignEvaluationTime index overhead width cacheCap natEqTime natSubTime natAddTime topicTime indexTime
      scalarTime zeroTime addTime mulTime tickTime +
    64 * overhead (1024 * preparationFrameWidth width 0 0 (index.bound + 1) cacheCap)

def badTargetTime (index : Index) (overhead : Nat → Nat)
    (width cacheCap natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime tickTime
      genIndexTime finZeroTime oneTime : Nat) : Nat :=
  index.termsTime overhead width genIndexTime mulTime finZeroTime oneTime +
    Reply.badSignEvaluationTime index overhead width cacheCap natEqTime natSubTime natAddTime topicTime indexTime
      scalarTime zeroTime addTime mulTime tickTime +
    64 * overhead (1024 * preparationFrameWidth width 0 0 (index.bound + 1) cacheCap)

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

theorem goodTarget_bound (sampling : MachineCompiler.SamplingImplementation Q iface rep) (index : Index)
    (m : index.messageTy.Value (cryptoBase F G₁ G₂ K M))
    (default : index.ty.Value (cryptoBase F G₁ G₂ K M) × F)
    (cache : List (index.ty.Value (cryptoBase F G₁ G₂ K M) × F))
    (width cacheCap natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime tickTime
      genIndexTime finZeroTime oneTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hn : ∀ k ≤ (index.bound + 1) + index.bound + 1, Q.size rep.data.nat k ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hm : Q.size (rep.ty index.messageTy) m ≤ width)
    (hj : ∀ j : Fin (index.bound + 1), Q.size (rep.ty (boundedNat index.bound)) j ≤ width)
    (hd : Q.size (rep.ty (Terms.termTy index.ty)) default ≤ 5 * width)
    (hc : cache.length ≤ cacheCap) (hk : ∀ p ∈ cache, Q.size (rep.ty index.ty) p.1 ≤ 5 * width)
    (hne : ∀ j k, j ≤ (index.bound + 1) + index.bound → k ≤ (index.bound + 1) + index.bound →
      (primitiveBound .natEq).time (j, k) ≤ natEqTime)
    (hns : ∀ k ≤ index.bound + 1, (primitiveBound .natSub).time (k, 1) ≤ natSubTime)
    (hna : ∀ k ≤ index.bound + 1, (primitiveBound .natAdd).time (k, 1) ≤ natAddTime)
    (he : ∀ x y : K, Q.size (rep.ty key) x ≤ Reply.goodSignEvaluationWidth index width cacheCap →
      Q.size (rep.ty key) y ≤ Reply.goodSignEvaluationWidth index width cacheCap → (primitiveBound .keyEq).time (x, y) ≤ topicTime)
    (hi : ∀ j : Fin (index.bound + 1), (primitiveBound (.finVal index.bound)).time j ≤ indexTime)
    (hdraw : ∀ z ∈ support (sampling.scalar.run control queryCost ()), z.steps ≤ scalarTime)
    (hz : (primitiveBound .zero).time () ≤ zeroTime)
    (ha : ∀ x y : F, (primitiveBound .add).time (x, y) ≤ addTime)
    (hmul : ∀ x y : F, (primitiveBound .mul).time (x, y) ≤ mulTime)
    (htick : ∀ n ≤ index.bound + 1, ∀ encoded ≤ 7 * Reply.goodSignEvaluationWidth index width cacheCap,
      control.loop n encoded ≤ tickTime)
    (hgen : ∀ k ≤ index.bound + 1, (primitiveBound (.finOfNat index.bound)).time k ≤ genIndexTime)
    (hfin : (primitiveBound (.finZero index.bound)).time () ≤ finZeroTime)
    (hone : (primitiveBound .one).time () ≤ oneTime)
    (out : Run (F × List (index.ty.Value (cryptoBase F G₁ G₂ K M) × F)))
    (hout : out ∈ support ((Language.compile rep data (arithmetic F G₁ G₂ K M cost) primitive
      (rep.ty (Reply.cacheTy index.ty scalar)) (readEffect rep (Read.goodRead rep data cost primitive sampling index))
      (evaluateTarget index.terms (.op .zero .unit) goodCombine)).run control queryCost ((m, default, ()), cache))) :
    (Q.size (rep.ty scalar) out.value.1 ≤ Reply.goodSignEvaluationWidth index width cacheCap ∧
      Q.size (rep.ty (Reply.cacheTy index.ty scalar)) out.value.2 ≤ Reply.goodSignEvaluationWidth index width cacheCap) ∧
      out.steps ≤ goodTargetTime index overhead width cacheCap natEqTime natSubTime natAddTime topicTime indexTime
        scalarTime zeroTime addTime mulTime tickTime genIndexTime finZeroTime oneTime := by
  let W := preparationFrameWidth width 0 0 (index.bound + 1) cacheCap
  have hw := preparationFrameWidth_ge width 0 0 (index.bound + 1) cacheCap
  have h5 : width ≤ 5 * width := by omega
  have hprep := index.terms_cost rep data cost primitive laws dataLaws primitiveBound sizes lists mono
    m width genIndexTime mulTime finZeroTime oneTime hh hu hm hf hj (fun n hn' => hn n (by omega))
    hgen hmul hfin hone
  have hrows := index.terms_rows_size rep cost sizes m width hh hm hf hj
  have hrowCap := index.terms_length (G₁ := G₁) (G₂ := G₂) (M := M) cost m
  have hrowsSize : Q.size (rep.ty (.list (Terms.termTy index.ty))) (index.sourceTerms cost m) ≤ W :=
    (index.terms_size rep cost sizes lists m width hh hm hf hj).trans
      (Nat.mul_le_mul_right width (by omega))
  have hinput : Q.size (rep.env [index.messageTy, Terms.termTy index.ty]) (m, default, ()) ≤ W := by
    have hp := @sizes.prod_le
    dsimp only [LanguageRepresentation.ty, LanguageRepresentation.env, W, preparationFrameWidth] at *
    grind only
  have hvalues : ∀ f : F, Q.size (rep.ty scalar) f ≤ 3 * width := by
    intro f
    exact (hf f).trans (by omega)
  have hcache := preparationCache_size rep sizes lists (indexTy := index.ty) (value := scalar) cache
    width 0 0 (index.bound + 1) cacheCap hh (fun p hp => (hk p hp).trans (by omega)) hvalues hc
  apply evaluateTarget_bound rep data cost primitive laws dataLaws primitiveBound sizes mono control queryCost routing
    (Read.goodRead rep data cost primitive sampling index) index.terms (.op .zero .unit) goodCombine m default cache
    (fun p => Q.size (rep.ty scalar) p.1 ≤ Reply.goodSignEvaluationWidth index width cacheCap ∧
      Q.size (rep.ty (Reply.cacheTy index.ty scalar)) p.2 ≤ Reply.goodSignEvaluationWidth index width cacheCap)
    W (index.termsTime overhead width genIndexTime mulTime finZeroTime oneTime)
    (Reply.goodSignEvaluationTime index overhead width cacheCap natEqTime natSubTime natAddTime topicTime indexTime
      scalarTime zeroTime addTime mulTime tickTime)
    (hh.trans hw) (hu.trans hw) hinput hcache hrowsSize hprep ?_ out hout
  intro z hz'
  have h := Evaluate.backendGood_bound rep data cost primitive laws dataLaws primitiveBound sizes lists mono
    control queryCost routing sampling index (index.sourceTerms cost m) default cache (5 * width) (index.bound + 1) cacheCap
    natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime tickTime
    (hh.trans h5) (hu.trans h5) (fun b => (hb b).trans h5) (fun n hn' => (hn n hn').trans h5)
    (fun f => (hf f).trans h5) hrows hd (le_of_eq hrowCap) hc hk hne hns hna he hi hdraw hz ha hmul htick z
    (by simpa only [Evaluate.backendGood, backendEvaluate, Index.sourceTerms] using hz')
  simpa only [Reply.goodSignEvaluationWidth, Reply.goodSignEvaluationTime, one_mul] using h

theorem badTarget_bound (sampling : MachineCompiler.SamplingImplementation Q iface rep) (index : Index)
    (m : index.messageTy.Value (cryptoBase F G₁ G₂ K M))
    (default : index.ty.Value (cryptoBase F G₁ G₂ K M) × F)
    (cache : List (index.ty.Value (cryptoBase F G₁ G₂ K M) × (F × F)))
    (width cacheCap natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime tickTime
      genIndexTime finZeroTime oneTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hn : ∀ k ≤ (index.bound + 1) + index.bound + 1, Q.size rep.data.nat k ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hm : Q.size (rep.ty index.messageTy) m ≤ width)
    (hj : ∀ j : Fin (index.bound + 1), Q.size (rep.ty (boundedNat index.bound)) j ≤ width)
    (hd : Q.size (rep.ty (Terms.termTy index.ty)) default ≤ 5 * width)
    (hc : cache.length ≤ cacheCap) (hk : ∀ p ∈ cache, Q.size (rep.ty index.ty) p.1 ≤ 5 * width)
    (hne : ∀ j k, j ≤ (index.bound + 1) + index.bound → k ≤ (index.bound + 1) + index.bound →
      (primitiveBound .natEq).time (j, k) ≤ natEqTime)
    (hns : ∀ k ≤ index.bound + 1, (primitiveBound .natSub).time (k, 1) ≤ natSubTime)
    (hna : ∀ k ≤ index.bound + 1, (primitiveBound .natAdd).time (k, 1) ≤ natAddTime)
    (he : ∀ x y : K, Q.size (rep.ty key) x ≤ 3 * Reply.badSignEvaluationWidth index width cacheCap →
      Q.size (rep.ty key) y ≤ 3 * Reply.badSignEvaluationWidth index width cacheCap → (primitiveBound .keyEq).time (x, y) ≤ topicTime)
    (hi : ∀ j : Fin (index.bound + 1), (primitiveBound (.finVal index.bound)).time j ≤ indexTime)
    (hdraw : ∀ z ∈ support (sampling.scalar.run control queryCost ()), z.steps ≤ scalarTime)
    (hz : (primitiveBound .zero).time () ≤ zeroTime)
    (ha : ∀ x y : F, (primitiveBound .add).time (x, y) ≤ addTime)
    (hmul : ∀ x y : F, (primitiveBound .mul).time (x, y) ≤ mulTime)
    (htick : ∀ n ≤ index.bound + 1, ∀ encoded ≤ 7 * Reply.badSignEvaluationWidth index width cacheCap,
      control.loop n encoded ≤ tickTime)
    (hgen : ∀ k ≤ index.bound + 1, (primitiveBound (.finOfNat index.bound)).time k ≤ genIndexTime)
    (hfin : (primitiveBound (.finZero index.bound)).time () ≤ finZeroTime)
    (hone : (primitiveBound .one).time () ≤ oneTime)
    (out : Run ((F × F) × List (index.ty.Value (cryptoBase F G₁ G₂ K M) × (F × F))))
    (hout : out ∈ support ((Language.compile rep data (arithmetic F G₁ G₂ K M cost) primitive
      (rep.ty (Reply.cacheTy index.ty (.pair scalar scalar))) (readEffect rep (Read.badRead rep data cost primitive sampling index))
      (evaluateTarget index.terms (.pair (.op .zero .unit) (.op .zero .unit)) badCombine)).run control queryCost ((m, default, ()), cache))) :
    (Q.size (rep.ty (.pair scalar scalar)) out.value.1 ≤ Reply.badSignEvaluationWidth index width cacheCap ∧
      Q.size (rep.ty (Reply.cacheTy index.ty (.pair scalar scalar))) out.value.2 ≤ Reply.badSignEvaluationWidth index width cacheCap) ∧
      out.steps ≤ badTargetTime index overhead width cacheCap natEqTime natSubTime natAddTime topicTime indexTime
        scalarTime zeroTime addTime mulTime tickTime genIndexTime finZeroTime oneTime := by
  let W := preparationFrameWidth width 0 0 (index.bound + 1) cacheCap
  have hw := preparationFrameWidth_ge width 0 0 (index.bound + 1) cacheCap
  have h5 : width ≤ 5 * width := by omega
  have hprep := index.terms_cost rep data cost primitive laws dataLaws primitiveBound sizes lists mono
    m width genIndexTime mulTime finZeroTime oneTime hh hu hm hf hj (fun n hn' => hn n (by omega))
    hgen hmul hfin hone
  have hrows := index.terms_rows_size rep cost sizes m width hh hm hf hj
  have hrowCap := index.terms_length (G₁ := G₁) (G₂ := G₂) (M := M) cost m
  have hrowsSize : Q.size (rep.ty (.list (Terms.termTy index.ty))) (index.sourceTerms cost m) ≤ W :=
    (index.terms_size rep cost sizes lists m width hh hm hf hj).trans
      (Nat.mul_le_mul_right width (by omega))
  have hinput : Q.size (rep.env [index.messageTy, Terms.termTy index.ty]) (m, default, ()) ≤ W := by
    have hp := @sizes.prod_le
    dsimp only [LanguageRepresentation.ty, LanguageRepresentation.env, W, preparationFrameWidth] at *
    grind only
  have hvalues : ∀ f : (F × F), Q.size (rep.ty (.pair scalar scalar)) f ≤ 3 * width := by
    intro f
    have h := sizes.prod_le (rep.ty scalar) (rep.ty scalar) f
    have h1 := hf f.1
    have h2 := hf f.2
    exact h.trans (by omega)
  have hcache := preparationCache_size rep sizes lists (indexTy := index.ty) (value := (.pair scalar scalar)) cache
    width 0 0 (index.bound + 1) cacheCap hh (fun p hp => (hk p hp).trans (by omega)) hvalues hc
  apply evaluateTarget_bound rep data cost primitive laws dataLaws primitiveBound sizes mono control queryCost routing
    (Read.badRead rep data cost primitive sampling index) index.terms (.pair (.op .zero .unit) (.op .zero .unit)) badCombine m default cache
    (fun p => Q.size (rep.ty (.pair scalar scalar)) p.1 ≤ Reply.badSignEvaluationWidth index width cacheCap ∧
      Q.size (rep.ty (Reply.cacheTy index.ty (.pair scalar scalar))) p.2 ≤ Reply.badSignEvaluationWidth index width cacheCap)
    W (index.termsTime overhead width genIndexTime mulTime finZeroTime oneTime)
    (Reply.badSignEvaluationTime index overhead width cacheCap natEqTime natSubTime natAddTime topicTime indexTime
      scalarTime zeroTime addTime mulTime tickTime)
    (hh.trans hw) (hu.trans hw) hinput hcache hrowsSize hprep ?_ out hout
  intro z hz'
  have h := Evaluate.backendBad_bound rep data cost primitive laws dataLaws primitiveBound sizes lists mono
    control queryCost routing sampling index (index.sourceTerms cost m) default cache (5 * width) (index.bound + 1) cacheCap
    natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime tickTime
    (hh.trans h5) (hu.trans h5) (fun b => (hb b).trans h5) (fun n hn' => (hn n hn').trans h5)
    (fun f => (hf f).trans h5) hrows hd (le_of_eq hrowCap) hc hk hne hns hna he hi hdraw hz ha hmul htick z
    (by simpa only [Evaluate.backendBad, backendEvaluate, Index.sourceTerms] using hz')
  simpa only [Reply.badSignEvaluationWidth, Reply.badSignEvaluationTime, one_mul] using h

end Signatures.Runtime.WeightedAGM.Extract
