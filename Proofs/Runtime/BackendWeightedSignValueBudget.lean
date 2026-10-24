import Proofs.Runtime.BackendWeightedSignAssembly
import Proofs.Runtime.BackendWeightedSignInputs
import Proofs.Runtime.BackendWeightedGoodEvaluate
import Proofs.Runtime.BackendWeightedBadEvaluate

/-! Complete runtime bounds for the actual signing-value programs, including
native term and fallback generation, private cache evaluation and retained-cache
routing. Only individual primitive, sampling, width and loop-tick bounds occur
as resource premises. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.WeightedAGM.Reply

open BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ K M : Type} [Field F]
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

def goodSignEvaluationWidth (index : Index) (width cap : Nat) : Nat :=
  Evaluate.evaluationWidth (5 * width) (index.bound + 1) (cap + (index.bound + 1))

def goodSignEvaluationTime (index : Index) (overhead : Nat → Nat)
    (width cap natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime tickTime : Nat) : Nat :=
  let rows := index.bound + 1
  let capacity := cap + rows
  let W := goodSignEvaluationWidth index width cap
  let fee := overhead (32 * CacheCompiler.frameWidth W capacity)
  rows * (rows * (natEqTime + natSubTime + 257 * fee) +
    capacity * (topicTime + 2 * indexTime + natEqTime + 391 * fee) + 2 * natAddTime +
    1 * addTime + 1 * mulTime + 1 * scalarTime + 1 * zeroTime + 516 * fee + tickTime) +
    1 * zeroTime + tickTime + 128 * fee

def goodSignValueTime (index : Index) (overhead : Nat → Nat)
    (width cap natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime tickTime genIndexTime finZeroTime oneTime : Nat) : Nat :=
  index.termsTime overhead width genIndexTime mulTime finZeroTime oneTime +
    (finZeroTime + zeroTime + 24 * overhead (64 * width)) +
    goodSignEvaluationTime index overhead width cap natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime tickTime +
    16 * overhead (64 * Terms.termSpace width (index.bound + 1))

def badSignEvaluationWidth (index : Index) (width cap : Nat) : Nat :=
  Evaluate.evaluationWidth (3 * (5 * width)) (index.bound + 1) (cap + (index.bound + 1))

def badSignEvaluationTime (index : Index) (overhead : Nat → Nat)
    (width cap natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime tickTime : Nat) : Nat :=
  let rows := index.bound + 1
  let capacity := cap + rows
  let W := badSignEvaluationWidth index width cap
  let fee := overhead (32 * CacheCompiler.frameWidth (3 * W) capacity)
  rows * (rows * (natEqTime + natSubTime + 257 * fee) +
    capacity * (topicTime + 2 * indexTime + natEqTime + 391 * fee) + 2 * natAddTime +
    2 * addTime + 2 * mulTime + 2 * scalarTime + 2 * zeroTime + 600 * fee + tickTime) +
    2 * zeroTime + tickTime + 128 * fee

def badSignValueTime (index : Index) (overhead : Nat → Nat)
    (width cap natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime tickTime genIndexTime finZeroTime oneTime : Nat) : Nat :=
  index.termsTime overhead width genIndexTime mulTime finZeroTime oneTime +
    (finZeroTime + zeroTime + 24 * overhead (64 * width)) +
    badSignEvaluationTime index overhead width cap natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime tickTime +
    16 * overhead (64 * Terms.termSpace width (index.bound + 1))

variable [SampleableType F] (sampling : MachineCompiler.SamplingImplementation Q iface rep) (index : Index)

include laws dataLaws primitiveBound sizes lists mono routing

theorem goodSignValue_bound
    (m : index.messageTy.Value (cryptoBase F G₁ G₂ K M))
    (cache : List (index.ty.Value (cryptoBase F G₁ G₂ K M) × F))
    (width cap natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime tickTime genIndexTime finZeroTime oneTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hm : Q.size (rep.ty index.messageTy) m ≤ width)
    (hc : Q.size (rep.ty (cacheTy index.ty scalar)) cache ≤ width)
    (hk : ∀ p ∈ cache, Q.size (rep.ty index.ty) p.1 ≤ width)
    (hlen : cache.length ≤ cap)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hj : ∀ j : Fin (index.bound + 1), Q.size (rep.ty (boundedNat index.bound)) j ≤ width)
    (hn : ∀ k ≤ (index.bound + 1) + index.bound + 1, Q.size rep.data.nat k ≤ width)
    (hne : ∀ j k, j ≤ (index.bound + 1) + index.bound → k ≤ (index.bound + 1) + index.bound →
      (primitiveBound .natEq).time (j, k) ≤ natEqTime)
    (hns : ∀ k ≤ index.bound + 1, (primitiveBound .natSub).time (k, 1) ≤ natSubTime)
    (hna : ∀ k ≤ index.bound + 1, (primitiveBound .natAdd).time (k, 1) ≤ natAddTime)
    (he : ∀ x y : K, Q.size (rep.ty key) x ≤ goodSignEvaluationWidth index width cap →
      Q.size (rep.ty key) y ≤ goodSignEvaluationWidth index width cap → (primitiveBound .keyEq).time (x, y) ≤ topicTime)
    (hi : ∀ j : Fin (index.bound + 1), (primitiveBound (.finVal index.bound)).time j ≤ indexTime)
    (hdraw : ∀ z ∈ support (sampling.scalar.run control queryCost ()), z.steps ≤ scalarTime)
    (hz : (primitiveBound .zero).time () ≤ zeroTime)
    (ha : ∀ x y : F, (primitiveBound .add).time (x, y) ≤ addTime)
    (hmul : ∀ x y : F, (primitiveBound .mul).time (x, y) ≤ mulTime)
    (htick : ∀ n ≤ index.bound + 1, ∀ encoded ≤ 7 * goodSignEvaluationWidth index width cap,
      control.loop n encoded ≤ tickTime)
    (hgen : ∀ k ≤ index.bound + 1, (primitiveBound (.finOfNat index.bound)).time k ≤ genIndexTime)
    (hfin : (primitiveBound (.finZero index.bound)).time () ≤ finZeroTime)
    (hone : (primitiveBound .one).time () ≤ oneTime)
    (out : Run (F × List (index.ty.Value (cryptoBase F G₁ G₂ K M) × F)))
    (hout : out ∈ support ((goodSignValue rep data cost primitive sampling index).run control queryCost (m, cache))) :
    Q.size (rep.ty (cacheResultTy index.ty scalar)) out.value ≤ 3 * goodSignEvaluationWidth index width cap ∧
      out.steps ≤ goodSignValueTime index overhead width cap natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime tickTime genIndexTime finZeroTime oneTime := by
  have h5 : width ≤ 5 * width := by omega
  have hprep : width ≤ Terms.termSpace width (index.bound + 1) := by dsimp [Terms.termSpace]; nlinarith
  have hdefault := index.default_size rep cost sizes m width hh hm (hf 0) (hj 0)
  have hterms := index.terms_size rep cost sizes lists m width hh hm hf hj
  have hrows := index.terms_rows_size rep cost sizes m width hh hm hf hj
  have hlength := index.terms_length (G₁ := G₁) (G₂ := G₂) (M := M) cost m
  have htermsTime := index.terms_cost rep data cost primitive laws dataLaws primitiveBound sizes lists mono
    m width genIndexTime mulTime finZeroTime oneTime hh hu hm hf hj
    (fun k hk => hn k (by omega)) hgen hmul hfin hone
  have hdefaultTime := index.default_cost rep data cost primitive laws dataLaws primitiveBound sizes mono
    m width finZeroTime zeroTime hh hu hm (hf 0) (hj 0) hfin hz
  apply signValue_bound rep data cost primitive laws dataLaws sizes mono control queryCost routing
    index.terms index.defaultTerm (Evaluate.backendGood rep data cost primitive sampling index)
    m cache (Terms.termSpace width (index.bound + 1)) (3 * goodSignEvaluationWidth index width cap)
    (index.termsTime overhead width genIndexTime mulTime finZeroTime oneTime)
    (finZeroTime + zeroTime + 24 * overhead (64 * width))
    (goodSignEvaluationTime index overhead width cap natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime tickTime)
    (hh.trans hprep) (hu.trans hprep) (hm.trans hprep) (hc.trans hprep) hterms
    (hdefault.trans (by dsimp [Terms.termSpace]; nlinarith)) htermsTime hdefaultTime ?_ out
    (by simpa only [goodSignValue] using hout)
  intro z hz'
  have h := Evaluate.backendGood_bound rep data cost primitive laws dataLaws primitiveBound sizes lists mono
    control queryCost routing sampling index (index.sourceTerms cost m)
    (index.defaultTerm.denote (arithmetic F G₁ G₂ K M cost) (m, ())) cache (5 * width) (index.bound + 1) cap
    natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime tickTime
    (hh.trans h5) (hu.trans h5) (fun b => (hb b).trans h5) (fun k hk => (hn k hk).trans h5)
    (fun f => (hf f).trans h5) hrows hdefault (le_of_eq hlength) hlen
    (fun p hp => (hk p hp).trans h5) hne hns hna he hi hdraw hz ha hmul htick z hz'
  have hw : width ≤ goodSignEvaluationWidth index width cap := by
    dsimp [goodSignEvaluationWidth, Evaluate.evaluationWidth]
    nlinarith
  have hp := sizes.prod_le (rep.ty scalar) (rep.ty (cacheTy index.ty scalar)) z.value
  change Q.size (rep.ty (cacheResultTy index.ty scalar)) z.value ≤ _ at hp
  have hvalue : Q.size (rep.ty scalar) z.value.1 ≤ goodSignEvaluationWidth index width cap := h.1.1
  have hcache : Q.size (rep.ty (cacheTy index.ty scalar)) z.value.2 ≤ goodSignEvaluationWidth index width cap := h.1.2
  refine ⟨hp.trans (by omega), ?_⟩
  simpa only [goodSignEvaluationTime, goodSignEvaluationWidth, one_mul] using h.2

theorem badSignValue_bound
    (m : index.messageTy.Value (cryptoBase F G₁ G₂ K M))
    (cache : List (index.ty.Value (cryptoBase F G₁ G₂ K M) × (F × F)))
    (width cap natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime tickTime genIndexTime finZeroTime oneTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hm : Q.size (rep.ty index.messageTy) m ≤ width)
    (hc : Q.size (rep.ty (cacheTy index.ty (.pair scalar scalar))) cache ≤ width)
    (hk : ∀ p ∈ cache, Q.size (rep.ty index.ty) p.1 ≤ width)
    (hlen : cache.length ≤ cap)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hj : ∀ j : Fin (index.bound + 1), Q.size (rep.ty (boundedNat index.bound)) j ≤ width)
    (hn : ∀ k ≤ (index.bound + 1) + index.bound + 1, Q.size rep.data.nat k ≤ width)
    (hne : ∀ j k, j ≤ (index.bound + 1) + index.bound → k ≤ (index.bound + 1) + index.bound →
      (primitiveBound .natEq).time (j, k) ≤ natEqTime)
    (hns : ∀ k ≤ index.bound + 1, (primitiveBound .natSub).time (k, 1) ≤ natSubTime)
    (hna : ∀ k ≤ index.bound + 1, (primitiveBound .natAdd).time (k, 1) ≤ natAddTime)
    (he : ∀ x y : K, Q.size (rep.ty key) x ≤ 3 * badSignEvaluationWidth index width cap →
      Q.size (rep.ty key) y ≤ 3 * badSignEvaluationWidth index width cap → (primitiveBound .keyEq).time (x, y) ≤ topicTime)
    (hi : ∀ j : Fin (index.bound + 1), (primitiveBound (.finVal index.bound)).time j ≤ indexTime)
    (hdraw : ∀ z ∈ support (sampling.scalar.run control queryCost ()), z.steps ≤ scalarTime)
    (hz : (primitiveBound .zero).time () ≤ zeroTime)
    (ha : ∀ x y : F, (primitiveBound .add).time (x, y) ≤ addTime)
    (hmul : ∀ x y : F, (primitiveBound .mul).time (x, y) ≤ mulTime)
    (htick : ∀ n ≤ index.bound + 1, ∀ encoded ≤ 7 * badSignEvaluationWidth index width cap,
      control.loop n encoded ≤ tickTime)
    (hgen : ∀ k ≤ index.bound + 1, (primitiveBound (.finOfNat index.bound)).time k ≤ genIndexTime)
    (hfin : (primitiveBound (.finZero index.bound)).time () ≤ finZeroTime)
    (hone : (primitiveBound .one).time () ≤ oneTime)
    (out : Run ((F × F) × List (index.ty.Value (cryptoBase F G₁ G₂ K M) × (F × F))))
    (hout : out ∈ support ((badSignValue rep data cost primitive sampling index).run control queryCost (m, cache))) :
    Q.size (rep.ty (cacheResultTy index.ty (.pair scalar scalar))) out.value ≤ 3 * badSignEvaluationWidth index width cap ∧
      out.steps ≤ badSignValueTime index overhead width cap natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime tickTime genIndexTime finZeroTime oneTime := by
  have h5 : width ≤ 5 * width := by omega
  have hprep : width ≤ Terms.termSpace width (index.bound + 1) := by dsimp [Terms.termSpace]; nlinarith
  have hdefault := index.default_size rep cost sizes m width hh hm (hf 0) (hj 0)
  have hterms := index.terms_size rep cost sizes lists m width hh hm hf hj
  have hrows := index.terms_rows_size rep cost sizes m width hh hm hf hj
  have hlength := index.terms_length (G₁ := G₁) (G₂ := G₂) (M := M) cost m
  have htermsTime := index.terms_cost rep data cost primitive laws dataLaws primitiveBound sizes lists mono
    m width genIndexTime mulTime finZeroTime oneTime hh hu hm hf hj
    (fun k hk => hn k (by omega)) hgen hmul hfin hone
  have hdefaultTime := index.default_cost rep data cost primitive laws dataLaws primitiveBound sizes mono
    m width finZeroTime zeroTime hh hu hm (hf 0) (hj 0) hfin hz
  apply signValue_bound rep data cost primitive laws dataLaws sizes mono control queryCost routing
    index.terms index.defaultTerm (Evaluate.backendBad rep data cost primitive sampling index)
    m cache (Terms.termSpace width (index.bound + 1)) (3 * badSignEvaluationWidth index width cap)
    (index.termsTime overhead width genIndexTime mulTime finZeroTime oneTime)
    (finZeroTime + zeroTime + 24 * overhead (64 * width))
    (badSignEvaluationTime index overhead width cap natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime tickTime)
    (hh.trans hprep) (hu.trans hprep) (hm.trans hprep) (hc.trans hprep) hterms
    (hdefault.trans (by dsimp [Terms.termSpace]; nlinarith)) htermsTime hdefaultTime ?_ out
    (by simpa only [badSignValue] using hout)
  intro z hz'
  have h := Evaluate.backendBad_bound rep data cost primitive laws dataLaws primitiveBound sizes lists mono
    control queryCost routing sampling index (index.sourceTerms cost m)
    (index.defaultTerm.denote (arithmetic F G₁ G₂ K M cost) (m, ())) cache (5 * width) (index.bound + 1) cap
    natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime tickTime
    (hh.trans h5) (hu.trans h5) (fun b => (hb b).trans h5) (fun k hk => (hn k hk).trans h5)
    (fun f => (hf f).trans h5) hrows hdefault (le_of_eq hlength) hlen
    (fun p hp => (hk p hp).trans h5) hne hns hna he hi hdraw hz ha hmul htick z hz'
  have hw : width ≤ badSignEvaluationWidth index width cap := by
    dsimp [badSignEvaluationWidth, Evaluate.evaluationWidth]
    nlinarith
  have hp := sizes.prod_le (rep.ty (.pair scalar scalar)) (rep.ty (cacheTy index.ty (.pair scalar scalar))) z.value
  change Q.size (rep.ty (cacheResultTy index.ty (.pair scalar scalar))) z.value ≤ _ at hp
  have hvalue : Q.size (rep.ty (.pair scalar scalar)) z.value.1 ≤ badSignEvaluationWidth index width cap := h.1.1
  have hcache : Q.size (rep.ty (cacheTy index.ty (.pair scalar scalar))) z.value.2 ≤ badSignEvaluationWidth index width cap := h.1.2
  refine ⟨hp.trans (by omega), ?_⟩
  simpa only [badSignEvaluationTime, badSignEvaluationWidth, one_mul] using h.2

end Signatures.Runtime.WeightedAGM.Reply
