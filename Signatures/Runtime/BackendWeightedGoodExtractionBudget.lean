import Signatures.Runtime.BackendWeightedGoodExtractionAssembly
import Signatures.Runtime.BackendWeightedExtractionWidth
import Signatures.Runtime.BackendWeightedExtractionCallState
import Signatures.Runtime.BackendWeightedExtraction

/-! Complete native good-extractor runtime, derived from primitive, sampling,
encoding and routing contracts. Every component budget is discharged here; the
transcript-cache premise is a state invariant of the preceding interaction. -/

open OracleComp OracleSpec PFunctor Model.LazyAGM Model.LazyAGM.WeightedReduction

namespace Signatures.Runtime.WeightedAGM.Extract

open BackendProgram Evaluate

def goodExtractionTime (index : Index) (overhead : Nat → Nat)
    (width hashCap signCap coeffCap cacheCap natEqTime natSubTime natAddTime topicTime indexTime scalarTime
      zeroTime addTime mulTime tickTime genIndexTime finZeroTime oneTime subTime divTime : Nat) : Nat :=
  hashExtractionTime overhead width hashCap coeffCap cacheCap natEqTime natSubTime natAddTime topicTime indexTime
      scalarTime zeroTime addTime mulTime tickTime oneTime +
    goodSigningCoefficientsTime index overhead width signCap coeffCap cacheCap natEqTime natSubTime natAddTime
      topicTime indexTime scalarTime zeroTime addTime mulTime tickTime genIndexTime finZeroTime oneTime +
    goodTargetTime index overhead width cacheCap natEqTime natSubTime natAddTime topicTime indexTime scalarTime
      zeroTime addTime mulTime tickTime genIndexTime finZeroTime oneTime +
    (finZeroTime + zeroTime + 64 * overhead (128 * width)) + addTime + subTime + divTime +
    512 * overhead (4096 * extractionWidth index width hashCap signCap coeffCap cacheCap)

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

theorem backendGood_bound (sampling : MachineCompiler.SamplingImplementation Q iface rep) (index : Index)
    (output : (AGM.outputTy index.messageTy).Value (cryptoBase F G₁ G₂ K M))
    (tr : Model.LazyAGM.Transcript (index.ty.Value (cryptoBase F G₁ G₂ K M))
      (index.messageTy.Value (cryptoBase F G₁ G₂ K M)) G₁)
    (cache : List (index.ty.Value (cryptoBase F G₁ G₂ K M) × F))
    (width hashCap signCap coeffCap cacheCap natEqTime natSubTime natAddTime topicTime indexTime scalarTime
      zeroTime addTime mulTime tickTime genIndexTime finZeroTime oneTime subTime divTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hn : ∀ k ≤ hashCap + signCap * (index.bound + 1) + (index.bound + 1) + index.bound + 1,
      Q.size rep.data.nat k ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hin : Q.size (rep.env [AGM.outputTy index.messageTy, Reply.transcriptTy index.ty index.messageTy]) (output, tr, ()) ≤ width)
    (hhash : ∀ p ∈ tr.1, Q.size (rep.ty (AGM.tokenTy index.ty)) p ≤ width)
    (hsign : ∀ p ∈ tr.2, Q.size (rep.ty (AGM.tokenTy index.messageTy)) p ≤ width)
    (hj : ∀ j : Fin (index.bound + 1), Q.size (rep.ty (boundedNat index.bound)) j ≤ width)
    (hnh : tr.1.length ≤ hashCap) (hnsign : tr.2.length ≤ signCap)
    (hng : output.2.2.1.length ≤ coeffCap) (hnx : output.2.2.2.length ≤ coeffCap)
    (hc : cache.length ≤ cacheCap) (hk : ∀ p ∈ cache, Q.size (rep.ty index.ty) p.1 ≤ 5 * width)
    (hcached : TranscriptCached (index.sourceTerms cost) (Reply.chronological tr) cache)
    (hne : ∀ j k, j ≤ hashCap + signCap * (index.bound + 1) + (index.bound + 1) + index.bound →
      k ≤ hashCap + signCap * (index.bound + 1) + (index.bound + 1) + index.bound →
      (primitiveBound .natEq).time (j, k) ≤ natEqTime)
    (hns : ∀ k ≤ hashCap + signCap * (index.bound + 1) + (index.bound + 1),
      (primitiveBound .natSub).time (k, 1) ≤ natSubTime)
    (hna : ∀ k ≤ hashCap + signCap * (index.bound + 1) + (index.bound + 1),
      (primitiveBound .natAdd).time (k, 1) ≤ natAddTime)
    (he : ∀ x y : K, Q.size (rep.ty key) x ≤ 3 * extractionWidth index width hashCap signCap coeffCap cacheCap →
      Q.size (rep.ty key) y ≤ 3 * extractionWidth index width hashCap signCap coeffCap cacheCap →
      (primitiveBound .keyEq).time (x, y) ≤ topicTime)
    (hi : ∀ j : Fin (index.bound + 1), (primitiveBound (.finVal index.bound)).time j ≤ indexTime)
    (hdraw : ∀ z ∈ support (sampling.scalar.run control queryCost ()), z.steps ≤ scalarTime)
    (hz : (primitiveBound .zero).time () ≤ zeroTime)
    (ha : ∀ x y : F, (primitiveBound .add).time (x, y) ≤ addTime)
    (hmul : ∀ x y : F, (primitiveBound .mul).time (x, y) ≤ mulTime)
    (htick : ∀ n ≤ hashCap + signCap * (index.bound + 1) + (index.bound + 1),
      ∀ encoded ≤ 7 * extractionWidth index width hashCap signCap coeffCap cacheCap, control.loop n encoded ≤ tickTime)
    (hgen : ∀ k ≤ index.bound + 1, (primitiveBound (.finOfNat index.bound)).time k ≤ genIndexTime)
    (hfin : (primitiveBound (.finZero index.bound)).time () ≤ finZeroTime)
    (hone : (primitiveBound .one).time () ≤ oneTime)
    (hsub : ∀ x y : F, (primitiveBound .sub).time (x, y) ≤ subTime)
    (hdiv : ∀ x y : F, (primitiveBound .div).time (x, y) ≤ divTime)
    (out : Run (F × List (index.ty.Value (cryptoBase F G₁ G₂ K M) × F)))
    (hout : out ∈ support ((backendGood rep data cost primitive sampling index).run
      control queryCost ((output, tr, ()), cache))) :
    (Q.size (rep.ty scalar) out.value.1 ≤ width ∧
      Q.size (rep.ty (Read.cacheTy index.ty scalar)) out.value.2 ≤ extractionWidth index width hashCap signCap coeffCap cacheCap) ∧
    out.steps ≤ goodExtractionTime index overhead width hashCap signCap coeffCap cacheCap natEqTime natSubTime natAddTime
      topicTime indexTime scalarTime zeroTime addTime mulTime tickTime genIndexTime finZeroTime oneTime subTime divTime := by
  let W := extractionWidth index width hashCap signCap coeffCap cacheCap
  let default := (defaultRow index.defaultTerm).denote (arithmetic F G₁ G₂ K M cost) (output, tr, ())
  have bounds := extractionWidth_bounds index width hashCap signCap coeffCap cacheCap
  have hw : width ≤ W := by omega
  have hhashW := bounds.2.2.1
  have hsignW := bounds.2.2.2.1
  have htargetW := bounds.2.2.2.2.2.1
  have hd : Q.size (rep.ty (evalRowTy index.ty)) default ≤ 5 * width :=
    defaultRow_size rep cost sizes index output tr width hh hin (hf 0) (hj 0)
  have hcacheSize := extractionCache_size rep sizes lists index (value := scalar) cache width hashCap signCap coeffCap cacheCap
    hh hk (fun f => (hf f).trans (by omega)) hc
  have hinit := defaultRow_cost rep data cost primitive laws dataLaws primitiveBound sizes mono index
    (output, tr, ()) width finZeroTime zeroTime hh hu hin (hf 0) (hj 0) hfin hz
  have h := goodExtraction_assembly rep data cost primitive laws dataLaws primitiveBound sizes mono control queryCost routing
    (Read.goodRead rep data cost primitive sampling index) (defaultRow index.defaultTerm)
    (evaluateCoefficients hashTerms (.op .zero .unit) goodCombine)
    (evaluateCoefficients index.terms (.op .zero .unit) goodCombine)
    (evaluateTarget index.terms (.op .zero .unit) goodCombine) output tr cache
    (fun c => c = cache) (fun c => c = cache) (fun c => c = cache)
    (fun c => Q.size (rep.ty (Read.cacheTy index.ty scalar)) c ≤ W)
    W (hashExtractionTime overhead width hashCap coeffCap cacheCap natEqTime natSubTime natAddTime topicTime indexTime
      scalarTime zeroTime addTime mulTime tickTime oneTime)
    (goodSigningCoefficientsTime index overhead width signCap coeffCap cacheCap natEqTime natSubTime natAddTime
      topicTime indexTime scalarTime zeroTime addTime mulTime tickTime genIndexTime finZeroTime oneTime)
    (goodTargetTime index overhead width cacheCap natEqTime natSubTime natAddTime topicTime indexTime scalarTime
      zeroTime addTime mulTime tickTime genIndexTime finZeroTime oneTime)
    (finZeroTime + zeroTime + 64 * overhead (128 * width)) addTime subTime divTime
    (hh.trans hw) (hu.trans hw) (fun f => (hf f).trans hw) (hin.trans hw) (hd.trans (by omega)) rfl
    (by rintro c rfl; exact hcacheSize) (by rintro c rfl; exact hcacheSize)
    (by rintro c rfl; exact hcacheSize) (fun _ h => h) ?_ ?_ ?_ hinit ha hsub hdiv out
    (by simpa only [backendGood, good, goodExtractionWith, goodHashArgs, goodSignArgs, goodTargetArgs, goodResult] using hout)
  · exact ⟨⟨hf _, h.1.2.1⟩, h.2⟩
  · intro c hc'
    subst c
    intro z hz'
    have hr := hashExtraction_bound rep data cost primitive laws dataLaws primitiveBound sizes lists mono control queryCost routing
      sampling index tr.1 output.2.2.1 default cache width hashCap coeffCap cacheCap natEqTime natSubTime natAddTime
      topicTime indexTime scalarTime zeroTime addTime mulTime tickTime oneTime hh hu hb (fun k hk => hn k (by omega)) hf
      hhash (hd.trans (by omega)) hnh hng hc (fun p hp => (hk p hp).trans (by omega))
      (fun j k hj hk => hne j k (by omega) (by omega)) (fun k hk => hns k (by omega)) (fun k hk => hna k (by omega))
      (fun x y hx hy => he x y (by omega) (by omega)) hi hdraw hz ha hmul
      (fun n hn encoded he => htick n (by omega) encoded (by omega)) hone z hz'
    have hcached' : TermsCached (Model.LazyAGM.WeightedReduction.signedTerms
        (fun i : index.ty.Value (cryptoBase F G₁ G₂ K M) => [(i, (1 : F))]) output.2.2.1 tr.1.reverse) cache := by
      rw [hash_signedTerms]
      exact hashTerms_cached _ _ _ hcached.1
    have hs := evaluateCoefficients_cached rep data cost primitive
      (Read.goodRead rep data cost primitive sampling index) (Read.goodRead_denote rep data cost primitive sampling index)
      control queryCost hashTerms (.op .zero .unit) goodCombine (by intros; rfl)
      (goodCombine_denote (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M) cost)
      tr.1 output.2.2.1 default cache hcached' z hz'
    exact ⟨hs, hr.2⟩
  · intro c hc'
    subst c
    intro z hz'
    have hr := goodSigningCoefficients_bound rep data cost primitive laws dataLaws primitiveBound sizes lists mono control queryCost routing
      sampling index tr.2 output.2.2.2 default cache width signCap coeffCap cacheCap natEqTime natSubTime natAddTime
      topicTime indexTime scalarTime zeroTime addTime mulTime tickTime genIndexTime finZeroTime oneTime
      hh hu hb (fun k hk => hn k (by omega)) hf hsign hj (hd.trans (by omega)) hnsign hnx hc
      (fun p hp => (hk p hp).trans (by omega))
      (fun j k hj hk => hne j k (by omega) (by omega)) (fun k hk => hns k (by omega)) (fun k hk => hna k (by omega))
      (fun x y hx hy => he x y (by omega) (by omega)) hi hdraw hz ha hmul
      (fun n hn encoded he => htick n (by omega) encoded (by omega)) hgen hfin hone z hz'
    have hs := evaluateCoefficients_cached rep data cost primitive
      (Read.goodRead rep data cost primitive sampling index) (Read.goodRead_denote rep data cost primitive sampling index)
      control queryCost index.terms (.op .zero .unit) goodCombine (by intros; rfl)
      (goodCombine_denote (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M) cost)
      tr.2 output.2.2.2 default cache (signedTerms_cached _ _ _ _ hcached.2) z hz'
    exact ⟨hs, hr.2⟩
  · intro c hc'
    subst c
    intro z hz'
    have hr := goodTarget_bound rep data cost primitive laws dataLaws primitiveBound sizes lists mono control queryCost routing
      sampling index output.1 default cache width cacheCap natEqTime natSubTime natAddTime
      topicTime indexTime scalarTime zeroTime addTime mulTime tickTime genIndexTime finZeroTime oneTime
      hh hu hb (fun k hk => hn k (by omega)) hf (extraction_target_size rep sizes output tr width hin) hj hd hc hk
      (fun j k hj hk => hne j k (by omega) (by omega)) (fun k hk => hns k (by omega)) (fun k hk => hna k (by omega))
      (fun x y hx hy => he x y (by omega) (by omega)) hi hdraw hz ha hmul
      (fun n hn encoded he => htick n (by omega) encoded (by omega)) hgen hfin hone z hz'
    exact ⟨hr.1.2.trans htargetW, hr.2⟩

end Signatures.Runtime.WeightedAGM.Extract
