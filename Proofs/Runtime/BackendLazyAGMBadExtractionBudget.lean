import Proofs.Runtime.BackendLazyAGMBadExtractionAssembly
import Proofs.Runtime.BackendLazyAGMBadTokens

/-! Complete native bad-extractor runtime certificate from primitive and
encoding contracts. The signing evaluation, final target access, and extraction
arithmetic retain and charge the entire original output and both transcripts. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.LazyAGM

open BackendProgram

def badExtractionTime (overhead : Nat → Nat) (width queryCap coeffCap cacheCap
    natEqTime natSubTime natAddTime messageEqTime scalarTime zeroTime groupZeroTime
    addTime mulTime subTime negTime divTime tickTime : Nat) : Nat :=
  let W := extractionWidth width queryCap coeffCap cacheCap
  let cap := cacheCap + queryCap
  let fee := overhead (32 * CacheCompiler.frameWidth (3 * W) cap)
  badTokenTime overhead (5 * width) queryCap coeffCap cacheCap natEqTime natSubTime natAddTime
    messageEqTime scalarTime zeroTime addTime mulTime tickTime +
  (cap * (messageEqTime + 257 * fee) + 2 * scalarTime + 2 * zeroTime + 212 * fee) +
  zeroTime + groupZeroTime + 2 * subTime + negTime + divTime + 512 * overhead (4096 * W)

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ M : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ M M cost).execute instr))
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  (mono : Monotone overhead) (control : ControlCosts)
  (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (routing : RoutingCostLaws control overhead)

include laws dataLaws primitiveBound sizes lists mono routing

attribute [local irreducible] Language.compile Expression.compile Expression.arguments

theorem backendExtractBad_bound (sampling : MachineCompiler.SamplingImplementation Q iface rep)
    (output : (AGM.outputTy message).Value (cryptoBase F G₁ G₂ M M))
    (tr : Model.LazyAGM.Transcript M M G₁) (cache : List (M × (F × F)))
    (width queryCap coeffCap cacheCap natEqTime natSubTime natAddTime messageEqTime
      scalarTime zeroTime groupZeroTime addTime mulTime subTime negTime divTime tickTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hn : ∀ n ≤ queryCap + 1, Q.size rep.data.nat n ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hg : Q.size (rep.ty point₁) (0 : G₁) ≤ width)
    (hi : Q.size (rep.env [AGM.outputTy message, transcriptTy]) (output, tr, ()) ≤ width)
    (ht : ∀ p ∈ tr.2, Q.size (rep.ty (AGM.tokenTy message)) p ≤ width)
    (htr : tr.2.length ≤ queryCap) (hcoeff : output.2.2.2.length ≤ coeffCap)
    (hc : cache.length ≤ cacheCap) (hk : ∀ p ∈ cache, Q.size (rep.ty message) p.1 ≤ width)
    (hne : ∀ n ≤ queryCap, (primitiveBound CryptoOp.natEq).time (n, 0) ≤ natEqTime)
    (hns : ∀ n ≤ queryCap, (primitiveBound CryptoOp.natSub).time (n, 1) ≤ natSubTime)
    (hna : ∀ n ≤ queryCap, (primitiveBound CryptoOp.natAdd).time (n, 1) ≤ natAddTime)
    (he : ∀ x y : M,
      Q.size (rep.ty message) x ≤ 3 * extractionWidth width queryCap coeffCap cacheCap →
      Q.size (rep.ty message) y ≤ 3 * extractionWidth width queryCap coeffCap cacheCap →
        (primitiveBound CryptoOp.messageEq).time (x, y) ≤ messageEqTime)
    (hsample : ∀ z ∈ support (sampling.scalar.run control queryCost ()), z.steps ≤ scalarTime)
    (hz : (primitiveBound CryptoOp.zero).time () ≤ zeroTime)
    (hgz : (primitiveBound CryptoOp.zero₁).time () ≤ groupZeroTime)
    (ha : ∀ x y : F, (primitiveBound CryptoOp.add).time (x, y) ≤ addTime)
    (hm : ∀ x y : F, (primitiveBound CryptoOp.mul).time (x, y) ≤ mulTime)
    (hsub : ∀ x y : F, (primitiveBound CryptoOp.sub).time (x, y) ≤ subTime)
    (hneg : ∀ x : F, (primitiveBound CryptoOp.neg).time x ≤ negTime)
    (hdiv : ∀ x y : F, (primitiveBound CryptoOp.div).time (x, y) ≤ divTime)
    (htick : ∀ n ≤ queryCap, ∀ encoded ≤ 7 * extractionWidth width queryCap coeffCap cacheCap,
      control.loop n encoded ≤ tickTime)
    (out : Run (F × List (M × (F × F))))
    (hout : out ∈ support ((backendExtractBad rep data cost primitive sampling).run
      control queryCost ((output, tr, ()), cache))) :
    (Q.size (rep.ty scalar) out.value.1 ≤ width ∧
      Q.size (rep.ty (cacheTy (.pair scalar scalar))) out.value.2 ≤ extractionWidth width queryCap coeffCap cacheCap ∧
      ExtractionCache (fun m => Q.size (rep.ty message) m ≤ 5 * width)
        (cacheCap + queryCap + 1) out.value.2) ∧
      out.steps ≤ badExtractionTime overhead width queryCap coeffCap cacheCap natEqTime natSubTime natAddTime
        messageEqTime scalarTime zeroTime groupZeroTime addTime mulTime subTime negTime divTime tickTime := by
  let W := extractionWidth width queryCap coeffCap cacheCap
  let valid := fun m => Q.size (rep.ty message) m ≤ 5 * width
  let I := fun cap => ExtractionCache (R := F × F) valid cap
  let default := defaultRow.denote (arithmetic F G₁ G₂ M M cost) (output, tr, ())
  let tokens := evaluateTokens (.pair (.op .zero .unit) (.op .zero .unit)) badCombine
  let tokenTime := badTokenTime overhead (5 * width) queryCap coeffCap cacheCap
    natEqTime natSubTime natAddTime messageEqTime scalarTime zeroTime addTime mulTime tickTime
  let readTime := (cacheCap + queryCap) * (messageEqTime +
    257 * overhead (32 * CacheCompiler.frameWidth (3 * W) (cacheCap + queryCap))) +
      2 * scalarTime + 2 * zeroTime + 212 * overhead (32 * CacheCompiler.frameWidth (3 * W) (cacheCap + queryCap))
  have h5 : width ≤ 5 * width := by omega
  have h5W : 5 * width ≤ W := extractionWidth_base width queryCap coeffCap cacheCap
  have hw : width ≤ W := h5.trans h5W
  have hpair (p : F × F) : Q.size (rep.ty (.pair scalar scalar)) p ≤ 3 * width := by
    have hp := sizes.prod_le (rep.ty scalar) (rep.ty scalar) p
    have h1 := hf p.1
    have h2 := hf p.2
    change Q.size (rep.ty (.pair scalar scalar)) p ≤ _ at hp
    omega
  have hdefault : Q.size (rep.ty evalRowTy) default ≤ 5 * width :=
    extraction_default_size rep sizes cost output tr width hh (hf 0) hg hi
  have hstore (cap : Nat) (hcap : cap ≤ cacheCap + 2 * queryCap + 1) :
      ∀ c, I cap c → Q.size (rep.ty (cacheTy (.pair scalar scalar))) c ≤ W := by
    intro c hc'
    exact extractionCache_size rep sizes lists (value := .pair scalar scalar) c width queryCap coeffCap cacheCap cap hh hc' hcap hpair
  have htoken : ∀ c, I cacheCap c →
      ∀ z ∈ support ((Language.compile rep data (arithmetic F G₁ G₂ M M cost) primitive
        (rep.ty (cacheTy (.pair scalar scalar)))
        (readEffect rep data cost primitive (pairSampler rep data sampling) (.pair (.op .zero .unit) (.op .zero .unit))) tokens).run
          control queryCost ((tr.2, output.2.2.2, default, ()), c)), I (cacheCap + queryCap) z.value.2 ∧ z.steps ≤ tokenTime := by
    intro c hc' z hz'
    have hE : evaluationWidth (9 * (5 * width)) queryCap (cacheCap + queryCap) ≤ W :=
      evaluationWidth_le_extractionWidth width queryCap coeffCap cacheCap _ _ (by omega) (by omega)
    have h := badTokens_budget rep data cost primitive laws dataLaws primitiveBound sizes lists mono control queryCost routing
      sampling tr.2 output.2.2.2 default c (5 * width) queryCap coeffCap cacheCap natEqTime natSubTime natAddTime messageEqTime
      scalarTime zeroTime addTime mulTime tickTime (hh.trans h5) (hu.trans h5) (fun b => (hb b).trans h5)
      (fun n hn' => (hn n hn').trans h5) (fun f => (hf f).trans h5) (fun p hp => (ht p hp).trans h5)
      hdefault htr hcoeff hc'.1 hc'.2 hne hns hna
      (fun x y hx hy => he x y (hx.trans (Nat.mul_le_mul_left 3 hE)) (hy.trans (Nat.mul_le_mul_left 3 hE)))
      hsample hz ha hm (fun n hn' encoded henc => htick n hn' encoded (henc.trans (Nat.mul_le_mul_left 7 hE))) z
      (by rw [backendEvaluateTokens]; exact hz')
    exact ⟨h.1.2.2, h.2⟩
  have hread : ∀ c, I (cacheCap + queryCap) c →
      ∀ z ∈ support ((backendBadRead rep data cost primitive sampling).run control queryCost (output.1, c)),
        I (cacheCap + queryCap + 1) z.value.2 ∧ z.steps ≤ readTime := by
    intro c hc' z hz'
    have htarget := extraction_target_size rep sizes output tr width hi
    have hbnd := backendBadRead_bound rep data cost primitive laws dataLaws primitiveBound sizes lists mono
      control queryCost routing sampling output.1 c W (cacheCap + queryCap) messageEqTime scalarTime zeroTime
      (hh.trans hw) (hu.trans hw) (fun b => (hb b).trans hw) (htarget.trans hw)
      (hstore _ (by omega) c hc') (fun p hp => (hc'.2 p hp).trans h5W) hc'.1
      (fun f => (hf f).trans hw) he hsample hz z hz'
    have hstate := backendRead_state rep data cost primitive (pairSampler rep data sampling)
      (.pair (.op .zero .unit) (.op .zero .unit)) (pairSampler_denote rep data sampling ())
      control queryCost valid output.1 c (htarget.trans h5) hc'.2 z
      (by rw [backendBadRead] at hz'; exact hz')
    exact ⟨⟨by have hlen := hc'.1; omega, hstate.2⟩, hbnd.2⟩
  have hsyntax : extractBad = badExtractionWith tokens := rfl
  have hcode : backendExtractBad rep data cost primitive sampling =
      Language.compile rep data (arithmetic F G₁ G₂ M M cost) primitive (rep.ty (cacheTy (.pair scalar scalar)))
        (readEffect rep data cost primitive (pairSampler rep data sampling) (.pair (.op .zero .unit) (.op .zero .unit)))
        (badExtractionWith tokens) := by
    rw [backendExtractBad]
    exact congrArg (fun p : Program CryptoOp (EvalCmd (.pair scalar scalar)) [AGM.outputTy message, transcriptTy] scalar =>
      Language.compile rep data (arithmetic F G₁ G₂ M M cost) primitive (rep.ty (cacheTy (.pair scalar scalar)))
        (readEffect rep data cost primitive (pairSampler rep data sampling) (.pair (.op .zero .unit) (.op .zero .unit))) p) hsyntax
  have hout' := (congrArg (fun code => out ∈ support (code.run control queryCost ((output, tr, ()), cache))) hcode).mp hout
  have h := badExtraction_assembly rep data cost primitive laws dataLaws primitiveBound sizes mono control queryCost routing
    sampling tokens output tr cache (I cacheCap) (I (cacheCap + queryCap)) (I (cacheCap + queryCap + 1))
    W tokenTime readTime zeroTime groupZeroTime subTime negTime divTime
    (hh.trans hw) (hu.trans hw) (fun f => (hf f).trans hw) (fun p => (hpair p).trans (by omega))
    (hg.trans hw) (hi.trans hw) (hdefault.trans h5W) ⟨hc, fun p hp => (hk p hp).trans h5⟩
    (hstore _ (by omega)) (hstore _ (by omega)) (hstore _ (by omega))
    htoken hread hz hgz hsub hneg hdiv out hout'
  exact ⟨⟨hf _, h.1.2.1, h.1.2.2⟩, h.2⟩

end Signatures.Runtime.LazyAGM
