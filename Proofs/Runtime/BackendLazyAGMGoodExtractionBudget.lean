import Proofs.Runtime.BackendLazyAGMGoodExtractionAssembly
import Proofs.Runtime.BackendLazyAGMGoodTokens

/-! Complete native good-extractor runtime certificate from primitive and
encoding contracts. Both chronological calls, all retained data, final target
access, and extraction arithmetic are composed with changing cache capacities. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.LazyAGM

open BackendProgram

def goodExtractionTime (overhead : Nat → Nat) (width queryCap coeffCap cacheCap
    natEqTime natSubTime natAddTime messageEqTime scalarTime zeroTime groupZeroTime
    addTime mulTime subTime divTime tickTime : Nat) : Nat :=
  let W := extractionWidth width queryCap coeffCap cacheCap
  let cap := cacheCap + 2 * queryCap
  let fee := overhead (32 * CacheCompiler.frameWidth W cap)
  goodTokenTime overhead (5 * width) queryCap coeffCap cacheCap natEqTime natSubTime natAddTime
    messageEqTime scalarTime zeroTime addTime mulTime tickTime +
  goodTokenTime overhead (5 * width) queryCap coeffCap (cacheCap + queryCap) natEqTime natSubTime natAddTime
    messageEqTime scalarTime zeroTime addTime mulTime tickTime +
  (cap * (messageEqTime + 257 * fee) + scalarTime + zeroTime + 192 * fee) +
  zeroTime + groupZeroTime + addTime + subTime + divTime + 512 * overhead (4096 * W)

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

theorem backendExtractGood_bound (sampling : MachineCompiler.SamplingImplementation Q iface rep)
    (output : (AGM.outputTy message).Value (cryptoBase F G₁ G₂ M M))
    (tr : Model.LazyAGM.Transcript M M G₁) (cache : List (M × F))
    (width queryCap coeffCap cacheCap natEqTime natSubTime natAddTime messageEqTime
      scalarTime zeroTime groupZeroTime addTime mulTime subTime divTime tickTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hn : ∀ n ≤ queryCap + 1, Q.size rep.data.nat n ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hg : Q.size (rep.ty point₁) (0 : G₁) ≤ width)
    (hi : Q.size (rep.env [AGM.outputTy message, transcriptTy]) (output, tr, ()) ≤ width)
    (ht : ∀ p ∈ tr.1 ++ tr.2, Q.size (rep.ty (AGM.tokenTy message)) p ≤ width)
    (htr : tr.1.length ≤ queryCap ∧ tr.2.length ≤ queryCap)
    (hcoeff : output.2.2.1.length ≤ coeffCap ∧ output.2.2.2.length ≤ coeffCap)
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
    (hdiv : ∀ x y : F, (primitiveBound CryptoOp.div).time (x, y) ≤ divTime)
    (htick : ∀ n ≤ queryCap, ∀ encoded ≤ 7 * extractionWidth width queryCap coeffCap cacheCap,
      control.loop n encoded ≤ tickTime)
    (out : Run (F × List (M × F)))
    (hout : out ∈ support ((backendExtractGood rep data cost primitive sampling).run
      control queryCost ((output, tr, ()), cache))) :
    (Q.size (rep.ty scalar) out.value.1 ≤ width ∧
      Q.size (rep.ty (cacheTy scalar)) out.value.2 ≤ extractionWidth width queryCap coeffCap cacheCap ∧
      ExtractionCache (fun m => Q.size (rep.ty message) m ≤ 5 * width)
        (cacheCap + 2 * queryCap + 1) out.value.2) ∧
      out.steps ≤ goodExtractionTime overhead width queryCap coeffCap cacheCap natEqTime natSubTime natAddTime
        messageEqTime scalarTime zeroTime groupZeroTime addTime mulTime subTime divTime tickTime := by
  let W := extractionWidth width queryCap coeffCap cacheCap
  let valid := fun m => Q.size (rep.ty message) m ≤ 5 * width
  let I := fun cap => ExtractionCache (R := F) valid cap
  let default := defaultRow.denote (arithmetic F G₁ G₂ M M cost) (output, tr, ())
  let tokens := evaluateTokens (.op .zero .unit) goodCombine
  let tokenTime := fun cap => goodTokenTime overhead (5 * width) queryCap coeffCap cap
    natEqTime natSubTime natAddTime messageEqTime scalarTime zeroTime addTime mulTime tickTime
  let readTime := (cacheCap + 2 * queryCap) * (messageEqTime +
    257 * overhead (32 * CacheCompiler.frameWidth W (cacheCap + 2 * queryCap))) +
      scalarTime + zeroTime + 192 * overhead (32 * CacheCompiler.frameWidth W (cacheCap + 2 * queryCap))
  have h5 : width ≤ 5 * width := by omega
  have h5W : 5 * width ≤ W := extractionWidth_base width queryCap coeffCap cacheCap
  have hw : width ≤ W := h5.trans h5W
  have hW3 : W ≤ 3 * W := by omega
  have hdefault : Q.size (rep.ty evalRowTy) default ≤ 5 * width :=
    extraction_default_size rep sizes cost output tr width hh (hf 0) hg hi
  have hstore (cap : Nat) (hcap : cap ≤ cacheCap + 2 * queryCap + 1) :
      ∀ c, I cap c → Q.size (rep.ty (cacheTy scalar)) c ≤ W := by
    intro c hc'
    exact extractionCache_size rep sizes lists (value := scalar) c width queryCap coeffCap cacheCap cap hh hc' hcap
      (fun f => (hf f).trans (by omega))
  have htoken (cap : Nat) (hcap : cap ≤ cacheCap + queryCap)
      (ts : List (M × G₁)) (cs : List F)
      (hts : ∀ p ∈ ts, Q.size (rep.ty (AGM.tokenTy message)) p ≤ width)
      (hnt : ts.length ≤ queryCap) (hnc : cs.length ≤ coeffCap) :
      ∀ c, I cap c → ∀ z ∈ support ((Language.compile rep data (arithmetic F G₁ G₂ M M cost) primitive
        (rep.ty (cacheTy scalar)) (readEffect rep data cost primitive sampling.scalar (.op .zero .unit)) tokens).run
          control queryCost ((ts, cs, default, ()), c)), I (cap + queryCap) z.value.2 ∧ z.steps ≤ tokenTime cap := by
    intro c hc' z hz'
    have hE : evaluationWidth (3 * (5 * width)) queryCap (cap + queryCap) ≤ W :=
      evaluationWidth_le_extractionWidth width queryCap coeffCap cacheCap _ _ (by omega) (by omega)
    have h := goodTokens_budget rep data cost primitive laws dataLaws primitiveBound sizes lists mono control queryCost routing
      sampling ts cs default c (5 * width) queryCap coeffCap cap natEqTime natSubTime natAddTime messageEqTime
      scalarTime zeroTime addTime mulTime tickTime (hh.trans h5) (hu.trans h5) (fun b => (hb b).trans h5)
      (fun n hn' => (hn n hn').trans h5) (fun f => (hf f).trans h5) (fun p hp => (hts p hp).trans h5)
      hdefault hnt hnc hc'.1 hc'.2 hne hns hna
      (fun x y hx hy => he x y (hx.trans (hE.trans hW3)) (hy.trans (hE.trans hW3)))
      hsample hz ha hm (fun n hn' encoded henc => htick n hn' encoded (henc.trans (Nat.mul_le_mul_left 7 hE))) z
      (by rw [backendEvaluateTokens]; exact hz')
    exact ⟨h.1.2.2, h.2⟩
  have hread : ∀ c, I (cacheCap + 2 * queryCap) c →
      ∀ z ∈ support ((backendGoodRead rep data cost primitive sampling).run control queryCost (output.1, c)),
        I (cacheCap + 2 * queryCap + 1) z.value.2 ∧ z.steps ≤ readTime := by
    intro c hc' z hz'
    have htarget := extraction_target_size rep sizes output tr width hi
    have hbnd := backendGoodRead_bound rep data cost primitive laws dataLaws primitiveBound sizes lists mono
      control queryCost routing sampling output.1 c W (cacheCap + 2 * queryCap) messageEqTime scalarTime zeroTime
      (hh.trans hw) (hu.trans hw) (fun b => (hb b).trans hw) (htarget.trans hw)
      (hstore _ (by omega) c hc') (fun p hp => (hc'.2 p hp).trans h5W) hc'.1
      (fun f => (hf f).trans hw) (fun x y hx hy => he x y (hx.trans hW3) (hy.trans hW3)) hsample hz z hz'
    have hstate := backendRead_state rep data cost primitive sampling.scalar (.op .zero .unit)
      (sampling.scalar_denote ()) control queryCost valid output.1 c (htarget.trans h5) hc'.2 z
      (by rw [backendGoodRead] at hz'; exact hz')
    exact ⟨⟨by have hlen := hc'.1; omega, hstate.2⟩, hbnd.2⟩
  have hsyntax : extractGood = goodExtractionWith tokens := rfl
  have hcode : backendExtractGood rep data cost primitive sampling =
      Language.compile rep data (arithmetic F G₁ G₂ M M cost) primitive (rep.ty (cacheTy scalar))
        (readEffect rep data cost primitive sampling.scalar (.op .zero .unit)) (goodExtractionWith tokens) := by
    rw [backendExtractGood]
    exact congrArg (fun p : Program CryptoOp (EvalCmd scalar) [AGM.outputTy message, transcriptTy] scalar =>
      Language.compile rep data (arithmetic F G₁ G₂ M M cost) primitive (rep.ty (cacheTy scalar))
        (readEffect rep data cost primitive sampling.scalar (.op .zero .unit)) p) hsyntax
  have hout' := (congrArg (fun code => out ∈ support (code.run control queryCost ((output, tr, ()), cache))) hcode).mp hout
  have h := goodExtraction_assembly rep data cost primitive laws dataLaws primitiveBound sizes mono control queryCost routing
    sampling tokens output tr cache (I cacheCap) (I (cacheCap + queryCap)) (I (cacheCap + 2 * queryCap))
    (I (cacheCap + 2 * queryCap + 1)) W (tokenTime cacheCap) (tokenTime (cacheCap + queryCap)) readTime
    zeroTime groupZeroTime addTime subTime divTime (hh.trans hw) (hu.trans hw) (fun f => (hf f).trans hw)
    (hg.trans hw) (hi.trans hw) (hdefault.trans h5W) ⟨hc, fun p hp => (hk p hp).trans h5⟩
    (hstore _ (by omega)) (hstore _ (by omega)) (hstore _ (by omega)) (hstore _ (by omega))
    (htoken cacheCap (by omega) tr.1 output.2.2.1 (fun p hp => ht p (List.mem_append_left _ hp)) htr.1 hcoeff.1)
    (by
      have hsign := htoken (cacheCap + queryCap) (by omega) tr.2 output.2.2.2
        (fun p hp => ht p (List.mem_append_right _ hp)) htr.2 hcoeff.2
      have hcap : (cacheCap + queryCap) + queryCap = cacheCap + 2 * queryCap := by omega
      simpa only [hcap] using hsign)
    hread hz hgz ha hsub hdiv out hout'
  exact ⟨⟨hf _, h.1.2.1, h.1.2.2⟩, h.2⟩

end Signatures.Runtime.LazyAGM
