import Signatures.Runtime.BackendLazyAGMReplyCost
import Signatures.Runtime.BackendLazyAGMReplyAssembly

/-! Complete costs for native lazy AGM hash/sign replies, obtained by composing
the actual argument, cache, response, and control code. The generic assembly
lemma's local-expression obligations are discharged using primitive costs. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.LazyAGM

open BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ M : Type} [Field F]
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

variable [SampleableType F]

theorem backendGoodReply_bound (samplingCode : MachineCompiler.SamplingImplementation Q iface rep)
    (signing : Bool) (m : M) (saved : (storeTy scalar goodConfigTy).Value (cryptoBase F G₁ G₂ M M))
    (width cap comparisonTime scalarTime zeroTime scaleTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hm : Q.size (rep.ty message) m ≤ width)
    (hs : Q.size (rep.ty (storeTy scalar goodConfigTy)) saved ≤ width)
    (hc : ∀ p ∈ saved.2.1, Q.size (rep.ty message) p.1 ≤ width)
    (hn : saved.2.1.length ≤ cap)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width)
    (he : ∀ x y : M, Q.size (rep.ty message) x ≤ 5 * width → Q.size (rep.ty message) y ≤ 5 * width →
      (primitiveBound CryptoOp.messageEq).time (x, y) ≤ comparisonTime)
    (hd : ∀ z ∈ support (samplingCode.scalar.run control queryCost ()), z.steps ≤ scalarTime)
    (hz : (primitiveBound CryptoOp.zero).time () ≤ zeroTime)
    (hscale : ∀ rho : F, ∀ g : G₁, (primitiveBound CryptoOp.scale₁).time (rho, g) ≤ scaleTime)
    (out : Run (G₁ × (storeTy scalar goodConfigTy).Value (cryptoBase F G₁ G₂ M M)))
    (hout : out ∈ support ((backendGoodReply rep data cost primitive samplingCode signing).run
      control queryCost (m, saved))) :
    Q.size (rep.ty (.pair point₁ (storeTy scalar goodConfigTy))) out.value ≤ 16 * replyWidth width cap ∧
      out.steps ≤ cap * (comparisonTime + 257 * overhead (64 * replyWidth width cap)) +
        scalarTime + zeroTime + scaleTime + 384 * overhead (64 * replyWidth width cap) := by
  let W := replyWidth width cap
  let fee := overhead (64 * W)
  have hw : width ≤ W := by dsimp [W, replyWidth, CacheCompiler.frameWidth]; nlinarith
  have h5 : width ≤ 5 * width := by omega
  have ha := goodCacheArgs_cost rep data cost primitive laws dataLaws primitiveBound sizes mono
    (m, saved, ()) (5 * width) zeroTime (hh.trans h5) (hu.trans h5) ((hf 0).trans h5)
    (replyFrame_size rep sizes (m, saved) width hh hu hm hs) hz
  have haFee : overhead (32 * (5 * width)) ≤ fee := by
    apply mono
    dsimp [W, replyWidth, CacheCompiler.frameWidth]
    nlinarith
  have hargs : Q.cost (Expression.arguments rep data (arithmetic F G₁ G₂ M M cost) primitive
      (cacheArgs (.op .zero .unit))) (m, saved, ()) ≤ zeroTime + 32 * fee := by omega
  have hresult : ∀ env, Q.size (rep.env [cacheResultTy scalar, message, storeTy scalar goodConfigTy]) env ≤ W →
      Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ M M cost) primitive
        (replyResult signing (goodResponse signing))) env ≤ scaleTime + 192 * fee := by
    intro env hi
    exact goodReplyResult_cost rep data cost primitive laws dataLaws primitiveBound sizes lists mono
      signing env W scaleTime (hh.trans hw) hi (fun g => (hg g).trans hw) hscale
  rw [backendGoodReply] at hout
  have h := backendReply_bound rep data cost primitive laws dataLaws primitiveBound sizes lists mono
    control queryCost routing samplingCode.scalar (.op .zero .unit) (goodResponse signing) signing m saved
    width cap comparisonTime scalarTime (zeroTime + 32 * fee) (scaleTime + 192 * fee)
    hh hu hb hm hs (fun p hp => ⟨hc p hp, hf p.2⟩) hn hg (hf 0) he
    (by intro u _ z hz'; cases u; exact ⟨hf z.value, hd z hz'⟩) hargs hresult out hout
  exact ⟨h.1, by dsimp only [fee, W] at h; omega⟩

theorem backendBadReply_bound (samplingCode : MachineCompiler.SamplingImplementation Q iface rep)
    (signing : Bool) (m : M)
    (saved : (storeTy (.pair scalar scalar) badConfigTy).Value (cryptoBase F G₁ G₂ M M))
    (width cap comparisonTime scalarTime zeroTime scaleTime addTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hm : Q.size (rep.ty message) m ≤ width)
    (hs : Q.size (rep.ty (storeTy (.pair scalar scalar) badConfigTy)) saved ≤ width)
    (hc : ∀ p ∈ saved.2.1, Q.size (rep.ty message) p.1 ≤ width)
    (hn : saved.2.1.length ≤ cap)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width)
    (he : ∀ x y : M, Q.size (rep.ty message) x ≤ 15 * width → Q.size (rep.ty message) y ≤ 15 * width →
      (primitiveBound CryptoOp.messageEq).time (x, y) ≤ comparisonTime)
    (hd : ∀ z ∈ support (samplingCode.scalar.run control queryCost ()), z.steps ≤ scalarTime)
    (hz : (primitiveBound CryptoOp.zero).time () ≤ zeroTime)
    (hscale : ∀ rho : F, ∀ g : G₁, (primitiveBound CryptoOp.scale₁).time (rho, g) ≤ scaleTime)
    (hadd : ∀ g h : G₁, (primitiveBound CryptoOp.add₁).time (g, h) ≤ addTime)
    (out : Run (G₁ × (storeTy (.pair scalar scalar) badConfigTy).Value (cryptoBase F G₁ G₂ M M)))
    (hout : out ∈ support ((backendBadReply rep data cost primitive samplingCode signing).run
      control queryCost (m, saved))) :
    Q.size (rep.ty (.pair point₁ (storeTy (.pair scalar scalar) badConfigTy))) out.value ≤
        16 * replyWidth (3 * width) cap ∧
      out.steps ≤ cap * (comparisonTime + 257 * overhead (64 * replyWidth (3 * width) cap)) +
        2 * scalarTime + 2 * zeroTime + 3 * scaleTime + addTime +
          468 * overhead (64 * replyWidth (3 * width) cap) := by
  let W := replyWidth (3 * width) cap
  let fee := overhead (64 * W)
  have hw : width ≤ W := by dsimp [W, replyWidth, CacheCompiler.frameWidth]; nlinarith
  have h3 : width ≤ 3 * width := by omega
  have h15 : width ≤ 15 * width := by omega
  have hp (p : F × F) : Q.size (rep.ty (.pair scalar scalar)) p ≤ 3 * width := by
    have h := sizes.prod_le (rep.ty scalar) (rep.ty scalar) p
    have h1 := hf p.1
    have h2 := hf p.2
    change Q.size (rep.ty (.pair scalar scalar)) p ≤ _ at h
    omega
  have ha := badCacheArgs_cost rep data cost primitive laws dataLaws primitiveBound sizes mono
    (m, saved, ()) (15 * width) zeroTime (hh.trans h15) (hu.trans h15) ((hf 0).trans h15)
    ((replyFrame_size rep sizes (m, saved) width hh hu hm hs).trans (by omega)) hz
  have haFee : overhead (32 * (15 * width)) ≤ fee := by
    apply mono
    dsimp [W, replyWidth, CacheCompiler.frameWidth]
    nlinarith
  have hargs : Q.cost (Expression.arguments rep data (arithmetic F G₁ G₂ M M cost) primitive
      (cacheArgs (.pair (.op .zero .unit) (.op .zero .unit)))) (m, saved, ()) ≤ 2 * zeroTime + 40 * fee := by omega
  have hresult : ∀ env, Q.size (rep.env
      [cacheResultTy (.pair scalar scalar), message, storeTy (.pair scalar scalar) badConfigTy]) env ≤ W →
      Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ M M cost) primitive
        (replyResult signing (badResponse signing))) env ≤ 3 * scaleTime + addTime + 256 * fee := by
    intro env hi
    exact badReplyResult_cost rep data cost primitive laws dataLaws primitiveBound sizes lists mono
      signing env W scaleTime addTime (hh.trans hw) hi (fun g => (hg g).trans hw) hscale hadd
  have component : Bounds control queryCost samplingCode.scalar (fun _ => True)
      (fun f => Q.size (rep.ty scalar) f ≤ width) scalarTime := by
    intro u _ z hz'
    cases u
    exact ⟨hf z.value, hd z hz'⟩
  have hpSampler := PairSampling.bound rep.data data (rep.ty scalar) (rep.ty scalar)
    samplingCode.scalar samplingCode.scalar sizes laws dataLaws mono control queryCost routing
    width scalarTime scalarTime hh hu component component
  have hpFee : overhead (8 * width) ≤ fee := mono (by omega)
  have hdraw : Bounds control queryCost (pairSampler rep data samplingCode) (fun _ => True)
      (fun r => Q.size (rep.ty (.pair scalar scalar)) r ≤ 3 * width) (2 * scalarTime + 12 * fee) := by
    intro u hi z hz'
    have h := hpSampler u hi z hz'
    exact ⟨hp z.value, by omega⟩
  rw [backendBadReply] at hout
  have h := backendReply_bound rep data cost primitive laws dataLaws primitiveBound sizes lists mono
    control queryCost routing (pairSampler rep data samplingCode) (.pair (.op .zero .unit) (.op .zero .unit))
    (badResponse signing) signing m saved (3 * width) cap comparisonTime (2 * scalarTime + 12 * fee)
    (2 * zeroTime + 40 * fee) (3 * scaleTime + addTime + 256 * fee)
    (hh.trans h3) (hu.trans h3) (fun b => (hb b).trans h3) (hm.trans h3) (hs.trans h3)
    (fun p hmem => ⟨(hc p hmem).trans h3, hp p.2⟩) hn (fun g => (hg g).trans h3) (hp (0, 0))
    (by intro x y hx hy; apply he x y <;> omega) hdraw hargs hresult out hout
  exact ⟨h.1, by dsimp only [fee, W] at h; omega⟩

end Signatures.Runtime.LazyAGM
