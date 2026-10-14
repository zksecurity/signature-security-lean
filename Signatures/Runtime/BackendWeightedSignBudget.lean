import Signatures.Runtime.BackendWeightedReplyAssembly
import Signatures.Runtime.BackendWeightedSignValueBudget

/-! Complete native signing-reply runtime bounds for OOPS and Proximity, in both
AGM branches. These assemble actual generated terms, fallback construction,
private reads and arithmetic, the response and reverse transcript update. -/

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

def goodSignWidth (index : Index) (width cap : Nat) : Nat :=
  replyWidth width (3 * goodSignEvaluationWidth index width cap)

def goodSignTime (index : Index) (overhead : Nat → Nat)
    (width cap natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime tickTime genIndexTime finZeroTime oneTime scaleTime : Nat) : Nat :=
  goodSignValueTime index overhead width cap natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime tickTime genIndexTime finZeroTime oneTime +
    scaleTime + 224 * overhead (64 * goodSignWidth index width cap)

def badSignWidth (index : Index) (width cap : Nat) : Nat :=
  replyWidth width (3 * badSignEvaluationWidth index width cap)

def badSignTime (index : Index) (overhead : Nat → Nat)
    (width cap natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime tickTime genIndexTime finZeroTime oneTime scaleTime groupAddTime : Nat) : Nat :=
  badSignValueTime index overhead width cap natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime tickTime genIndexTime finZeroTime oneTime +
    3 * scaleTime + groupAddTime + 288 * overhead (64 * badSignWidth index width cap)

variable [SampleableType F] (sampling : MachineCompiler.SamplingImplementation Q iface rep) (index : Index)

include laws dataLaws primitiveBound sizes lists mono routing

theorem goodSign_bound
    (m : index.messageTy.Value (cryptoBase F G₁ G₂ K M))
    (saved : (storeTy index.ty index.messageTy scalar LazyAGM.goodConfigTy).Value (cryptoBase F G₁ G₂ K M))
    (width cap natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime tickTime genIndexTime finZeroTime oneTime scaleTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hm : Q.size (rep.ty index.messageTy) m ≤ width)
    (hs : Q.size (rep.ty (storeTy index.ty index.messageTy scalar LazyAGM.goodConfigTy)) saved ≤ width)
    (hk : ∀ p ∈ saved.2.1, Q.size (rep.ty index.ty) p.1 ≤ width)
    (hlen : saved.2.1.length ≤ cap)
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
    (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width)
    (hscale : ∀ r : F, ∀ g : G₁, (primitiveBound .scale₁).time (r, g) ≤ scaleTime)
    (out : Run (G₁ × (storeTy index.ty index.messageTy scalar LazyAGM.goodConfigTy).Value (cryptoBase F G₁ G₂ K M)))
    (hout : out ∈ support ((goodSign rep data cost primitive sampling index).run control queryCost (m, saved))) :
    Q.size (rep.ty (.pair point₁ (storeTy index.ty index.messageTy scalar LazyAGM.goodConfigTy))) out.value ≤
        16 * goodSignWidth index width cap ∧
      out.steps ≤ goodSignTime index overhead width cap natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime tickTime genIndexTime finZeroTime oneTime scaleTime := by
  have hc : Q.size (rep.ty (cacheTy index.ty scalar)) saved.2.1 ≤ width := by
    have h₁ := sizes.snd_le (rep.ty LazyAGM.goodConfigTy)
      (rep.ty (.pair (cacheTy index.ty scalar) (transcriptTy index.ty index.messageTy))) saved
    have h₂ := sizes.fst_le (rep.ty (cacheTy index.ty scalar))
      (rep.ty (transcriptTy index.ty index.messageTy)) saved.2
    exact h₂.trans (h₁.trans hs)
  have hw : width ≤ goodSignWidth index width cap := by dsimp [goodSignWidth, replyWidth]; omega
  have result := backendReply_bound rep data cost primitive laws dataLaws primitiveBound sizes lists mono
    control queryCost routing true (goodSignValue rep data cost primitive sampling index)
    (LazyAGM.goodResponse true) m saved width (3 * goodSignEvaluationWidth index width cap)
    (goodSignValueTime index overhead width cap natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime tickTime genIndexTime finZeroTime oneTime)
    (scaleTime + 192 * overhead (64 * goodSignWidth index width cap)) hh hu hm hs hg (by
      intro z hz'
      exact goodSignValue_bound rep data cost primitive laws dataLaws primitiveBound sizes lists mono
        control queryCost routing sampling index m saved.2.1 width cap natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime tickTime genIndexTime finZeroTime oneTime
        hh hu hb hm hc hk hlen hf hj hn hne hns hna he hi hdraw hz ha hmul htick hgen hfin hone z hz') (by
      intro env henv
      exact goodReplyResult_cost rep data cost primitive laws dataLaws primitiveBound sizes lists mono
        true env (goodSignWidth index width cap) scaleTime (hh.trans hw) henv
        (fun g => (hg g).trans hw) hscale) out (by
      simpa only [goodSign] using hout)
  refine ⟨result.1, result.2.trans ?_⟩
  dsimp only [goodSignTime, goodSignWidth]
  omega

theorem badSign_bound
    (m : index.messageTy.Value (cryptoBase F G₁ G₂ K M))
    (saved : (storeTy index.ty index.messageTy (.pair scalar scalar) LazyAGM.badConfigTy).Value (cryptoBase F G₁ G₂ K M))
    (width cap natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime tickTime genIndexTime finZeroTime oneTime scaleTime groupAddTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hm : Q.size (rep.ty index.messageTy) m ≤ width)
    (hs : Q.size (rep.ty (storeTy index.ty index.messageTy (.pair scalar scalar) LazyAGM.badConfigTy)) saved ≤ width)
    (hk : ∀ p ∈ saved.2.1, Q.size (rep.ty index.ty) p.1 ≤ width)
    (hlen : saved.2.1.length ≤ cap)
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
    (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width)
    (hscale : ∀ r : F, ∀ g : G₁, (primitiveBound .scale₁).time (r, g) ≤ scaleTime)
    (hadd : ∀ g h : G₁, (primitiveBound .add₁).time (g, h) ≤ groupAddTime)
    (out : Run (G₁ × (storeTy index.ty index.messageTy (.pair scalar scalar) LazyAGM.badConfigTy).Value (cryptoBase F G₁ G₂ K M)))
    (hout : out ∈ support ((badSign rep data cost primitive sampling index).run control queryCost (m, saved))) :
    Q.size (rep.ty (.pair point₁ (storeTy index.ty index.messageTy (.pair scalar scalar) LazyAGM.badConfigTy))) out.value ≤
        16 * badSignWidth index width cap ∧
      out.steps ≤ badSignTime index overhead width cap natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime tickTime genIndexTime finZeroTime oneTime scaleTime groupAddTime := by
  have hc : Q.size (rep.ty (cacheTy index.ty (.pair scalar scalar))) saved.2.1 ≤ width := by
    have h₁ := sizes.snd_le (rep.ty LazyAGM.badConfigTy)
      (rep.ty (.pair (cacheTy index.ty (.pair scalar scalar)) (transcriptTy index.ty index.messageTy))) saved
    have h₂ := sizes.fst_le (rep.ty (cacheTy index.ty (.pair scalar scalar)))
      (rep.ty (transcriptTy index.ty index.messageTy)) saved.2
    exact h₂.trans (h₁.trans hs)
  have hw : width ≤ badSignWidth index width cap := by dsimp [badSignWidth, replyWidth]; omega
  have result := backendReply_bound rep data cost primitive laws dataLaws primitiveBound sizes lists mono
    control queryCost routing true (badSignValue rep data cost primitive sampling index)
    (LazyAGM.badResponse true) m saved width (3 * badSignEvaluationWidth index width cap)
    (badSignValueTime index overhead width cap natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime tickTime genIndexTime finZeroTime oneTime)
    (3 * scaleTime + groupAddTime + 256 * overhead (64 * badSignWidth index width cap)) hh hu hm hs hg (by
      intro z hz'
      exact badSignValue_bound rep data cost primitive laws dataLaws primitiveBound sizes lists mono
        control queryCost routing sampling index m saved.2.1 width cap natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime tickTime genIndexTime finZeroTime oneTime
        hh hu hb hm hc hk hlen hf hj hn hne hns hna he hi hdraw hz ha hmul htick hgen hfin hone z hz') (by
      intro env henv
      exact badReplyResult_cost rep data cost primitive laws dataLaws primitiveBound sizes lists mono
        true env (badSignWidth index width cap) scaleTime groupAddTime (hh.trans hw) henv
        (fun g => (hg g).trans hw) hscale hadd) out (by
      simpa only [badSign] using hout)
  refine ⟨result.1, result.2.trans ?_⟩
  dsimp only [badSignTime, badSignWidth]
  omega

end Signatures.Runtime.WeightedAGM.Reply
