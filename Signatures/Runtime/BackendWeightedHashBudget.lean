import Signatures.Runtime.BackendWeightedReplyAssembly
import Signatures.Runtime.BackendWeightedReadBudget

/-! Complete runtime bounds for actual weighted hash replies in both reduction
branches. All private cache work, sampling, response computation, transcript
updates and retained-store routing are derived from primitive contracts. -/

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

/-- One common frame bound for scalar and paired-mask hash replies. -/
def hashWidth (width cap : Nat) : Nat :=
  replyWidth width ((4 * (cap + 1) + 3) * (3 * width))

def goodHashTime (overhead : Nat → Nat)
    (width cap topicTime indexTime natTime scalarTime zeroTime scaleTime : Nat) : Nat :=
  Read.goodTime overhead width cap (topicTime + 2 * indexTime + natTime) scalarTime zeroTime +
    scaleTime + 224 * overhead (64 * hashWidth width cap)

def badHashTime (overhead : Nat → Nat)
    (width cap topicTime indexTime natTime scalarTime zeroTime scaleTime addTime : Nat) : Nat :=
  Read.badTime overhead width cap (topicTime + 2 * indexTime + natTime) scalarTime zeroTime +
    3 * scaleTime + addTime + 288 * overhead (64 * hashWidth width cap)

variable [SampleableType F] (sampling : MachineCompiler.SamplingImplementation Q iface rep) (index : Index)

include laws dataLaws primitiveBound sizes lists mono routing

theorem goodHash_bound
    (request : index.ty.Value (cryptoBase F G₁ G₂ K M))
    (saved : (storeTy index.ty index.messageTy scalar LazyAGM.goodConfigTy).Value (cryptoBase F G₁ G₂ K M))
    (width cap topicTime indexTime natTime scalarTime zeroTime scaleTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hn : ∀ j ≤ index.bound, Q.size rep.data.nat j ≤ width)
    (hm : Q.size (rep.ty index.ty) request ≤ width)
    (hs : Q.size (rep.ty (storeTy index.ty index.messageTy scalar LazyAGM.goodConfigTy)) saved ≤ width)
    (hk : ∀ p ∈ saved.2.1, Q.size (rep.ty index.ty) p.1 ≤ width)
    (hlen : saved.2.1.length ≤ cap)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width)
    (he : ∀ a b : K, Q.size (rep.ty key) a ≤ width → Q.size (rep.ty key) b ≤ width →
      (primitiveBound .keyEq).time (a, b) ≤ topicTime)
    (hi : ∀ j : Fin (index.bound + 1), (primitiveBound (.finVal index.bound)).time j ≤ indexTime)
    (heq : ∀ j k : Nat, j ≤ index.bound → k ≤ index.bound → (primitiveBound .natEq).time (j, k) ≤ natTime)
    (hdraw : ∀ z ∈ support (sampling.scalar.run control queryCost ()), z.steps ≤ scalarTime)
    (hz : (primitiveBound .zero).time () ≤ zeroTime)
    (hscale : ∀ r : F, ∀ g : G₁, (primitiveBound .scale₁).time (r, g) ≤ scaleTime)
    (out : Run (G₁ × (storeTy index.ty index.messageTy scalar LazyAGM.goodConfigTy).Value (cryptoBase F G₁ G₂ K M)))
    (hout : out ∈ support ((goodHash rep data cost primitive sampling index).run control queryCost (request, saved))) :
    Q.size (rep.ty (.pair point₁ (storeTy index.ty index.messageTy scalar LazyAGM.goodConfigTy))) out.value ≤
        16 * hashWidth width cap ∧
      out.steps ≤ goodHashTime overhead width cap topicTime indexTime natTime scalarTime zeroTime scaleTime := by
  have hc : Q.size (rep.ty (cacheTy index.ty scalar)) saved.2.1 ≤ width := by
    have h₁ := sizes.snd_le (rep.ty LazyAGM.goodConfigTy)
      (rep.ty (.pair (cacheTy index.ty scalar) (transcriptTy index.ty index.messageTy))) saved
    have h₂ := sizes.fst_le (rep.ty (cacheTy index.ty scalar))
      (rep.ty (transcriptTy index.ty index.messageTy)) saved.2
    exact h₂.trans (h₁.trans hs)
  have hw : width ≤ hashWidth width cap := by dsimp [hashWidth, replyWidth]; nlinarith
  have result := backendReply_bound rep data cost primitive laws dataLaws primitiveBound sizes lists mono
    control queryCost routing false (Read.goodRead rep data cost primitive sampling index)
    (LazyAGM.goodResponse false) request saved width ((4 * (cap + 1) + 3) * (3 * width))
    (Read.goodTime overhead width cap (topicTime + 2 * indexTime + natTime) scalarTime zeroTime)
    (scaleTime + 192 * overhead (64 * hashWidth width cap)) hh hu hm hs hg (by
      intro z hz'
      have h := Read.goodRead_bound rep data cost primitive sizes laws dataLaws primitiveBound mono
        sampling index lists control queryCost routing request saved.2.1 width cap topicTime indexTime natTime
        scalarTime zeroTime hh hu hb hn hm hc hk hlen hf he hi heq hdraw hz z hz'
      have hsize := CacheCompiler.output_size rep sizes lists width (cap + 1)
        hh z.value h.1
      exact ⟨hsize.trans (by nlinarith), h.2⟩) (by
      intro env henv
      exact goodReplyResult_cost rep data cost primitive laws dataLaws primitiveBound sizes lists mono
        false env (hashWidth width cap) scaleTime (hh.trans hw) henv
        (fun g => (hg g).trans hw) hscale) out (by
      simpa only [goodHash] using hout)
  refine ⟨result.1, result.2.trans ?_⟩
  dsimp only [goodHashTime, hashWidth]
  omega

theorem badHash_bound
    (request : index.ty.Value (cryptoBase F G₁ G₂ K M))
    (saved : (storeTy index.ty index.messageTy (.pair scalar scalar) LazyAGM.badConfigTy).Value (cryptoBase F G₁ G₂ K M))
    (width cap topicTime indexTime natTime scalarTime zeroTime scaleTime addTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hn : ∀ j ≤ index.bound, Q.size rep.data.nat j ≤ width)
    (hm : Q.size (rep.ty index.ty) request ≤ width)
    (hs : Q.size (rep.ty (storeTy index.ty index.messageTy (.pair scalar scalar) LazyAGM.badConfigTy)) saved ≤ width)
    (hk : ∀ p ∈ saved.2.1, Q.size (rep.ty index.ty) p.1 ≤ width)
    (hlen : saved.2.1.length ≤ cap)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width)
    (he : ∀ a b : K, Q.size (rep.ty key) a ≤ 3 * width → Q.size (rep.ty key) b ≤ 3 * width →
      (primitiveBound .keyEq).time (a, b) ≤ topicTime)
    (hi : ∀ j : Fin (index.bound + 1), (primitiveBound (.finVal index.bound)).time j ≤ indexTime)
    (heq : ∀ j k : Nat, j ≤ index.bound → k ≤ index.bound → (primitiveBound .natEq).time (j, k) ≤ natTime)
    (hdraw : ∀ z ∈ support (sampling.scalar.run control queryCost ()), z.steps ≤ scalarTime)
    (hz : (primitiveBound .zero).time () ≤ zeroTime)
    (hscale : ∀ r : F, ∀ g : G₁, (primitiveBound .scale₁).time (r, g) ≤ scaleTime)
    (hadd : ∀ g h : G₁, (primitiveBound .add₁).time (g, h) ≤ addTime)
    (out : Run (G₁ × (storeTy index.ty index.messageTy (.pair scalar scalar) LazyAGM.badConfigTy).Value (cryptoBase F G₁ G₂ K M)))
    (hout : out ∈ support ((badHash rep data cost primitive sampling index).run control queryCost (request, saved))) :
    Q.size (rep.ty (.pair point₁ (storeTy index.ty index.messageTy (.pair scalar scalar) LazyAGM.badConfigTy))) out.value ≤
        16 * hashWidth width cap ∧
      out.steps ≤ badHashTime overhead width cap topicTime indexTime natTime scalarTime zeroTime scaleTime addTime := by
  have hc : Q.size (rep.ty (cacheTy index.ty (.pair scalar scalar))) saved.2.1 ≤ width := by
    have h₁ := sizes.snd_le (rep.ty LazyAGM.badConfigTy)
      (rep.ty (.pair (cacheTy index.ty (.pair scalar scalar)) (transcriptTy index.ty index.messageTy))) saved
    have h₂ := sizes.fst_le (rep.ty (cacheTy index.ty (.pair scalar scalar)))
      (rep.ty (transcriptTy index.ty index.messageTy)) saved.2
    exact h₂.trans (h₁.trans hs)
  have hw : width ≤ hashWidth width cap := by dsimp [hashWidth, replyWidth]; nlinarith
  have result := backendReply_bound rep data cost primitive laws dataLaws primitiveBound sizes lists mono
    control queryCost routing false (Read.badRead rep data cost primitive sampling index)
    (LazyAGM.badResponse false) request saved width ((4 * (cap + 1) + 3) * (3 * width))
    (Read.badTime overhead width cap (topicTime + 2 * indexTime + natTime) scalarTime zeroTime)
    (3 * scaleTime + addTime + 256 * overhead (64 * hashWidth width cap)) hh hu hm hs hg (by
      intro z hz'
      have h := Read.badRead_bound rep data cost primitive sizes laws dataLaws primitiveBound mono
        sampling index lists control queryCost routing request saved.2.1 width cap topicTime indexTime natTime
        scalarTime zeroTime hh hu hb hn hm hc hk hlen hf he hi heq hdraw hz z hz'
      have hsize := CacheCompiler.output_size rep sizes lists (3 * width) (cap + 1)
        (hh.trans (by omega)) z.value h.1
      exact ⟨hsize.trans (by rfl), h.2⟩) (by
      intro env henv
      exact badReplyResult_cost rep data cost primitive laws dataLaws primitiveBound sizes lists mono
        false env (hashWidth width cap) scaleTime addTime (hh.trans hw) henv
        (fun g => (hg g).trans hw) hscale hadd) out (by
      simpa only [badHash] using hout)
  refine ⟨result.1, result.2.trans ?_⟩
  dsimp only [badHashTime, hashWidth]
  omega

end Signatures.Runtime.WeightedAGM.Reply
