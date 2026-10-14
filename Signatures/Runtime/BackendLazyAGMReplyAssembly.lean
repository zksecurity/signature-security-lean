import Signatures.Runtime.BackendLazyAGMReplySize

/-! Assembly of native lazy AGM reply costs from the actual argument, cache,
response, and control code. The specialized reply budgets discharge the local
expression obligations using individual primitive certificates. -/

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

theorem backendReply_bound {value config : Ty CryptoAtom}
    (sampler : Code Q unifSpec iface rep.data.unit (rep.ty value))
    (fallback : Expr CryptoOp [message, storeTy value config] value)
    (response : Expr CryptoOp [value, config] point₁) (signing : Bool)
    (m : M) (saved : (storeTy value config).Value (cryptoBase F G₁ G₂ M M))
    (width cap comparisonTime sampleTime argumentTime resultTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hm : Q.size (rep.ty message) m ≤ width)
    (hs : Q.size (rep.ty (storeTy value config)) saved ≤ width)
    (hc : CacheCompiler.Entries (Q := Q) rep (key := message) (val := value) width saved.2.1)
    (hn : saved.2.1.length ≤ cap)
    (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width)
    (hdefault : Q.size (rep.ty value)
      (fallback.denote (arithmetic F G₁ G₂ M M cost) (m, saved, ())) ≤ width)
    (he : ∀ x y : M, Q.size (rep.ty message) x ≤ 5 * width → Q.size (rep.ty message) y ≤ 5 * width →
      (primitiveBound CryptoOp.messageEq).time (x, y) ≤ comparisonTime)
    (hd : Bounds control queryCost sampler (fun _ => True)
      (fun r => Q.size (rep.ty value) r ≤ width) sampleTime)
    (ha : Q.cost (Expression.arguments rep data (arithmetic F G₁ G₂ M M cost) primitive
      (cacheArgs fallback)) (m, saved, ()) ≤ argumentTime)
    (hr : ∀ env, Q.size (rep.env [cacheResultTy value, message, storeTy value config]) env ≤ replyWidth width cap →
      Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ M M cost) primitive
        (replyResult signing response)) env ≤ resultTime)
    (out : Run (G₁ × (storeTy value config).Value (cryptoBase F G₁ G₂ M M)))
    (hout : out ∈ support ((backendReply rep data cost primitive sampler fallback response signing).run
      control queryCost (m, saved))) :
    Q.size (rep.ty (.pair point₁ (storeTy value config))) out.value ≤ 16 * replyWidth width cap ∧
      out.steps ≤ cap * (comparisonTime + 257 * overhead (64 * replyWidth width cap)) +
        sampleTime + argumentTime + resultTime + 160 * overhead (64 * replyWidth width cap) := by
  let W := replyWidth width cap
  let fee := overhead (64 * W)
  have hw : width ≤ W := by dsimp [W, replyWidth, CacheCompiler.frameWidth]; nlinarith
  have h5 : width ≤ 5 * width := by omega
  let env : Env (cryptoBase F G₁ G₂ M M) [message, storeTy value config] := (m, saved, ())
  let args := (cacheArgs fallback).denote (arithmetic F G₁ G₂ M M cost) env
  have henv : Q.size (rep.env [message, storeTy value config]) env ≤ 5 * width :=
    replyFrame_size rep sizes (m, saved) width hh hu hm hs
  have hargs : Q.size (rep.env [message, value, cacheTy value]) args ≤ 35 * width := by
    have h := cacheArgs_size rep sizes cost fallback env (5 * width) (hh.trans h5) (hu.trans h5)
      henv (hdefault.trans h5)
    exact h.trans (by omega)
  have hinput : Q.size (rep.ty (.pair message (storeTy value config))) (m, saved) ≤ 3 * width := by
    have h := sizes.prod_le (rep.ty message) (rep.ty (storeTy value config)) (m, saved)
    change Q.size (rep.ty (.pair message (storeTy value config))) (m, saved) ≤ _ at h
    dsimp only at h
    omega
  have hpacked : Q.size (StepClass.HasProd.prod (rep.env [message, value, cacheTy value])
      (rep.env [message, storeTy value config])) (args, env) ≤ W := by
    have h := sizes.prod_le (rep.env [message, value, cacheTy value])
      (rep.env [message, storeTy value config]) (args, env)
    dsimp only at h
    dsimp only [W, replyWidth, CacheCompiler.frameWidth]
    nlinarith
  have henvW : Q.size (rep.env [message, storeTy value config]) env ≤ W := by
    dsimp only [W, replyWidth, CacheCompiler.frameWidth]
    nlinarith
  have hinputW : Q.size (rep.ty (.pair message (storeTy value config))) (m, saved) ≤ W := by
    dsimp only [W, replyWidth, CacheCompiler.frameWidth]
    nlinarith
  have hcacheInput : CacheCompiler.Input (Q := Q) rep (key := message) (val := value) (5 * width) cap args := by
    change Q.size (rep.ty message) m ≤ _ ∧ Q.size (rep.ty value) _ ≤ _ ∧ _
    exact ⟨hm.trans h5, hdefault.trans h5,
      (fun p hp => ⟨(hc p hp).1.trans h5, (hc p hp).2.trans h5⟩), hn⟩
  have hdraw : Bounds control queryCost sampler (fun _ => True)
      (fun r => Q.size (rep.ty value) r ≤ 5 * width) sampleTime := by
    intro u hi z hz
    obtain ⟨hv, ht⟩ := hd u hi z hz
    exact ⟨hv.trans h5, ht⟩
  rw [backendReply, replyBody] at hout
  simp only [Code.run, sequenceRun, mem_support_bind_iff, support_pure, Set.mem_singleton_iff,
    exists_eq_left] at hout
  obtain ⟨_, ⟨_, ⟨cached, hcached, rfl⟩, rfl⟩, rfl⟩ := hout
  have hcResult := SampledCache.bound rep data (arithmetic F G₁ G₂ M M cost) primitive
    (rep.env [message, storeTy value config]) sampler sizes lists laws dataLaws primitiveBound mono
    control queryCost routing CryptoOp.messageEq (fun _ _ => rfl)
    (5 * width) cap comparisonTime sampleTime (hh.trans h5) (hu.trans h5) (fun b => (hb b).trans h5)
    he hdraw args hcacheInput env henv cached hcached
  have hcachedSize : Q.size (rep.env [cacheResultTy value, message, storeTy value config]) cached.value ≤ W := by
    have hresult := CacheCompiler.output_size rep sizes lists (5 * width) (cap + 1) (hh.trans h5)
      cached.value.1 hcResult.1
    have hp := sizes.prod_le (rep.ty (cacheResultTy value)) (rep.env [message, storeTy value config]) cached.value
    rw [hcResult.2.1] at hp
    change Q.size (rep.env [cacheResultTy value, message, storeTy value config]) cached.value ≤ _ at hp
    dsimp only [W, replyWidth, CacheCompiler.frameWidth]
    nlinarith
  have hfinal := replyResult_size rep sizes lists cost signing response cached.value W (hh.trans hw)
    hcachedSize (fun g => (hg g).trans hw)
  have hfinalCost := hr cached.value hcachedSize
  have hfee : ∀ n ≤ 64 * W, overhead n ≤ fee := fun _ hn => mono hn
  have hcacheFee : overhead (32 * CacheCompiler.frameWidth (5 * width) cap) ≤ fee :=
    mono (by dsimp [W, replyWidth]; omega)
  have hcacheTime : cached.steps ≤ cap * (comparisonTime + 257 * fee) + sampleTime + 133 * fee := by
    apply hcResult.2.2.trans
    gcongr
  have hframeCost : Q.cost (replyFrame (value := value) (config := config) rep data) (m, saved) ≤ 5 * fee := by
    have hprod := @sizes.prod_le
    have hfst := @sizes.fst_le
    have hsnd := @sizes.snd_le
    have hlocal := (LocalBound.pair laws (LocalBound.fst laws (rep.ty message) (rep.ty (storeTy value config)))
      (LocalBound.pair laws (LocalBound.snd laws (rep.ty message) (rep.ty (storeTy value config)))
        (dataLaws.unitBound (rep.ty (.pair message (storeTy value config)))))).cost_le (m, saved)
    change Q.cost (replyFrame rep data) (m, saved) ≤ _ at hlocal
    apply hlocal.trans
    dsimp only [LocalBound.pair, LocalBound.fst, LocalBound.snd, DataCostLaws.unitBound,
      LanguageRepresentation.env, LanguageRepresentation.ty, env] at *
    grind only
  have hprepareCost : Q.cost (QP.pair
      (Expression.arguments rep data (arithmetic F G₁ G₂ M M cost) primitive (cacheArgs fallback))
      (Q.identity (rep.env [message, storeTy value config]))) env ≤ argumentTime + 2 * fee := by
    have hp := laws.pair
      (Expression.arguments rep data (arithmetic F G₁ G₂ M M cost) primitive (cacheArgs fallback))
      (Q.identity (rep.env [message, storeTy value config])) env
    have hid := (laws.identity (rep.env [message, storeTy value config]) env).trans (hfee _ (by omega))
    have hf := hfee _ (show Q.size (rep.env [message, storeTy value config]) env +
      Q.size (StepClass.HasProd.prod (rep.env [message, value, cacheTy value])
        (rep.env [message, storeTy value config])) (args, env) ≤ 64 * W by omega)
    dsimp only [id_eq] at hp
    have hat : Q.cost (Expression.arguments rep data (arithmetic F G₁ G₂ M M cost) primitive
        (cacheArgs fallback)) env ≤ argumentTime := ha
    apply hp.trans
    change Q.cost (Expression.arguments rep data (arithmetic F G₁ G₂ M M cost) primitive
      (cacheArgs fallback)) env + Q.cost (Q.identity (rep.env [message, storeTy value config])) env +
        overhead (Q.size (rep.env [message, storeTy value config]) env +
          Q.size (StepClass.HasProd.prod (rep.env [message, value, cacheTy value])
            (rep.env [message, storeTy value config])) (args, env)) ≤ argumentTime + 2 * fee
    omega
  have hcall := routing.localCall
  have hseq := routing.sequence
  refine ⟨hfinal, ?_⟩
  dsimp only [Run.steps, Run.value, env, args, fee, W, id_eq,
    LanguageRepresentation.ty, LanguageRepresentation.env] at *
  grind only

end Signatures.Runtime.LazyAGM
