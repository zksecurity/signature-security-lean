import Signatures.Runtime.BackendLazyAGMReadCost

/-! Complete assembly cost of a native private-cache read, including its
argument frame, sampled cache, result projection, and all control transitions. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.LazyAGM

open BackendProgram ReplySyntax

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

theorem backendRead_bound {value : Ty CryptoAtom}
    (sampler : Code Q unifSpec iface rep.data.unit (rep.ty value))
    (fallback : Expr CryptoOp [message, cacheTy value] value)
    (m : M) (cache : List (M × value.Value (cryptoBase F G₁ G₂ M M)))
    (width cap comparisonTime sampleTime argumentTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hm : Q.size (rep.ty message) m ≤ width)
    (hs : Q.size (rep.ty (cacheTy value)) cache ≤ width)
    (hc : CacheCompiler.Entries (Q := Q) rep (key := message) (val := value) width cache)
    (hn : cache.length ≤ cap)
    (hf : Q.size (rep.ty value)
      (fallback.denote (arithmetic F G₁ G₂ M M cost) (m, cache, ())) ≤ width)
    (he : ∀ x y : M, Q.size (rep.ty message) x ≤ width → Q.size (rep.ty message) y ≤ width →
      (primitiveBound CryptoOp.messageEq).time (x, y) ≤ comparisonTime)
    (hd : Bounds control queryCost sampler (fun _ => True)
      (fun r => Q.size (rep.ty value) r ≤ width) sampleTime)
    (ha : Q.cost (Expression.arguments rep data (arithmetic F G₁ G₂ M M cost) primitive
      (readArgs fallback)) (m, cache, ()) ≤ argumentTime)
    (out : Run (value.Value (cryptoBase F G₁ G₂ M M) × List (M × value.Value (cryptoBase F G₁ G₂ M M))))
    (hout : out ∈ support ((backendRead rep data cost primitive sampler fallback).run
      control queryCost (m, cache))) :
    CacheCompiler.Output (Q := Q) rep (key := message) (val := value) width (cap + 1) out.value ∧
      out.steps ≤ cap * (comparisonTime + 257 * overhead (32 * CacheCompiler.frameWidth width cap)) +
        sampleTime + argumentTime + 160 * overhead (32 * CacheCompiler.frameWidth width cap) := by
  let W := CacheCompiler.frameWidth width cap
  let fee := overhead (32 * W)
  let env : Env (cryptoBase F G₁ G₂ M M) [message, cacheTy value] := (m, cache, ())
  let args := (readArgs fallback).denote (arithmetic F G₁ G₂ M M cost) env
  have hw : 9 * width ≤ W := by dsimp [W, CacheCompiler.frameWidth]; nlinarith
  have henv : Q.size (rep.env [message, cacheTy value]) env ≤ 5 * width := by
    have hp := @sizes.prod_le
    dsimp only [env, LanguageRepresentation.env] at *
    grind only
  have hargs : Q.size (rep.env [message, value, cacheTy value]) args ≤ 7 * width := by
    have hp := @sizes.prod_le
    dsimp only [args, readArgs, env, v0, v1, Args.denote, Expr.denote, Var.get,
      LanguageRepresentation.env] at *
    grind only
  have hinput : Q.size (rep.ty (.pair message (cacheTy value))) (m, cache) ≤ 3 * width := by
    have hp := sizes.prod_le (rep.ty message) (rep.ty (cacheTy value)) (m, cache)
    dsimp only at hp
    exact hp.trans (by omega)
  have hpacked : Q.size (StepClass.HasProd.prod (rep.env [message, value, cacheTy value])
      rep.data.unit) (args, ()) ≤ W := by
    have hp := sizes.prod_le (rep.env [message, value, cacheTy value]) rep.data.unit (args, ())
    dsimp only at hp
    omega
  have hi : CacheCompiler.Input (Q := Q) rep (key := message) (val := value) width cap args := by
    exact ⟨hm, hf, hc, hn⟩
  rw [backendRead] at hout
  simp only [Code.run, sequenceRun, mem_support_bind_iff, support_pure, Set.mem_singleton_iff,
    exists_eq_left] at hout
  obtain ⟨_, ⟨_, ⟨cached, hcached, rfl⟩, rfl⟩, rfl⟩ := hout
  have hcache := SampledCache.bound rep data (arithmetic F G₁ G₂ M M cost) primitive
    rep.data.unit sampler sizes lists laws dataLaws primitiveBound mono control queryCost routing
    CryptoOp.messageEq (fun _ _ => rfl) width cap comparisonTime sampleTime hh hu hb he hd args hi () hu cached hcached
  have hcacheOutput := CacheCompiler.output_size rep sizes lists width (cap + 1) hh cached.value.1 hcache.1
  have hcachedSize : Q.size (StepClass.HasProd.prod (rep.ty (cacheResultTy value)) rep.data.unit)
      cached.value ≤ W := by
    have hp := sizes.prod_le (rep.ty (cacheResultTy value)) rep.data.unit cached.value
    rw [hcache.2.1] at hp
    dsimp only [W, CacheCompiler.frameWidth]
    nlinarith
  have hfee : ∀ n ≤ 32 * W, overhead n ≤ fee := fun _ hn => mono hn
  have hframeCost : Q.cost (readFrame (value := value) rep data) (m, cache) ≤ 5 * fee := by
    have hprod := @sizes.prod_le
    have hfst := @sizes.fst_le
    have hsnd := @sizes.snd_le
    have hl := (LocalBound.pair laws (LocalBound.fst laws (rep.ty message) (rep.ty (cacheTy value)))
      (LocalBound.pair laws (LocalBound.snd laws (rep.ty message) (rep.ty (cacheTy value)))
        (dataLaws.unitBound (rep.ty (.pair message (cacheTy value)))))).cost_le (m, cache)
    change Q.cost (readFrame rep data) (m, cache) ≤ _ at hl
    apply hl.trans
    dsimp only [LocalBound.pair, LocalBound.fst, LocalBound.snd, DataCostLaws.unitBound,
      LanguageRepresentation.env, LanguageRepresentation.ty, env] at *
    grind only
  have hprepareCost : Q.cost (QP.pair
      (Expression.arguments rep data (arithmetic F G₁ G₂ M M cost) primitive (readArgs fallback))
      (data.unit _)) env ≤ argumentTime + 2 * fee := by
    have hp := laws.pair
      (Expression.arguments rep data (arithmetic F G₁ G₂ M M cost) primitive (readArgs fallback))
      (data.unit _) env
    have huCost := (dataLaws.unit (rep.env [message, cacheTy value]) env).trans
      (hfee _ (by omega))
    have hfCost := hfee _ (show Q.size (rep.env [message, cacheTy value]) env +
      Q.size (StepClass.HasProd.prod (rep.env [message, value, cacheTy value]) rep.data.unit)
        (args, ()) ≤ 32 * W by omega)
    have hat : Q.cost (Expression.arguments rep data (arithmetic F G₁ G₂ M M cost) primitive
      (readArgs fallback)) env ≤ argumentTime := ha
    apply hp.trans
    change Q.cost (Expression.arguments rep data (arithmetic F G₁ G₂ M M cost) primitive
      (readArgs fallback)) env + Q.cost (data.unit _) env +
      overhead (Q.size (rep.env [message, cacheTy value]) env +
        Q.size (StepClass.HasProd.prod (rep.env [message, value, cacheTy value]) rep.data.unit)
          (args, ())) ≤ argumentTime + 2 * fee
    omega
  have hprojection := sizes.fst_le (rep.ty (cacheResultTy value)) rep.data.unit cached.value
  have hfinishCost := (laws.fst (rep.ty (cacheResultTy value)) rep.data.unit cached.value).trans
    (hfee _ (by omega))
  have hcall := routing.localCall
  have hseq := routing.sequence
  refine ⟨hcache.1, ?_⟩
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  dsimp only [Run.steps, Run.value, env, args, fee, W, id_eq,
    LanguageRepresentation.ty, LanguageRepresentation.env] at *
  grind only

end Signatures.Runtime.LazyAGM
