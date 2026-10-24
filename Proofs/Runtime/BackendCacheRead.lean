import Proofs.Runtime.BackendStructuredCache

/-! Implemented cache reads with the cache as effect state. The input is a key
and its current finite cache; the output is the answer and updated cache. The
argument packer, executed fallback construction, and final state projection are
ordinary backend code. Their costs and stored descriptions are charged here. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.BackendProgram.CacheRead

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {Atom I : Type} {base : Atom → Type}
  {spec : OracleSpec I} {iface : Interface (C := C) spec}
  (rep : LanguageRepresentation C base) (data : DataCode Q rep.data)
  {key val : Ty Atom} [DecidableEq (key.Value base)]
  (comparison : Q.Realizer (rep.ty (.pair key key)) rep.data.bool (fun p => decide (p.1 = p.2)))
  {default : key.Value base × List (key.Value base × val.Value base) → val.Value base}
  (fallback : Q.Realizer (rep.ty (.pair key (.list (.pair key val)))) (rep.ty val) default)
  (sampler : Code Q spec iface rep.data.unit (rep.ty val))

def arguments :
    Q.Realizer (rep.ty (.pair key (.list (.pair key val))))
      (StepClass.HasProd.prod (rep.env [key, val, .list (.pair key val)]) rep.data.unit)
      (fun p => ((p.1, default p, p.2, ()), ())) :=
  QP.pair (QP.pair (QP.fst _ _) (QP.pair fallback (QP.pair (QP.snd _ _) (data.unit _)))) (data.unit _)

@[irreducible] def code :
    Code Q spec iface (rep.ty (.pair key (.list (.pair key val))))
      (rep.ty (.pair val (.list (.pair key val)))) :=
  .seq (.atomic (arguments rep data fallback))
    (.seq (StructuredCache.code rep data comparison rep.data.unit sampler) (.atomic (QP.fst _ _)))

theorem denote (k : key.Value base) (cache : List (key.Value base × val.Value base)) :
    (code rep data comparison fallback sampler).denote (k, cache) =
      match cache.lookup k with
      | some v => pure (v, cache)
      | none => (fun v => (v, (k, v) :: cache)) <$> sampler.denote () := by
  rw [code]
  simp only [Code.denote, pure_bind]
  rw [StructuredCache.denote]
  cases cache.lookup k <;> simp [bind_pure_comp]

theorem uniform [SampleableType (val.Value base)] {iface : Interface (C := C) unifSpec}
    (sampler : Code Q unifSpec iface rep.data.unit (rep.ty val))
    (hs : sampler.denote () = ($ᵗ (val.Value base) : ProbComp (val.Value base)))
    (k : key.Value base) (cache : List (key.Value base × val.Value base)) :
    (code rep data comparison fallback sampler).denote (k, cache) =
      (QueryImpl.ListCache.handler (uniformSampleImpl (spec := key.Value base →ₒ val.Value base)) k).run cache := by
  rw [denote]
  cases h : cache.lookup k <;>
    simp [QueryImpl.ListCache.handler, StateT.run, h, hs, uniformSampleImpl]

theorem hit_run (other : Code Q spec iface rep.data.unit (rep.ty val))
    (control : ControlCosts) (queryCost : (i : I) → spec.Range i → Nat)
    (k : key.Value base) (cache : List (key.Value base × val.Value base))
    (value : val.Value base) (hit : cache.lookup k = some value) :
    (code rep data comparison fallback sampler).run control queryCost (k, cache) =
      (code rep data comparison fallback other).run control queryCost (k, cache) := by
  have h := StructuredCache.hit_run rep data comparison rep.data.unit sampler other control queryCost
    k (default (k, cache)) cache () value hit
  simp only [code, Code.run, sequenceRun, pure_bind, arguments]
  rw [h]

theorem description (sizes : DescriptionSize Q) (allowance : Nat)
    (laws : LocalDescriptionLaws sizes allowance)
    (dataLaws : DataDescriptionLaws sizes rep.data data allowance) :
    (code rep data comparison fallback sampler).descriptionSize sizes ≤
      sampler.descriptionSize sizes + sizes.localSize comparison + sizes.localSize fallback +
        260 * allowance + 34 := by
  have ha := laws.pair_bound (laws.pair_bound (laws.fst (rep.ty key) (rep.ty (.list (.pair key val))))
    (laws.pair_bound (le_refl (sizes.localSize fallback))
      (laws.pair_bound (laws.snd (rep.ty key) (rep.ty (.list (.pair key val)))) (dataLaws.unit _))))
      (dataLaws.unit _)
  have hc := StructuredCache.description rep data comparison rep.data.unit sampler sizes allowance laws dataLaws
  have ho := laws.fst (rep.ty (.pair val (.list (.pair key val)))) rep.data.unit
  rw [code]
  dsimp only [Code.descriptionSize, arguments, LanguageRepresentation.ty, LanguageRepresentation.env] at *
  omega

variable [C.HasOption]
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (mono : Monotone overhead) (control : ControlCosts)
  (queryCost : (i : I) → spec.Range i → Nat) (routing : RoutingCostLaws control overhead)

include sizes lists laws dataLaws mono routing

theorem bound (k : key.Value base) (cache : List (key.Value base × val.Value base))
    (width cap comparisonTime fallbackTime sampleTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hk : Q.size (rep.ty key) k ≤ width)
    (hc : Q.size (rep.ty (.list (.pair key val))) cache ≤ width)
    (he : CacheCompiler.Entries (Q := Q) rep width cache) (hn : cache.length ≤ cap)
    (hf : Q.size (rep.ty val) (default (k, cache)) ≤ width)
    (hcomparison : ∀ x y, Q.size (rep.ty key) x ≤ width → Q.size (rep.ty key) y ≤ width →
      Q.cost comparison (x, y) ≤ comparisonTime)
    (hdefault : Q.cost fallback (k, cache) ≤ fallbackTime)
    (hsampler : Bounds control queryCost sampler (fun _ => True)
      (fun v => Q.size (rep.ty val) v ≤ width) sampleTime)
    (out : Run (val.Value base × List (key.Value base × val.Value base)))
    (hout : out ∈ support ((code rep data comparison fallback sampler).run control queryCost (k, cache))) :
    CacheCompiler.Output (Q := Q) rep width (cap + 1) out.value ∧
      out.steps ≤ cap * (comparisonTime + 257 * overhead (32 * CacheCompiler.frameWidth width cap)) +
        fallbackTime + sampleTime + 160 * overhead (32 * CacheCompiler.frameWidth width cap) := by
  let W := CacheCompiler.frameWidth width cap
  let fee := overhead (32 * W)
  let args : Env base [key, val, .list (.pair key val)] := (k, default (k, cache), cache, ())
  have hw : 9 * width ≤ W := by dsimp [W, CacheCompiler.frameWidth]; nlinarith
  have hinput : Q.size (rep.ty (.pair key (.list (.pair key val)))) (k, cache) ≤ 3 * width := by
    have h := sizes.prod_le (rep.ty key) (rep.ty (.list (.pair key val))) (k, cache)
    dsimp only at h
    exact h.trans (by omega)
  have hargs : Q.size (StepClass.HasProd.prod (rep.env [key, val, .list (.pair key val)]) rep.data.unit)
      (args, ()) ≤ 9 * width := by
    have hp := @sizes.prod_le
    dsimp only [args, LanguageRepresentation.env] at *
    grind only
  have hi : CacheCompiler.Input (Q := Q) rep width cap args := ⟨hk, hf, he, hn⟩
  rw [code] at hout
  simp only [Code.run, sequenceRun, mem_support_bind_iff, support_pure, Set.mem_singleton_iff,
    exists_eq_left] at hout
  obtain ⟨_, ⟨cached, hcached, rfl⟩, rfl⟩ := hout
  have hcache := StructuredCache.bound rep data comparison rep.data.unit sampler sizes lists laws dataLaws
    mono control queryCost routing width cap comparisonTime sampleTime hh hu hb hcomparison hsampler
    args hi () hu cached hcached
  have hcacheOutput := CacheCompiler.output_size rep sizes lists width (cap + 1) hh cached.value.1 hcache.1
  have hcachedSize : Q.size (StepClass.HasProd.prod (rep.ty (.pair val (.list (.pair key val)))) rep.data.unit)
      cached.value ≤ W := by
    have hp := sizes.prod_le (rep.ty (.pair val (.list (.pair key val)))) rep.data.unit cached.value
    rw [hcache.2.1] at hp
    dsimp only [W, CacheCompiler.frameWidth]
    nlinarith
  have hfee : ∀ n ≤ 32 * W, overhead n ≤ fee := fun _ h => mono h
  have hpack : Q.cost (arguments rep data fallback) (k, cache) ≤ fallbackTime + 8 * fee := by
    let bound := LocalBound.pair laws
      (LocalBound.pair laws (LocalBound.fst laws (rep.ty key) (rep.ty (.list (.pair key val))))
        (LocalBound.pair laws (LocalBound.measured fallback)
          (LocalBound.pair laws (LocalBound.snd laws (rep.ty key) (rep.ty (.list (.pair key val))))
            (dataLaws.unitBound _)))) (dataLaws.unitBound _)
    have h := bound.cost_le (k, cache)
    have hp := @sizes.prod_le
    apply h.trans
    dsimp only [bound, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.measured,
      DataCostLaws.unitBound, LanguageRepresentation.ty, LanguageRepresentation.env, args] at *
    grind only
  have hprojection := sizes.fst_le (rep.ty (.pair val (.list (.pair key val)))) rep.data.unit cached.value
  have hfinish := (laws.fst (rep.ty (.pair val (.list (.pair key val)))) rep.data.unit cached.value).trans
    (hfee _ (by omega))
  have hcall := routing.localCall
  have hseq := routing.sequence
  refine ⟨hcache.1, ?_⟩
  dsimp only [Run.steps, Run.value, args, fee, W, id_eq, LanguageRepresentation.ty,
    LanguageRepresentation.env] at *
  grind only

end Signatures.Runtime.BackendProgram.CacheRead
