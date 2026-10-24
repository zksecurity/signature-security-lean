import Proofs.Runtime.BackendWeightedComparison
import Proofs.Runtime.BackendStructuredCache
import Proofs.Runtime.BackendPairSampling
import Proofs.Runtime.BackendMachine
import Proofs.BLS.LazyAGMList

/-! Native weighted private caches. The compile-time index selects the actual
OOPS or Proximity key encoding. Both the scalar and independent-scalar-pair
branches use compiled structured comparisons and a finite encountered-entry
list. Their bounds charge the comparison implementation, sampling, scan,
retained environments, insertion, and stored code. No finite topic/slot domain
or completed-cache efficiency assumption is required. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.WeightedAGM.PrivateCache

open BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ K M S : Type} [Field F] [SampleableType F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (sampling : MachineCompiler.SamplingImplementation Q iface rep)
  (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (store : C.Str S) (index : Index)

/-- Generic cache access with this scheme's implemented comparator. The sampler
is code; the good/bad definitions below select the actual scalar/pair samplers. -/
def access {val : Ty CryptoAtom} (sampler : Code Q unifSpec iface rep.data.unit (rep.ty val)) :
    Code Q unifSpec iface (StepClass.HasProd.prod (rep.env [index.ty, val, .list (.pair index.ty val)]) store)
      (StepClass.HasProd.prod (rep.ty (.pair val (.list (.pair index.ty val)))) store) :=
  StructuredCache.code rep data (index.code rep data cost primitive) store sampler

def pairSampler : Code Q unifSpec iface rep.data.unit (rep.ty (.pair scalar scalar)) :=
  PairSampling.code rep.data data (rep.ty scalar) (rep.ty scalar) sampling.scalar sampling.scalar

def goodCache := access rep data cost primitive store index sampling.scalar

def badCache := access rep data cost primitive store index (pairSampler rep data sampling)

omit QS [Field F] [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq K] [DecidableEq M] in
theorem pairSampler_denote (input : Unit) :
    (pairSampler rep data sampling).denote input = ($ᵗ (F × F) : ProbComp (F × F)) :=
  PairSampling.uniform rep.data data (rep.ty scalar) (rep.ty scalar) sampling.scalar sampling.scalar
    sampling.scalar_denote sampling.scalar_denote input

/-- This is the weighted private list oracle at the encoded index type; the
returned list and ambient state are preserved jointly. Proximity's source-index
encoding is connected explicitly in `proximity_goodCache_denote` below. -/
theorem goodCache_denote (k : index.ty.Value (cryptoBase F G₁ G₂ K M))
    (default : F) (cache : List (index.ty.Value (cryptoBase F G₁ G₂ K M) × F)) (saved : S) :
    (goodCache rep data sampling cost primitive store index).denote ((k, default, cache, ()), saved) =
      (fun p => (p, saved)) <$>
        ((BLS.LazyAGM.Reduction.privateListOracle
          (M := index.ty.Value (cryptoBase F G₁ G₂ K M)) (R := F)) (.inr k)).run cache := by
  exact StructuredCache.uniform rep data (index.code rep data cost primitive) store
    sampling.scalar (sampling.scalar_denote ()) k default cache saved

theorem badCache_denote (k : index.ty.Value (cryptoBase F G₁ G₂ K M))
    (default : F × F) (cache : List (index.ty.Value (cryptoBase F G₁ G₂ K M) × (F × F))) (saved : S) :
    (badCache rep data sampling cost primitive store index).denote ((k, default, cache, ()), saved) =
      (fun p => (p, saved)) <$>
        ((BLS.LazyAGM.Reduction.privateListOracle
          (M := index.ty.Value (cryptoBase F G₁ G₂ K M)) (R := F × F)) (.inr k)).run cache := by
  exact StructuredCache.uniform rep data (index.code rep data cost primitive) store
    (pairSampler rep data sampling) (pairSampler_denote rep data sampling ()) k default cache saved

/-- The source constant coordinate is `none`; native code uses tag zero.
Coordinate tags and slot labels are preserved by an injective encoding. -/
theorem proximity_goodCache_denote (ell : Nat) (k : Option (Fin ell) × K) (default : F)
    (cache : List ((Option (Fin ell) × K) × F)) (saved : S) :
    (goodCache rep data sampling cost primitive store (.proximity ell)).denote
        ((Weights.encodeProximityKey k, default, cache.map (Prod.map Weights.encodeProximityKey id), ()), saved) =
      (fun p => ((p.1, p.2.map (Prod.map Weights.encodeProximityKey id)), saved)) <$>
        ((BLS.LazyAGM.Reduction.privateListOracle (M := Option (Fin ell) × K) (R := F)) (.inr k)).run cache :=
  StructuredCache.uniform_encoded rep data ((Index.proximity ell).code rep data cost primitive) store
    sampling.scalar (sampling.scalar_denote ()) Weights.encodeProximityKey
    (Weights.encodeProximityKey_injective ell) k default cache saved

theorem proximity_badCache_denote (ell : Nat) (k : Option (Fin ell) × K) (default : F × F)
    (cache : List ((Option (Fin ell) × K) × (F × F))) (saved : S) :
    (badCache rep data sampling cost primitive store (.proximity ell)).denote
        ((Weights.encodeProximityKey k, default, cache.map (Prod.map Weights.encodeProximityKey id), ()), saved) =
      (fun p => ((p.1, p.2.map (Prod.map Weights.encodeProximityKey id)), saved)) <$>
        ((BLS.LazyAGM.Reduction.privateListOracle (M := Option (Fin ell) × K) (R := F × F)) (.inr k)).run cache :=
  StructuredCache.uniform_encoded rep data ((Index.proximity ell).code rep data cost primitive) store
    (pairSampler rep data sampling) (pairSampler_denote rep data sampling ()) Weights.encodeProximityKey
    (Weights.encodeProximityKey_injective ell) k default cache saved

theorem goodCache_hit_run (other : MachineCompiler.SamplingImplementation Q iface rep)
    (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
    (k : index.ty.Value (cryptoBase F G₁ G₂ K M)) (default : F)
    (cache : List (index.ty.Value (cryptoBase F G₁ G₂ K M) × F)) (saved : S)
    (value : F) (hit : cache.lookup k = some value) :
    (goodCache rep data sampling cost primitive store index).run control queryCost ((k, default, cache, ()), saved) =
      (goodCache rep data other cost primitive store index).run control queryCost ((k, default, cache, ()), saved) :=
  StructuredCache.hit_run rep data (index.code rep data cost primitive) store sampling.scalar other.scalar
    control queryCost k default cache saved value hit

theorem badCache_hit_run (other : MachineCompiler.SamplingImplementation Q iface rep)
    (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
    (k : index.ty.Value (cryptoBase F G₁ G₂ K M)) (default : F × F)
    (cache : List (index.ty.Value (cryptoBase F G₁ G₂ K M) × (F × F))) (saved : S)
    (value : F × F) (hit : cache.lookup k = some value) :
    (badCache rep data sampling cost primitive store index).run control queryCost ((k, default, cache, ()), saved) =
      (badCache rep data other cost primitive store index).run control queryCost ((k, default, cache, ()), saved) :=
  StructuredCache.hit_run rep data (index.code rep data cost primitive) store
    (pairSampler rep data sampling) (pairSampler rep data other) control queryCost k default cache saved value hit

def time (overhead : Nat → Nat) (width cap comparisonTime sampleTime : Nat) : Nat :=
  cap * (comparisonTime + 391 * overhead (32 * CacheCompiler.frameWidth width cap)) +
    sampleTime + 133 * overhead (32 * CacheCompiler.frameWidth width cap)

section Bounds

variable [C.HasOption]
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  (mono : Monotone overhead) (control : ControlCosts)
  (queryCost : (i : Nat) → unifSpec.Range i → Nat) (routing : RoutingCostLaws control overhead)

include sizes lists laws dataLaws mono routing

omit [SampleableType F] in
/-- All comparator obligations are discharged using its actual primitive
instructions. Only the separate sampler's component budget is supplied here. -/
theorem access_bound {val : Ty CryptoAtom} (sampler : Code Q unifSpec iface rep.data.unit (rep.ty val))
    (width cap topicTime indexTime natTime sampleTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hn : ∀ j ≤ index.bound, Q.size rep.data.nat j ≤ width)
    (ht : ∀ a b : K, Q.size (rep.ty key) a ≤ width → Q.size (rep.ty key) b ≤ width →
      (primitiveBound .keyEq).time (a, b) ≤ topicTime)
    (hi : ∀ j : Fin (index.bound + 1), (primitiveBound (.finVal index.bound)).time j ≤ indexTime)
    (he : ∀ j k : Nat, j ≤ index.bound → k ≤ index.bound → (primitiveBound .natEq).time (j, k) ≤ natTime)
    (hd : Bounds control queryCost sampler (fun _ => True) (fun v => Q.size (rep.ty val) v ≤ width) sampleTime)
    (env : Env (cryptoBase F G₁ G₂ K M) [index.ty, val, .list (.pair index.ty val)])
    (henv : CacheCompiler.Input (Q := Q) rep width cap env) (saved : S) (hs : Q.size store saved ≤ width)
    (z : Run ((val.Value (cryptoBase F G₁ G₂ K M) ×
      List (index.ty.Value (cryptoBase F G₁ G₂ K M) × val.Value (cryptoBase F G₁ G₂ K M))) × S))
    (hz : z ∈ support ((access rep data cost primitive store index sampler).run control queryCost (env, saved))) :
    CacheCompiler.Output (Q := Q) rep width (cap + 1) z.value.1 ∧ z.value.2 = saved ∧
      z.steps ≤ time overhead width cap (topicTime + 2 * indexTime + natTime) sampleTime := by
  have hc := StructuredCache.bound rep data (index.code rep data cost primitive) store sampler
    sizes lists laws dataLaws mono control queryCost routing width cap
    (topicTime + 2 * indexTime + natTime + 134 * overhead (128 * width)) sampleTime hh hu hb
    (fun x y hx hy => index.native_cost rep data cost primitive sizes laws dataLaws primitiveBound mono
      x y width topicTime indexTime natTime hh hu hb hn hx hy ht hi he)
    hd env henv saved hs z hz
  have hm : overhead (128 * width) ≤ overhead (32 * CacheCompiler.frameWidth width cap) := by
    apply mono
    dsimp [CacheCompiler.frameWidth]
    nlinarith
  refine ⟨hc.1, hc.2.1, hc.2.2.trans ?_⟩
  dsimp [time]
  nlinarith [Nat.mul_le_mul_left (134 * cap) hm]

theorem goodCache_bound (k : index.ty.Value (cryptoBase F G₁ G₂ K M))
    (cache : List (index.ty.Value (cryptoBase F G₁ G₂ K M) × F)) (saved : S)
    (width cap topicTime indexTime natTime scalarTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hn : ∀ j ≤ index.bound, Q.size rep.data.nat j ≤ width)
    (hk : Q.size (rep.ty index.ty) k ≤ width)
    (hc : ∀ p ∈ cache, Q.size (rep.ty index.ty) p.1 ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hlen : cache.length ≤ cap) (hs : Q.size store saved ≤ width)
    (ht : ∀ a b : K, Q.size (rep.ty key) a ≤ width → Q.size (rep.ty key) b ≤ width →
      (primitiveBound .keyEq).time (a, b) ≤ topicTime)
    (hi : ∀ j : Fin (index.bound + 1), (primitiveBound (.finVal index.bound)).time j ≤ indexTime)
    (he : ∀ j k : Nat, j ≤ index.bound → k ≤ index.bound → (primitiveBound .natEq).time (j, k) ≤ natTime)
    (hd : ∀ z ∈ support (sampling.scalar.run control queryCost ()), z.steps ≤ scalarTime)
    (z : Run ((F × List (index.ty.Value (cryptoBase F G₁ G₂ K M) × F)) × S))
    (hz : z ∈ support ((goodCache rep data sampling cost primitive store index).run control queryCost
      ((k, 0, cache, ()), saved))) :
    CacheCompiler.Output (Q := Q) rep (key := index.ty) (val := scalar) width (cap + 1) z.value.1 ∧
      z.value.2 = saved ∧
      z.steps ≤ time overhead width cap (topicTime + 2 * indexTime + natTime) scalarTime :=
  access_bound rep data cost primitive store index sizes lists laws dataLaws primitiveBound mono
    control queryCost routing sampling.scalar width cap topicTime indexTime natTime scalarTime hh hu hb hn ht hi he
    (by intro u _ out hout; cases u; exact ⟨hf out.value, hd out hout⟩)
    (k, 0, cache, ()) ⟨hk, hf 0, (fun p hp => ⟨hc p hp, hf p.2⟩), hlen⟩ saved hs z hz

theorem badCache_bound (k : index.ty.Value (cryptoBase F G₁ G₂ K M))
    (cache : List (index.ty.Value (cryptoBase F G₁ G₂ K M) × (F × F))) (saved : S)
    (width cap topicTime indexTime natTime scalarTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hn : ∀ j ≤ index.bound, Q.size rep.data.nat j ≤ width)
    (hk : Q.size (rep.ty index.ty) k ≤ width)
    (hc : ∀ p ∈ cache, Q.size (rep.ty index.ty) p.1 ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hlen : cache.length ≤ cap) (hs : Q.size store saved ≤ width)
    (ht : ∀ a b : K, Q.size (rep.ty key) a ≤ 3 * width → Q.size (rep.ty key) b ≤ 3 * width →
      (primitiveBound .keyEq).time (a, b) ≤ topicTime)
    (hi : ∀ j : Fin (index.bound + 1), (primitiveBound (.finVal index.bound)).time j ≤ indexTime)
    (he : ∀ j k : Nat, j ≤ index.bound → k ≤ index.bound → (primitiveBound .natEq).time (j, k) ≤ natTime)
    (hd : ∀ z ∈ support (sampling.scalar.run control queryCost ()), z.steps ≤ scalarTime)
    (z : Run (((F × F) × List (index.ty.Value (cryptoBase F G₁ G₂ K M) × (F × F))) × S))
    (hz : z ∈ support ((badCache rep data sampling cost primitive store index).run control queryCost
      ((k, (0, 0), cache, ()), saved))) :
    CacheCompiler.Output (Q := Q) rep (key := index.ty) (val := .pair scalar scalar)
      (3 * width) (cap + 1) z.value.1 ∧ z.value.2 = saved ∧
      z.steps ≤ time overhead (3 * width) cap (topicTime + 2 * indexTime + natTime) (2 * scalarTime) +
        12 * overhead (32 * CacheCompiler.frameWidth (3 * width) cap) := by
  let fee := overhead (32 * CacheCompiler.frameWidth (3 * width) cap)
  have hw : width ≤ 3 * width := by omega
  have hp (p : F × F) : Q.size (rep.ty (.pair scalar scalar)) p ≤ 3 * width := by
    have h := sizes.prod_le (rep.ty scalar) (rep.ty scalar) p
    have h1 := hf p.1
    have h2 := hf p.2
    change Q.size (rep.ty (.pair scalar scalar)) p ≤ _ at h
    omega
  have component : Bounds control queryCost sampling.scalar (fun _ => True)
      (fun f => Q.size (rep.ty scalar) f ≤ width) scalarTime := by
    intro u _ out hout
    cases u
    exact ⟨hf out.value, hd out hout⟩
  have hpair := PairSampling.bound rep.data data (rep.ty scalar) (rep.ty scalar)
    sampling.scalar sampling.scalar sizes laws dataLaws mono control queryCost routing
    width scalarTime scalarTime hh hu component component
  have hfee : overhead (8 * width) ≤ fee := by
    apply mono
    dsimp [CacheCompiler.frameWidth]
    nlinarith
  have hdPair : Bounds control queryCost (pairSampler rep data sampling) (fun _ => True)
      (fun p => Q.size (rep.ty (.pair scalar scalar)) p ≤ 3 * width) (2 * scalarTime + 12 * fee) := by
    intro u _ out hout
    have h := hpair u True.intro out hout
    exact ⟨hp out.value, by omega⟩
  have result := access_bound rep data cost primitive store index sizes lists laws dataLaws primitiveBound
    mono control queryCost routing (pairSampler rep data sampling)
    (3 * width) cap topicTime indexTime natTime (2 * scalarTime + 12 * fee)
    (hh.trans hw) (hu.trans hw) (fun b => (hb b).trans hw) (fun j hj => (hn j hj).trans hw)
    ht hi he hdPair (k, (0, 0), cache, ())
    ⟨hk.trans hw, hp (0, 0), (fun p hmem => ⟨(hc p hmem).trans hw, hp p.2⟩), hlen⟩
    saved (hs.trans hw) z hz
  exact ⟨result.1, result.2.1, by dsimp only [time, fee] at *; omega⟩

end Bounds

variable (sizes : DescriptionSize Q) (allowance : Nat)
  (laws : LocalDescriptionLaws sizes allowance)
  (dataLaws : DataDescriptionLaws sizes rep.data data allowance)
  (primitiveSize : {a b : Ty CryptoAtom} → CryptoOp a b → Nat)
  (hp : ∀ {a b} (instr : CryptoOp a b), sizes.localSize (primitive instr) ≤ primitiveSize instr)

include laws dataLaws hp

theorem goodCache_description :
    (goodCache rep data sampling cost primitive store index).descriptionSize sizes ≤
      sampling.scalar.descriptionSize sizes + primitiveSize .keyEq +
        2 * primitiveSize (.finVal index.bound) + primitiveSize .natEq + 320 * allowance + 30 := by
  have hc := StructuredCache.description rep data (index.code rep data cost primitive) store sampling.scalar
    sizes allowance laws dataLaws
  have hi := index.description rep data cost primitive sizes allowance laws dataLaws primitiveSize hp
  exact hc.trans (by omega)

theorem badCache_description :
    (badCache rep data sampling cost primitive store index).descriptionSize sizes ≤
      2 * sampling.scalar.descriptionSize sizes + primitiveSize .keyEq +
        2 * primitiveSize (.finVal index.bound) + primitiveSize .natEq + 326 * allowance + 36 := by
  have hc := StructuredCache.description rep data (index.code rep data cost primitive) store
    (pairSampler rep data sampling) sizes allowance laws dataLaws
  have hi := index.description rep data cost primitive sizes allowance laws dataLaws primitiveSize hp
  have hs := PairSampling.description rep.data data (rep.ty scalar) (rep.ty scalar)
    sampling.scalar sampling.scalar sizes allowance laws dataLaws
  change (pairSampler rep data sampling).descriptionSize sizes ≤ _ at hs
  exact hc.trans (by omega)

end Signatures.Runtime.WeightedAGM.PrivateCache
