import Proofs.Runtime.BackendPairSampling
import Proofs.Runtime.BackendSampledCache
import Proofs.Runtime.BackendMachine
import Proofs.BLS.LazyAGMList

/-! Native scalar and independent-pair caches for the two lazy BLS AGM solvers.
Each program scans its explicit finite list. Correctness preserves the returned
answer and updated list jointly. Native budgets include sampling, scan, control,
and copies; static description bounds include every stored sampler occurrence.
The surrounding reply, extraction, and general-caller composition are separate
obligations, not conclusions of this module.
-/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.LazyAGM

open BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ M S : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M))
  (data : DataCode Q rep.data) (samplingCode : MachineCompiler.SamplingImplementation Q iface rep)
  (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ M M cost).execute instr))
  (store : C.Str S)

def pairSampler : Code Q unifSpec iface rep.data.unit (rep.ty (.pair scalar scalar)) :=
  PairSampling.code rep.data data (rep.ty scalar) (rep.ty scalar) samplingCode.scalar samplingCode.scalar

@[irreducible] def goodCache :
    Code Q unifSpec iface (StepClass.HasProd.prod (rep.env [message, scalar, .list (.pair message scalar)]) store)
      (StepClass.HasProd.prod (rep.ty (.pair scalar (.list (.pair message scalar)))) store) :=
  SampledCache.code rep data (arithmetic F G₁ G₂ M M cost) primitive store samplingCode.scalar .messageEq

@[irreducible] def badCache :
    Code Q unifSpec iface
      (StepClass.HasProd.prod (rep.env [message, .pair scalar scalar, .list (.pair message (.pair scalar scalar))]) store)
      (StepClass.HasProd.prod (rep.ty (.pair (.pair scalar scalar) (.list (.pair message (.pair scalar scalar))))) store) :=
  SampledCache.code rep data (arithmetic F G₁ G₂ M M cost) primitive store (pairSampler rep data samplingCode) .messageEq

omit QS [Field F] [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M] in
theorem pairSampler_denote (input : Unit) :
    (pairSampler rep data samplingCode).denote input = ($ᵗ (F × F) : ProbComp (F × F)) :=
  PairSampling.uniform rep.data data (rep.ty scalar) (rep.ty scalar) samplingCode.scalar samplingCode.scalar
    samplingCode.scalar_denote samplingCode.scalar_denote input

theorem goodCache_denote (m : M) (default : F) (cache : List (M × F)) (saved : S) :
    (goodCache rep data samplingCode cost primitive store).denote ((m, default, cache, ()), saved) =
      (fun p => (p, saved)) <$>
        ((BLS.LazyAGM.Reduction.privateListOracle (M := M) (R := F)) (.inr m)).run cache := by
  rw [goodCache, SampledCache.uniform rep data (arithmetic F G₁ G₂ M M cost) primitive store
    CryptoOp.messageEq samplingCode.scalar (samplingCode.scalar_denote ()) (fun _ _ => rfl)]
  rfl

theorem badCache_denote (m : M) (default : F × F) (cache : List (M × (F × F))) (saved : S) :
    (badCache rep data samplingCode cost primitive store).denote ((m, default, cache, ()), saved) =
      (fun p => (p, saved)) <$>
        ((BLS.LazyAGM.Reduction.privateListOracle (M := M) (R := F × F)) (.inr m)).run cache := by
  rw [badCache, SampledCache.uniform rep data (arithmetic F G₁ G₂ M M cost) primitive store
    CryptoOp.messageEq (pairSampler rep data samplingCode) (pairSampler_denote rep data samplingCode ())
    (fun _ _ => rfl)]
  rfl

theorem goodCache_hit_run (other : MachineCompiler.SamplingImplementation Q iface rep)
    (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
    (m : M) (default : F) (cache : List (M × F)) (saved : S) (value : F)
    (hit : cache.lookup m = some value) :
    (goodCache rep data samplingCode cost primitive store).run control queryCost ((m, default, cache, ()), saved) =
      (goodCache rep data other cost primitive store).run control queryCost ((m, default, cache, ()), saved) := by
  rw [goodCache, goodCache]
  exact SampledCache.hit_run rep data (arithmetic F G₁ G₂ M M cost) primitive store samplingCode.scalar
    CryptoOp.messageEq (fun _ _ => rfl) other.scalar control queryCost m default cache saved value hit

theorem badCache_hit_run (other : MachineCompiler.SamplingImplementation Q iface rep)
    (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
    (m : M) (default : F × F) (cache : List (M × (F × F))) (saved : S) (value : F × F)
    (hit : cache.lookup m = some value) :
    (badCache rep data samplingCode cost primitive store).run control queryCost ((m, default, cache, ()), saved) =
      (badCache rep data other cost primitive store).run control queryCost ((m, default, cache, ()), saved) := by
  rw [badCache, badCache]
  exact SampledCache.hit_run rep data (arithmetic F G₁ G₂ M M cost) primitive store (pairSampler rep data samplingCode)
    CryptoOp.messageEq (fun _ _ => rfl) (pairSampler rep data other) control queryCost m default cache saved value hit

section Bounds

variable [C.HasOption]
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  (mono : Monotone overhead) (control : ControlCosts)
  (queryCost : (i : Nat) → unifSpec.Range i → Nat) (routing : RoutingCostLaws control overhead)

include sizes lists laws dataLaws mono routing

theorem goodCache_bound (m : M) (cache : List (M × F)) (saved : S)
    (width cap comparisonTime scalarTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hm : Q.size (rep.ty message) m ≤ width)
    (hc : ∀ p ∈ cache, Q.size (rep.ty message) p.1 ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hn : cache.length ≤ cap) (hs : Q.size store saved ≤ width)
    (he : ∀ x y : M, Q.size (rep.ty message) x ≤ width → Q.size (rep.ty message) y ≤ width →
      (primitiveBound CryptoOp.messageEq).time (x, y) ≤ comparisonTime)
    (hd : ∀ z ∈ support (samplingCode.scalar.run control queryCost ()), z.steps ≤ scalarTime)
    (z : Run ((F × List (M × F)) × S))
    (hz : z ∈ support ((goodCache rep data samplingCode cost primitive store).run control queryCost
      ((m, 0, cache, ()), saved))) :
    CacheCompiler.Output (Q := Q) rep (key := message) (val := scalar) width (cap + 1) z.value.1 ∧
      z.value.2 = saved ∧
      z.steps ≤ cap * (comparisonTime + 257 * overhead (32 * CacheCompiler.frameWidth width cap)) +
        scalarTime + 133 * overhead (32 * CacheCompiler.frameWidth width cap) := by
  rw [goodCache] at hz
  exact SampledCache.bound rep data (arithmetic F G₁ G₂ M M cost) primitive store samplingCode.scalar
    sizes lists laws dataLaws primitiveBound mono control queryCost routing CryptoOp.messageEq
    (fun _ _ => rfl) width cap comparisonTime scalarTime hh hu hb he
    (by intro u _ out hout; cases u; exact ⟨hf out.value, hd out hout⟩)
    (m, 0, cache, ()) ⟨hm, hf 0, (fun p hp => ⟨hc p hp, hf p.2⟩), hn⟩ saved hs z hz

theorem badCache_bound (m : M) (cache : List (M × (F × F))) (saved : S)
    (width cap comparisonTime scalarTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hm : Q.size (rep.ty message) m ≤ width)
    (hc : ∀ p ∈ cache, Q.size (rep.ty message) p.1 ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hn : cache.length ≤ cap) (hs : Q.size store saved ≤ width)
    (he : ∀ x y : M, Q.size (rep.ty message) x ≤ 3 * width → Q.size (rep.ty message) y ≤ 3 * width →
      (primitiveBound CryptoOp.messageEq).time (x, y) ≤ comparisonTime)
    (hd : ∀ z ∈ support (samplingCode.scalar.run control queryCost ()), z.steps ≤ scalarTime)
    (z : Run (((F × F) × List (M × (F × F))) × S))
    (hz : z ∈ support ((badCache rep data samplingCode cost primitive store).run control queryCost
      ((m, (0, 0), cache, ()), saved))) :
    CacheCompiler.Output (Q := Q) rep (key := message) (val := .pair scalar scalar) (3 * width) (cap + 1) z.value.1 ∧
      z.value.2 = saved ∧
      z.steps ≤ cap * (comparisonTime + 257 * overhead (32 * CacheCompiler.frameWidth (3 * width) cap)) +
        2 * scalarTime + 145 * overhead (32 * CacheCompiler.frameWidth (3 * width) cap) := by
  let fee := overhead (32 * CacheCompiler.frameWidth (3 * width) cap)
  have hscale : width ≤ 3 * width := by omega
  have hp (p : F × F) : Q.size (rep.ty (.pair scalar scalar)) p ≤ 3 * width := by
    have h := sizes.prod_le (rep.ty scalar) (rep.ty scalar) p
    have h1 := hf p.1
    have h2 := hf p.2
    change Q.size (rep.ty (.pair scalar scalar)) p ≤ _ at h
    omega
  have component : Bounds control queryCost samplingCode.scalar (fun _ => True)
      (fun f => Q.size (rep.ty scalar) f ≤ width) scalarTime := by
    intro u _ out hout
    cases u
    exact ⟨hf out.value, hd out hout⟩
  have hpair := PairSampling.bound rep.data data (rep.ty scalar) (rep.ty scalar)
    samplingCode.scalar samplingCode.scalar sizes laws dataLaws mono control queryCost routing
    width scalarTime scalarTime hh hu component component
  have hfee : overhead (8 * width) ≤ fee := by
    apply mono
    dsimp [CacheCompiler.frameWidth]
    nlinarith
  have samplerBound : Bounds control queryCost (pairSampler rep data samplingCode) (fun _ => True)
      (fun p => Q.size (rep.ty (.pair scalar scalar)) p ≤ 3 * width) (2 * scalarTime + 12 * fee) := by
    intro u _ out hout
    have h := hpair u True.intro out hout
    exact ⟨hp out.value, by omega⟩
  rw [badCache] at hz
  have result := SampledCache.bound rep data (arithmetic F G₁ G₂ M M cost) primitive store
    (pairSampler rep data samplingCode) sizes lists laws dataLaws primitiveBound mono control queryCost routing
    CryptoOp.messageEq (fun _ _ => rfl) (3 * width) cap comparisonTime (2 * scalarTime + 12 * fee)
    (hh.trans hscale) (hu.trans hscale) (fun b => (hb b).trans hscale) he samplerBound
    (m, (0, 0), cache, ()) ⟨hm.trans hscale, hp (0, 0),
      (fun p hmem => ⟨(hc p hmem).trans hscale, hp p.2⟩), hn⟩ saved (hs.trans hscale) z hz
  exact ⟨result.1, result.2.1, by dsimp only [fee] at result; omega⟩

end Bounds

theorem goodCache_description (sizes : DescriptionSize Q) (allowance : Nat)
    (laws : LocalDescriptionLaws sizes allowance)
    (dataLaws : DataDescriptionLaws sizes rep.data data allowance) :
    (goodCache rep data samplingCode cost primitive store).descriptionSize sizes ≤
      samplingCode.scalar.descriptionSize sizes + sizes.localSize (primitive .messageEq) + 250 * allowance + 30 := by
  rw [goodCache]
  exact SampledCache.description rep data (arithmetic F G₁ G₂ M M cost) primitive store samplingCode.scalar
    CryptoOp.messageEq sizes allowance laws dataLaws

theorem badCache_description (sizes : DescriptionSize Q) (allowance : Nat)
    (laws : LocalDescriptionLaws sizes allowance)
    (dataLaws : DataDescriptionLaws sizes rep.data data allowance) :
    (badCache rep data samplingCode cost primitive store).descriptionSize sizes ≤
      2 * samplingCode.scalar.descriptionSize sizes + sizes.localSize (primitive .messageEq) + 256 * allowance + 36 := by
  rw [badCache]
  have hc := SampledCache.description rep data (arithmetic F G₁ G₂ M M cost) primitive store
    (pairSampler rep data samplingCode) CryptoOp.messageEq sizes allowance laws dataLaws
  have hs := PairSampling.description rep.data data (rep.ty scalar) (rep.ty scalar)
    samplingCode.scalar samplingCode.scalar sizes allowance laws dataLaws
  change (pairSampler rep data samplingCode).descriptionSize sizes ≤ _ at hs
  omega

end Signatures.Runtime.LazyAGM
